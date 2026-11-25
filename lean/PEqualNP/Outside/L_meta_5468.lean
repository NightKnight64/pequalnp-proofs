import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5468
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def step (x : List Bool) (g : Gate) : List Bool :=
  x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]

private theorem step_other (x : List Bool) (g : Gate) (i : ℕ) (ne : i ≠ x.length) :
    (step x g).getD i false = x.getD i false := by
  unfold step
  by_cases lt : i < x.length
  · exact List.getD_append _ _ _ _ lt
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have right : x.getD i false = false := List.getD_eq_default _ _ (by omega)
    rw [right]
    have pos : 0 < i - x.length := by omega
    cases h : i - x.length with
    | zero => omega
    | succ k => simp

private theorem step_new (x : List Bool) (g : Gate) :
    (step x g).getD x.length false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  unfold step
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

private theorem gate_mono (g : Gate) (op : g.op = .and ∨ g.op = .or)
    (x y : List Bool) (le : ∀i∈g.inputs, x.getD i false ≤ y.getD i false) :
    g.op.eval (g.inputs.map fun i => x.getD i false) ≤
      g.op.eval (g.inputs.map fun i => y.getD i false) := by
  rw [Bool.le_iff_imp]
  rcases op with h|h
  · simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,id_eq]
    intro hit _ val
    obtain ⟨i,im,rfl⟩ := val
    exact Bool.le_iff_imp.mp (le i im) (hit _ ⟨i,im,rfl⟩)
  · simp only [h,GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
    rintro ⟨_,⟨i,im,rfl⟩,yes⟩
    exact ⟨_,⟨i,im,rfl⟩,Bool.le_iff_imp.mp (le i im) yes⟩

private theorem frontier (gs : List Gate) (m : ℕ) (S : Finset ℕ)
    (mono : Monotone2 (⟨gs,0⟩ : Circuit)) :
    ∃ T : Finset ℕ, T.card ≤ S.card + gs.length ∧
      ∀ x y : List Bool, x.length = m → y.length = m →
        (∀ i ∈ T, x.getD i false ≤ y.getD i false) →
          ∀ i ∈ S, (gs.foldl step x).getD i false ≤ (gs.foldl step y).getD i false := by
  induction gs generalizing m S with
  | nil => exact ⟨S,by simp,fun _ _ _ _ h=>h⟩
  | cons g gs ih =>
    obtain ⟨Q,cap,tail⟩ := ih (m+1) S (fun a am=>mono a (List.mem_cons_of_mem _ am))
    have gate := mono g List.mem_cons_self
    have op : g.op=.and ∨ g.op=.or := by simpa using gate.1
    have extend (x : List Bool) (xl : x.length=m) : (step x g).length=m+1 := by simp [step,xl]
    by_cases member : m∈Q
    · let T := Q.erase m ∪ g.inputs.toFinset
      have cost := Finset.card_union_le (Q.erase m) g.inputs.toFinset
      have erase := Finset.card_erase_add_one member
      have args := g.inputs.toFinset_card_le.trans gate.2
      refine ⟨T,by change T.card≤S.card+gs.length+1;change T.card≤_ at cost;omega,?_⟩
      intro x y xl yl le
      apply tail (step x g) (step y g) (extend x xl) (extend y yl)
      intro i im
      by_cases same : i=m
      · subst i
        rw [←xl,step_new,show x.length=y.length by omega,step_new]
        exact gate_mono g op x y (fun j jm=>le j (Finset.mem_union_right _ (List.mem_toFinset.mpr jm)))
      · rw [step_other x g i (by omega),step_other y g i (by omega)]
        exact le i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨same,im⟩))
    · refine ⟨Q,by simp;omega,?_⟩
      intro x y xl yl le
      apply tail (step x g) (step y g) (extend x xl) (extend y yl)
      intro i im
      have ne : i≠m := fun h=>member (h ▸ im)
      rw [step_other x g i (by omega),step_other y g i (by omega)]
      exact le i im

theorem support (C : Circuit) (m : ℕ) (mono : Monotone2 C) :
    ∃ T : Finset ℕ, T.card ≤ C.size + 1 ∧ ∀ X Y : List Bool, X.length = m → Y.length = m →
      (∀ i∈T, X.getD i false ≤ Y.getD i false) → C.eval X ≤ C.eval Y := by
  obtain ⟨T,cap,support_⟩ := frontier C.gates m {C.output} mono
  refine ⟨T,by simp at cap ⊢;unfold Circuit.size;omega,?_⟩
  intro X Y xl yl h
  exact support_ X Y xl yl h C.output (Finset.mem_singleton_self _)

def target (u v : Fin 4) : Bool := (1919 : ℕ).testBit (4 * u.val + v.val)

def Supports (C : Circuit) (S : Finset ℕ) : Prop :=
  ∀ X Y : List Bool, X.length = 8 → Y.length = 8 →
    (∀ i ∈ S, X.getD i false ≤ Y.getD i false) → C.eval X ≤ C.eval Y

theorem mandatory (C : Circuit) (rep : Represents target C) {S : Finset ℕ}
    (supports : Supports C S) (w : ℕ) (a b c d : Fin 4)
    (positive : target a b = true) (negative : target c d = false)
    (ordered : ∀ i : Fin 8, i.val ≠ w →
      (oneEach a b).getD i.val false ≤ (oneEach c d).getD i.val false) :
    w ∈ S := by
  by_contra missing
  have len (u v : Fin 4) : (oneEach u v).length = 8 := by simp [oneEach]
  have lower := supports (oneEach a b) (oneEach c d) (len a b) (len c d) (by
    intro i im
    by_cases valid : i < 8
    · exact ordered ⟨i, valid⟩ (fun e => missing (e ▸ im))
    · rw [List.getD_eq_default _ _ (by rw [len]; omega),
          List.getD_eq_default _ _ (by rw [len]; omega)])
  rw [rep a b, rep c d, positive, negative] at lower
  exact Bool.noConfusion (Bool.le_iff_imp.mp lower rfl)

theorem core {C : Circuit} (rep : Represents target C) {S : Finset ℕ}
    (supports : Supports C S) : 6 ≤ S.card := by
  classical
  have r0 := mandatory C rep supports 0 0 0 3 0 (by decide) (by decide) (by decide)
  have r1 := mandatory C rep supports 1 1 0 3 0 (by decide) (by decide) (by decide)
  have r2 := mandatory C rep supports 2 2 0 3 0 (by decide) (by decide) (by decide)
  have c0 := mandatory C rep supports 4 1 0 1 3 (by decide) (by decide) (by decide)
  have c1 := mandatory C rep supports 5 1 1 1 3 (by decide) (by decide) (by decide)
  have c2 := mandatory C rep supports 6 1 2 1 3 (by decide) (by decide) (by decide)
  let required : Finset ℕ := {0,1,2,4,5,6}
  have sub : required ⊆ S := by
    intro i im
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5 ∨ i = 6 by simpa [required] using im) with
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  exact (show required.card = 6 by decide) ▸ Finset.card_le_card sub

private def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 6]⟩,
    ⟨.and, [8, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩

theorem upper :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 4 => (1919 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  unfold PEqualNP.Represents.RepSizeAtMost PEqualNP.Represents.Represents
    PEqualNP.Represents.oneEach
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g gm
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at gm
  rcases gm with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5468

theorem PEqualNP.Outside.L_meta_5468 :
PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1919 : ℕ).testBit (4 * u.val + v.val)) 5 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1919 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  refine ⟨PEqualNP.Outside.L_meta_5468.upper, ?_⟩
  rintro ⟨C, mono, size, represents⟩
  obtain ⟨S, count, ordered⟩ := PEqualNP.Outside.L_meta_5468.support C 8 mono
  have needed := PEqualNP.Outside.L_meta_5468.core (C := C) (S := S) represents ordered
  omega
