-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
-- name    : QMAPerfectCompleteness_Proof_CircuitUnitary
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:46:27.85135+00:00
-- url     : https://prove2.me/theorems/6ab3894a-7224-4a12-975c-1b0b071ab2d3
-- title:
--   Placed quantum gates and circuit unitarity
-- statement:
--   Splits a computational basis into the target wires of an injectively placed gate and its spectator wires. This identifies the placed instruction matrix with the gate tensored with an identity, and supplies the unitarity facts needed for finite ordered gate lists and their acceptance effects.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CircuitUnitary.lean, lines 7–99.

/- Generated from Solutions.CircuitUnitary by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates



open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CircuitProof

/-- Split basis bits into the target bits of an instruction and untouched bits. -/
noncomputable def splitTargets {r n : ℕ} (e : Fin r ↪ Fin n) :
    Basis n ≃ Basis r × ({w : Fin n // w ∉ Set.range e} → Bool) := by
  classical
  let f : Basis n → Basis r × ({w : Fin n // w ∉ Set.range e} → Bool) :=
    fun x => (x ∘ e, fun w => x w)
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    funext w
    by_cases hw : w ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hw
      exact congrFun (congrArg Prod.fst h) a
    · exact congrFun (congrArg Prod.snd h) ⟨w,hw⟩
  · rintro ⟨a,b⟩
    let x : Basis n := fun w => if hw : w ∈ Set.range e then a (Classical.choose hw)
      else b ⟨w,hw⟩
    refine ⟨x, ?_⟩
    apply Prod.ext
    · funext j
      have hj : e j ∈ Set.range e := ⟨j,rfl⟩
      have hc : Classical.choose hj = j := e.injective (Classical.choose_spec hj)
      change (if hw : e j ∈ Set.range e then a (Classical.choose hw) else b ⟨e j,hw⟩) = a j
      rw [dif_pos hj, hc]
    · funext j
      change (if hw : (j : Fin n) ∈ Set.range e then a (Classical.choose hw)
        else b ⟨j,hw⟩) = b j
      simp [j.2]

@[simp] theorem splitTargets_fst {r n : ℕ} (e : Fin r ↪ Fin n) (x : Basis n) :
    (splitTargets e x).1 = x ∘ e := rfl

@[simp] theorem splitTargets_snd {r n : ℕ} (e : Fin r ↪ Fin n) (x : Basis n)
    (w : {w : Fin n // w ∉ Set.range e}) : (splitTargets e x).2 w = x w := rfl

lemma unaffected_iff {r n : ℕ} (e : Fin r ↪ Fin n) (x y : Basis n) :
    (∀ w, (∀ a, e a ≠ w) → y w = x w) ↔
      (splitTargets e y).2 = (splitTargets e x).2 := by
  classical
  constructor
  · intro h
    funext w
    exact h w (by simpa [Set.mem_range] using w.2)
  · intro h w hw
    exact congrFun h ⟨w, by simpa [Set.mem_range] using hw⟩

lemma instr_eq_submatrix {G : GateSet} {n : ℕ} (i : Instr G n) :
    i.matrix = (((G.get i.gate).matrix ⊗ₖ
      (1 : Matrix ({w : Fin n // w ∉ Set.range i.targets} → Bool)
        ({w : Fin n // w ∉ Set.range i.targets} → Bool) ℂ)).submatrix
      (splitTargets i.targets) (splitTargets i.targets)) := by
  classical
  ext y x
  simp only [Instr.matrix, Matrix.of_apply, Matrix.submatrix_apply, Matrix.kronecker_apply,
    splitTargets_fst, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, splitTargets_fst]
  by_cases h : ∀ w, (∀ a, i.targets a ≠ w) → y w = x w
  · have hr := (unaffected_iff i.targets x y).mp h
    rw [if_pos h, if_pos hr, mul_one]
  · have hr : (splitTargets i.targets y).2 ≠ (splitTargets i.targets x).2 :=
      mt (unaffected_iff i.targets x y).mpr h
    rw [if_neg h, if_neg hr, mul_zero]

lemma submatrix_unitary {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (A : Matrix β β ℂ) (hA : A ∈ Matrix.unitaryGroup β ℂ) :
    A.submatrix e e ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix] at hA ⊢
  rw [Matrix.submatrix_mul_equiv A Aᴴ e e e, hA]
  simp

lemma kronecker_identity_unitary {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (A : Matrix α α ℂ) (hA : A ∈ Matrix.unitaryGroup α ℂ) :
    A ⊗ₖ (1 : Matrix β β ℂ) ∈ Matrix.unitaryGroup (α × β) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  simp only [Matrix.star_eq_conjTranspose] at hA
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, hA, Matrix.one_mul,
    Matrix.one_kronecker_one]

/-- A placed instruction is unitary, including all untouched wires. -/
theorem instr_unitary {G : GateSet} {n : ℕ} (i : Instr G n) :
    i.matrix ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  classical
  rw [instr_eq_submatrix]
  exact submatrix_unitary _ _ (kronecker_identity_unitary _ (G.get i.gate).unitary)

/-- Ordered products of placed gates are unitary. -/
theorem circuit_unitary {G : GateSet} {n : ℕ} (gs : List (Instr G n)) :
    circuitMatrix gs ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  induction gs with
  | nil => exact one_mem _
  | cons g gs ih => exact mul_mem ih (instr_unitary g)







open scoped ComplexOrder



end QMAPerfectCompleteness.Main.CircuitProof


