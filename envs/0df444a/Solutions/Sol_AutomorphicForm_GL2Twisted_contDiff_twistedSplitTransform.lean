-- Prove2me | solution 1 for AutomorphicForm.GL2Twisted.contDiff_twistedSplitTransform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8ea0b861-81d1-5a08-b7b7-3d2b9162399c

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Twisted_contDiff_twistedSplitTransform

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Twisted

open MeasureTheory

noncomputable section

namespace TwistedSplitSmooth

private abbrev Ent : Type := Fin 2 → Fin 2 → ℂ

private abbrev Box : Type := ℝ × ℝ × ℝ × ℝ

private abbrev Dom : Type := ℂ × Box

private def unitaryAt (b : Box) : GL (Fin 2) ℂ :=
  unitaryElt b.1 b.2.1 b.2.2.1 b.2.2.2

private def boxMeasure₃ : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod
    ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))

private def boxMeasure₂ : Measure (ℝ × ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Set.Ioc 0 (Real.pi / 2))).prod boxMeasure₃

private def boxMeasure : Measure Box := ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod boxMeasure₂

private scoped instance : IsFiniteMeasure boxMeasure₃ := by unfold boxMeasure₃; infer_instance
private scoped instance : IsFiniteMeasure boxMeasure₂ := by unfold boxMeasure₂; infer_instance
private scoped instance : IsFiniteMeasure boxMeasure := by unfold boxMeasure; infer_instance

private def kMat (ψ η ξ₁ ξ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
      Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
    Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
      Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))]

private def kInv (ψ η ξ₁ ξ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(ψ * Complex.I)) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I))),
      Complex.exp (-(ψ * Complex.I)) * (-(Real.sin η * Complex.exp (ξ₂ * Complex.I)));
    Complex.exp (-(ψ * Complex.I)) * (Real.sin η * Complex.exp (-(ξ₂ * Complex.I))),
      Complex.exp (-(ψ * Complex.I)) * (Real.cos η * Complex.exp (ξ₁ * Complex.I))]

private def kBar (ψ η ξ₁ ξ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (kMat ψ η ξ₁ ξ₂).map (starRingEnd ℂ)

private def kBarInv (ψ η ξ₁ ξ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (kInv ψ η ξ₁ ξ₂).map (starRingEnd ℂ)

private theorem exp_mul_exp_neg (t : ℝ) : Complex.exp (t * Complex.I) * Complex.exp (-(t * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private theorem cos_sq_add_sin_sq' (η : ℝ) : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq η

private theorem kInv_mul_kMat (ψ η ξ₁ ξ₂ : ℝ) : kInv ψ η ξ₁ ξ₂ * kMat ψ η ξ₁ ξ₂ = 1 := by
  have hψ := exp_mul_exp_neg ψ
  have h₁ := exp_mul_exp_neg ξ₁
  have h₂ := exp_mul_exp_neg ξ₂
  have h₃ := cos_sq_add_sin_sq' η
  rw [kInv, kMat, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination ((Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I))) +
        (Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)))) * hψ +
      (Real.cos η : ℂ) ^ 2 * h₁ + (Real.sin η : ℂ) ^ 2 * h₂ + h₃
  · ring
  · ring
  · linear_combination ((Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I))) +
        (Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)))) * hψ +
      (Real.sin η : ℂ) ^ 2 * h₂ + (Real.cos η : ℂ) ^ 2 * h₁ + h₃

private theorem kMat_mul_kInv (ψ η ξ₁ ξ₂ : ℝ) : kMat ψ η ξ₁ ξ₂ * kInv ψ η ξ₁ ξ₂ = 1 := by
  have hψ := exp_mul_exp_neg ψ
  have h₁ := exp_mul_exp_neg ξ₁
  have h₂ := exp_mul_exp_neg ξ₂
  have h₃ := cos_sq_add_sin_sq' η
  rw [kMat, kInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination ((Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I))) +
        (Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)))) * hψ +
      (Real.cos η : ℂ) ^ 2 * h₁ + (Real.sin η : ℂ) ^ 2 * h₂ + h₃
  · ring
  · ring
  · linear_combination ((Real.sin η : ℂ) ^ 2 * (Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I))) +
        (Real.cos η : ℂ) ^ 2 * (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)))) * hψ +
      (Real.sin η : ℂ) ^ 2 * h₂ + (Real.cos η : ℂ) ^ 2 * h₁ + h₃

private theorem kBar_mul_kBarInv (ψ η ξ₁ ξ₂ : ℝ) : kBar ψ η ξ₁ ξ₂ * kBarInv ψ η ξ₁ ξ₂ = 1 := by
  rw [kBar, kBarInv, ← Matrix.map_mul, kMat_mul_kInv, Matrix.map_one] <;> simp

private theorem norm_exp_real_mul_I (t : ℝ) : ‖Complex.exp (t * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]; simp

private theorem norm_exp_neg_real_mul_I (t : ℝ) : ‖Complex.exp (-(t * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

private theorem kMat_entry_norm_le (ψ η ξ₁ ξ₂ : ℝ) (i j : Fin 2) : ‖kMat ψ η ξ₁ ξ₂ i j‖ ≤ 1 := by
  have hc : ‖(Real.cos η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one η
  have hs : ‖(Real.sin η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one η
  fin_cases i <;> fin_cases j <;>
    simp only [kMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, norm_mul, norm_neg, norm_exp_real_mul_I, norm_exp_neg_real_mul_I, one_mul, mul_one] <;>
    assumption

private theorem kInv_entry_norm_le (ψ η ξ₁ ξ₂ : ℝ) (i j : Fin 2) : ‖kInv ψ η ξ₁ ξ₂ i j‖ ≤ 1 := by
  have hc : ‖(Real.cos η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one η
  have hs : ‖(Real.sin η : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one η
  fin_cases i <;> fin_cases j <;>
    simp only [kInv, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, norm_mul, norm_neg, norm_exp_real_mul_I, norm_exp_neg_real_mul_I, one_mul, mul_one] <;>
    assumption

private theorem kBarInv_entry_norm_le (ψ η ξ₁ ξ₂ : ℝ) (i j : Fin 2) : ‖kBarInv ψ η ξ₁ ξ₂ i j‖ ≤ 1 := by
  simpa [kBarInv, Matrix.map_apply, Complex.norm_conj] using kInv_entry_norm_le ψ η ξ₁ ξ₂ i j

private theorem unitaryElt_val (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kMat ψ η ξ₁ ξ₂ := rfl

private theorem unitaryElt_inv_val (ψ η ξ₁ ξ₂ : ℝ) :
    (((unitaryElt ψ η ξ₁ ξ₂)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kInv ψ η ξ₁ ξ₂ := by
  refine Units.inv_eq_of_mul_eq_one_left ?_
  rw [unitaryElt_val]
  exact kInv_mul_kMat ψ η ξ₁ ξ₂

private theorem conjEntries_val (g : GL (Fin 2) ℂ) :
    ((conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((g : Matrix (Fin 2) (Fin 2) ℂ)).map (starRingEnd ℂ) :=
  rfl

private theorem conjEntries_unitaryElt_val (ψ η ξ₁ ξ₂ : ℝ) :
    ((conjEntries (unitaryElt ψ η ξ₁ ξ₂) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kBar ψ η ξ₁ ξ₂ := rfl

private def conjugateAt (b : Box) (M : Matrix (Fin 2) (Fin 2) ℂ) : Ent :=
  Matrix.of.symm (kInv b.1 b.2.1 b.2.2.1 b.2.2.2 * M * kBar b.1 b.2.1 b.2.2.1 b.2.2.2)

private def entryTriple (ω : Dom) : Ent × Ent × Ent :=
  (conjugateAt ω.2 !![1, 0; 0, 0], conjugateAt ω.2 !![0, 0; 0, 1], conjugateAt ω.2 !![0, ω.1; 0, 0])

private def combine (Y : Ent × Ent × Ent) (a : ℝ × ℝ) : Ent :=
  (Real.sqrt a.1 : ℂ) • Y.1 + (Real.sqrt a.2 : ℂ) • Y.2.1 + Y.2.2

private def density (ω : Dom) : ℝ :=
  (1 / (4 * Real.pi ^ 3)) * (Real.sin ω.2.2.1 * Real.cos ω.2.2.1)

private def domMeasure : Measure Dom := (volume : Measure ℂ).prod boxMeasure

private scoped instance : SFinite domMeasure := by unfold domMeasure; infer_instance

private theorem isOpen_vanishingSet {P : Type} [TopologicalSpace P] [T2Space P] (c C : ℝ) (K : Set P)
    (hK : IsCompact K) :
    IsOpen {q : ℝ × ℝ × P | q.1 < c ∨ q.2.1 < c ∨ C < q.1 ∨ C < q.2.1 ∨ q.2.2 ∉ K} := by
  have h1 : IsOpen {q : ℝ × ℝ × P | q.1 < c} := isOpen_lt continuous_fst continuous_const
  have h2 : IsOpen {q : ℝ × ℝ × P | q.2.1 < c} :=
    isOpen_lt (continuous_fst.comp continuous_snd) continuous_const
  have h3 : IsOpen {q : ℝ × ℝ × P | C < q.1} := isOpen_lt continuous_const continuous_fst
  have h4 : IsOpen {q : ℝ × ℝ × P | C < q.2.1} :=
    isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
  have h5 : IsOpen {q : ℝ × ℝ × P | q.2.2 ∉ K} :=
    hK.isClosed.isOpen_compl.preimage (continuous_snd.comp continuous_snd)
  exact h1.union (h2.union (h3.union (h4.union h5)))

private theorem twistedSplitElt_val (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    ((twistedSplitElt a₁ a₂ v h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] :=
  rfl

private theorem splitMatrix_eq (a₁ a₂ : ℝ) (v : ℂ) :
    (!![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) =
      (Real.sqrt a₁ : ℂ) • !![1, 0; 0, 0] + (Real.sqrt a₂ : ℂ) • !![0, 0; 0, 1] + !![0, v; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem combine_entryTriple (a₁ a₂ : ℝ) (v : ℂ) (b : Box) :
    combine (entryTriple (v, b)) (a₁, a₂) = conjugateAt b !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] := by
  simp only [combine, entryTriple, conjugateAt, splitMatrix_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  rfl

private theorem entries_eq (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (v : ℂ) (b : Box) :
    Matrix.of.symm (((unitaryAt b)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (unitaryAt b) :
        GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      combine (entryTriple (v, b)) (a₁, a₂) := by
  obtain ⟨ψ, η, ξ₁, ξ₂⟩ := b
  rw [combine_entryTriple]
  simp only [Units.val_mul, unitaryAt, unitaryElt_inv_val, conjEntries_unitaryElt_val, twistedSplitElt_val,
    conjugateAt]

private theorem entries_eq' (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (v : ℂ) (ψ η ξ₁ ξ₂ : ℝ) :
    Matrix.of.symm (((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (unitaryElt ψ η ξ₁ ξ₂) :
        GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      combine (entryTriple (v, (ψ, η, ξ₁, ξ₂))) (a₁, a₂) :=
  entries_eq a₁ a₂ h v (ψ, η, ξ₁, ξ₂)

private theorem entry_norm_le_of_conjugateAt (b : Box) (M : Matrix (Fin 2) (Fin 2) ℂ) (B : ℝ)
    (h : ∀ i j, ‖conjugateAt b M i j‖ ≤ B) (i j : Fin 2) : ‖M i j‖ ≤ 4 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (h 0 0)
  obtain ⟨ψ, η, ξ₁, ξ₂⟩ := b
  set X : Matrix (Fin 2) (Fin 2) ℂ := kInv ψ η ξ₁ ξ₂ * M * kBar ψ η ξ₁ ξ₂ with hX
  have hX' : ∀ a c, ‖X a c‖ ≤ B := fun a c => h a c
  have hM : M = kMat ψ η ξ₁ ξ₂ * X * kBarInv ψ η ξ₁ ξ₂ := by
    rw [hX, Matrix.mul_assoc (kInv _ _ _ _), ← Matrix.mul_assoc (kMat _ _ _ _), kMat_mul_kInv, Matrix.one_mul,
      Matrix.mul_assoc, kBar_mul_kBarInv, Matrix.mul_one]
  have key : ∀ a c : Fin 2, ‖kMat ψ η ξ₁ ξ₂ i a * X a c * kBarInv ψ η ξ₁ ξ₂ c j‖ ≤ B := by
    intro a c
    rw [norm_mul, norm_mul]
    calc ‖kMat ψ η ξ₁ ξ₂ i a‖ * ‖X a c‖ * ‖kBarInv ψ η ξ₁ ξ₂ c j‖ ≤ 1 * B * 1 := by
          gcongr
          · exact kMat_entry_norm_le ψ η ξ₁ ξ₂ i a
          · exact hX' a c
          · exact kBarInv_entry_norm_le ψ η ξ₁ ξ₂ c j
      _ = B := by ring
  rw [hM, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, add_mul]
  calc ‖kMat ψ η ξ₁ ξ₂ i 0 * X 0 0 * kBarInv ψ η ξ₁ ξ₂ 0 j + kMat ψ η ξ₁ ξ₂ i 1 * X 1 0 * kBarInv ψ η ξ₁ ξ₂ 0 j +
          (kMat ψ η ξ₁ ξ₂ i 0 * X 0 1 * kBarInv ψ η ξ₁ ξ₂ 1 j + kMat ψ η ξ₁ ξ₂ i 1 * X 1 1 * kBarInv ψ η ξ₁ ξ₂ 1 j)‖
        ≤ ‖kMat ψ η ξ₁ ξ₂ i 0 * X 0 0 * kBarInv ψ η ξ₁ ξ₂ 0 j‖ + ‖kMat ψ η ξ₁ ξ₂ i 1 * X 1 0 * kBarInv ψ η ξ₁ ξ₂ 0 j‖ +
          (‖kMat ψ η ξ₁ ξ₂ i 0 * X 0 1 * kBarInv ψ η ξ₁ ξ₂ 1 j‖ +
            ‖kMat ψ η ξ₁ ξ₂ i 1 * X 1 1 * kBarInv ψ η ξ₁ ξ₂ 1 j‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ B + B + (B + B) := by gcongr <;> exact key _ _
    _ = 4 * B := by ring

private theorem entry_norm_le_norm (Y : Ent) (i j : Fin 2) : ‖Y i j‖ ≤ ‖Y‖ :=
  (norm_le_pi_norm (Y i) j).trans (norm_le_pi_norm Y i)

private theorem norm_fst_le_of_entryTriple (ω : Dom) (B : ℝ) (h : ‖entryTriple ω‖ ≤ B) : ‖ω.1‖ ≤ 4 * B := by
  have h3 : ‖(entryTriple ω).2.2‖ ≤ B := ((norm_snd_le _).trans (norm_snd_le _)).trans h
  have hent : ∀ i j, ‖conjugateAt ω.2 !![0, ω.1; 0, 0] i j‖ ≤ B := fun i j =>
    (entry_norm_le_norm _ i j).trans h3
  have := entry_norm_le_of_conjugateAt ω.2 _ B hent 0 1
  simpa using this

private theorem continuous_entryTriple : Continuous entryTriple := by
  have hexp : Continuous fun z : ℂ => Complex.exp z := Complex.continuous_exp
  have hconj : Continuous fun z : ℂ => (starRingEnd ℂ) z := Complex.continuous_conj
  have hre : Continuous fun x : ℝ => (x : ℂ) := Complex.continuous_ofReal
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_) <;>
    refine continuous_pi fun i => continuous_pi fun k => ?_ <;>
    fin_cases i <;> fin_cases k <;>
    simp only [conjugateAt, kInv, kBar, kMat, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_symm_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;>
    fun_prop

private theorem continuous_density : Continuous density := by
  unfold density
  fun_prop

private theorem density_aestronglyMeasurable : AEStronglyMeasurable density domMeasure :=
  continuous_density.measurable.aestronglyMeasurable

private theorem entryTriple_aestronglyMeasurable : AEStronglyMeasurable entryTriple domMeasure :=
  continuous_entryTriple.measurable.aestronglyMeasurable

private theorem abs_density_le (ω : Dom) : |density ω| ≤ 1 / (4 * Real.pi ^ 3) := by
  unfold density
  have hc : (0 : ℝ) ≤ 1 / (4 * Real.pi ^ 3) := by positivity
  rw [abs_mul, abs_of_nonneg hc, abs_mul]
  calc 1 / (4 * Real.pi ^ 3) * (|Real.sin ω.2.2.1| * |Real.cos ω.2.2.1|) ≤ 1 / (4 * Real.pi ^ 3) * (1 * 1) := by
        gcongr
        · exact Real.abs_sin_le_one _
        · exact Real.abs_cos_le_one _
    _ = 1 / (4 * Real.pi ^ 3) := by ring

private theorem slab (B : ℝ) :
    Integrable (fun ω : Dom => if ‖entryTriple ω‖ ≤ B then |density ω| else 0) domMeasure := by
  have habs : Measurable fun ω : Dom => |density ω| := by
    have h := continuous_density.measurable
    fun_prop
  have hmeas : Measurable fun ω : Dom => if ‖entryTriple ω‖ ≤ B then |density ω| else 0 :=
    Measurable.ite (measurableSet_le continuous_entryTriple.measurable.norm measurable_const) habs measurable_const
  have hdisc : Integrable (fun v : ℂ => (Metric.closedBall (0 : ℂ) (4 * B)).indicator
      (fun _ => (1 / (4 * Real.pi ^ 3) : ℝ)) v) (volume : Measure ℂ) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (hs := measure_closedBall_lt_top.ne))
  have hg : Integrable (fun ω : Dom => (Metric.closedBall (0 : ℂ) (4 * B)).indicator
      (fun _ => (1 / (4 * Real.pi ^ 3) : ℝ)) ω.1 * (fun _ : Box => (1 : ℝ)) ω.2) domMeasure :=
    hdisc.mul_prod (integrable_const (1 : ℝ))
  refine hg.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  simp only [mul_one, Real.norm_eq_abs]
  split_ifs with hω
  · have hv : ω.1 ∈ Metric.closedBall (0 : ℂ) (4 * B) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_fst_le_of_entryTriple ω B hω
    rw [Set.indicator_of_mem hv, abs_abs]
    exact abs_density_le ω
  · rw [abs_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _

private theorem integrable_of_continuous_of_bounded {α : Type} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℂ) (hf : Continuous f) (M : ℝ)
    (hM : ∀ x, ‖f x‖ ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall hM)

private theorem boxMeasure_integral_eq (g : Box → ℂ) (hg : Continuous g) (M : ℝ) (hM : ∀ b, ‖g b‖ ≤ M) :
    ∫ b, g b ∂boxMeasure =
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), g (ψ, η, ξ₁, ξ₂) := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  simp only [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le hπ2]
  have h₁ : Integrable g boxMeasure := integrable_of_continuous_of_bounded boxMeasure g hg M hM
  unfold boxMeasure at h₁ ⊢
  rw [integral_prod _ h₁]
  congr 1
  funext ψ
  have h₂ : Integrable (fun y => g (ψ, y)) boxMeasure₂ :=
    integrable_of_continuous_of_bounded boxMeasure₂ _ (hg.comp (continuous_const.prodMk continuous_id)) M
      fun y => hM _
  unfold boxMeasure₂ at h₂ ⊢
  rw [integral_prod _ h₂]
  congr 1
  funext η
  have h₃ : Integrable (fun y => g (ψ, η, y)) boxMeasure₃ :=
    integrable_of_continuous_of_bounded boxMeasure₃ _
      (hg.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))) M fun y => hM _
  unfold boxMeasure₃ at h₃ ⊢
  rw [integral_prod _ h₃]

private theorem continuous_combine (a : ℝ × ℝ) : Continuous fun Y : Ent × Ent × Ent => combine Y a := by
  unfold combine
  fun_prop

private theorem kBar_entry_norm_le (ψ η ξ₁ ξ₂ : ℝ) (i j : Fin 2) : ‖kBar ψ η ξ₁ ξ₂ i j‖ ≤ 1 := by
  simpa [kBar, Matrix.map_apply, Complex.norm_conj] using kMat_entry_norm_le ψ η ξ₁ ξ₂ i j

private theorem conjugateAt_entry_norm_le (b : Box) (M : Matrix (Fin 2) (Fin 2) ℂ) (B : ℝ)
    (h : ∀ i j, ‖M i j‖ ≤ B) (i j : Fin 2) : ‖conjugateAt b M i j‖ ≤ 4 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (h 0 0)
  obtain ⟨ψ, η, ξ₁, ξ₂⟩ := b
  have key : ∀ a c : Fin 2, ‖kInv ψ η ξ₁ ξ₂ i a * M a c * kBar ψ η ξ₁ ξ₂ c j‖ ≤ B := by
    intro a c
    rw [norm_mul, norm_mul]
    calc ‖kInv ψ η ξ₁ ξ₂ i a‖ * ‖M a c‖ * ‖kBar ψ η ξ₁ ξ₂ c j‖ ≤ 1 * B * 1 := by
          gcongr
          · exact kInv_entry_norm_le ψ η ξ₁ ξ₂ i a
          · exact h a c
          · exact kBar_entry_norm_le ψ η ξ₁ ξ₂ c j
      _ = B := by ring
  show ‖(kInv ψ η ξ₁ ξ₂ * M * kBar ψ η ξ₁ ξ₂) i j‖ ≤ 4 * B
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, add_mul]
  calc ‖kInv ψ η ξ₁ ξ₂ i 0 * M 0 0 * kBar ψ η ξ₁ ξ₂ 0 j + kInv ψ η ξ₁ ξ₂ i 1 * M 1 0 * kBar ψ η ξ₁ ξ₂ 0 j +
          (kInv ψ η ξ₁ ξ₂ i 0 * M 0 1 * kBar ψ η ξ₁ ξ₂ 1 j + kInv ψ η ξ₁ ξ₂ i 1 * M 1 1 * kBar ψ η ξ₁ ξ₂ 1 j)‖
        ≤ ‖kInv ψ η ξ₁ ξ₂ i 0 * M 0 0 * kBar ψ η ξ₁ ξ₂ 0 j‖ + ‖kInv ψ η ξ₁ ξ₂ i 1 * M 1 0 * kBar ψ η ξ₁ ξ₂ 0 j‖ +
          (‖kInv ψ η ξ₁ ξ₂ i 0 * M 0 1 * kBar ψ η ξ₁ ξ₂ 1 j‖ + ‖kInv ψ η ξ₁ ξ₂ i 1 * M 1 1 * kBar ψ η ξ₁ ξ₂ 1 j‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ B + B + (B + B) := by gcongr <;> exact key _ _
    _ = 4 * B := by ring

private theorem norm_le_of_entries (Y : Ent) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i j, ‖Y i j‖ ≤ B) : ‖Y‖ ≤ B :=
  (pi_norm_le_iff_of_nonneg hB).2 fun i => (pi_norm_le_iff_of_nonneg hB).2 fun j => h i j

private theorem norm_entryTriple_le (ω : Dom) : ‖entryTriple ω‖ ≤ 4 * (1 + ‖ω.1‖) := by
  have h0 : (0 : ℝ) ≤ 4 * (1 + ‖ω.1‖) := by positivity
  have hv : (0 : ℝ) ≤ ‖ω.1‖ := norm_nonneg _
  have h1 : ∀ i j, ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1 + ‖ω.1‖ := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  have h2 : ∀ i j, ‖(!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1 + ‖ω.1‖ := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  have h3 : ∀ i j, ‖(!![0, ω.1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1 + ‖ω.1‖ := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  show ‖((conjugateAt ω.2 !![1, 0; 0, 0], conjugateAt ω.2 !![0, 0; 0, 1], conjugateAt ω.2 !![0, ω.1; 0, 0]) :
    Ent × Ent × Ent)‖ ≤ 4 * (1 + ‖ω.1‖)
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le ?_ (max_le ?_ ?_)
  · exact norm_le_of_entries _ _ h0 (conjugateAt_entry_norm_le ω.2 _ _ h1)
  · exact norm_le_of_entries _ _ h0 (conjugateAt_entry_norm_le ω.2 _ _ h2)
  · exact norm_le_of_entries _ _ h0 (conjugateAt_entry_norm_le ω.2 _ _ h3)

private theorem norm_fst_le_of_combine (a₁ a₂ : ℝ) (v : ℂ) (b : Box) (B : ℝ)
    (h : ‖combine (entryTriple (v, b)) (a₁, a₂)‖ ≤ B) : ‖v‖ ≤ 4 * B := by
  rw [combine_entryTriple] at h
  have hent : ∀ i j, ‖conjugateAt b !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] i j‖ ≤ B := fun i j =>
    (entry_norm_le_norm _ i j).trans h
  have := entry_norm_le_of_conjugateAt b _ B hent 0 1
  simpa using this

private theorem sqrt_le_of_combine (a₁ a₂ : ℝ) (v : ℂ) (b : Box) (B : ℝ)
    (h : ‖combine (entryTriple (v, b)) (a₁, a₂)‖ ≤ B) : Real.sqrt a₁ ≤ 4 * B ∧ Real.sqrt a₂ ≤ 4 * B := by
  rw [combine_entryTriple] at h
  have hent : ∀ i j, ‖conjugateAt b !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] i j‖ ≤ B := fun i j =>
    (entry_norm_le_norm _ i j).trans h
  have h1 := entry_norm_le_of_conjugateAt b _ B hent 0 0
  have h2 := entry_norm_le_of_conjugateAt b _ B hent 1 1
  constructor
  · simpa [abs_of_nonneg (Real.sqrt_nonneg a₁)] using h1
  · simpa [abs_of_nonneg (Real.sqrt_nonneg a₂)] using h2

private theorem norm_det_conjugateAt (b : Box) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖Matrix.det (Matrix.of (conjugateAt b M))‖ = ‖Matrix.det M‖ := by
  obtain ⟨ψ, η, ξ₁, ξ₂⟩ := b
  have hdet : Matrix.det (kInv ψ η ξ₁ ξ₂) * Matrix.det (kMat ψ η ξ₁ ξ₂) = 1 := by
    rw [← Matrix.det_mul, kInv_mul_kMat, Matrix.det_one]
  have hconj : Matrix.det (kBar ψ η ξ₁ ξ₂) = (starRingEnd ℂ) (Matrix.det (kMat ψ η ξ₁ ξ₂)) := by
    rw [kBar, RingHom.map_det]
    rfl
  have hn : ‖Matrix.det (kInv ψ η ξ₁ ξ₂)‖ * ‖Matrix.det (kMat ψ η ξ₁ ξ₂)‖ = 1 := by
    rw [← norm_mul, hdet, norm_one]
  show ‖Matrix.det (kInv ψ η ξ₁ ξ₂ * M * kBar ψ η ξ₁ ξ₂)‖ = ‖Matrix.det M‖
  rw [Matrix.det_mul, Matrix.det_mul, hconj, norm_mul, norm_mul, Complex.norm_conj]
  calc ‖Matrix.det (kInv ψ η ξ₁ ξ₂)‖ * ‖Matrix.det M‖ * ‖Matrix.det (kMat ψ η ξ₁ ξ₂)‖
      = ‖Matrix.det (kInv ψ η ξ₁ ξ₂)‖ * ‖Matrix.det (kMat ψ η ξ₁ ξ₂)‖ * ‖Matrix.det M‖ := by ring
    _ = ‖Matrix.det M‖ := by rw [hn, one_mul]

private theorem norm_det_splitMatrix (a₁ a₂ : ℝ) (v : ℂ) :
    ‖Matrix.det (!![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ)‖ =
      Real.sqrt a₁ * Real.sqrt a₂ := by
  rw [Matrix.det_fin_two_of]
  simp [abs_of_nonneg (Real.sqrt_nonneg a₁), abs_of_nonneg (Real.sqrt_nonneg a₂)]

private def sqSum (Y : Ent × Ent × Ent) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (‖Y.1 i j‖ ^ 2 + ‖Y.2.1 i j‖ ^ 2 + ‖Y.2.2 i j‖ ^ 2)

private theorem contDiff_sqSum : ContDiff ℝ (⊤ : ℕ∞) sqSum := by
  unfold sqSum
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun Y : Ent × Ent × Ent => Y.1 i j :=
    (contDiff_apply ℝ ℂ j).comp ((contDiff_apply ℝ (Fin 2 → ℂ) i).comp contDiff_fst)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun Y : Ent × Ent × Ent => Y.2.1 i j :=
    (contDiff_apply ℝ ℂ j).comp ((contDiff_apply ℝ (Fin 2 → ℂ) i).comp (contDiff_fst.comp contDiff_snd))
  have h3 : ContDiff ℝ (⊤ : ℕ∞) fun Y : Ent × Ent × Ent => Y.2.2 i j :=
    (contDiff_apply ℝ ℂ j).comp ((contDiff_apply ℝ (Fin 2 → ℂ) i).comp (contDiff_snd.comp contDiff_snd))
  exact ((h1.norm_sq (𝕜 := ℝ)).add (h2.norm_sq (𝕜 := ℝ))).add (h3.norm_sq (𝕜 := ℝ))

private theorem sqSum_nonneg (Y : Ent × Ent × Ent) : 0 ≤ sqSum Y := by
  unfold sqSum
  positivity

private theorem sqSum_le (Y : Ent × Ent × Ent) : sqSum Y ≤ 12 * ‖Y‖ ^ 2 := by
  have h1 : ∀ i j, ‖Y.1 i j‖ ≤ ‖Y‖ := fun i j => (entry_norm_le_norm _ i j).trans (norm_fst_le Y)
  have h2 : ∀ i j, ‖Y.2.1 i j‖ ≤ ‖Y‖ := fun i j =>
    (entry_norm_le_norm _ i j).trans ((norm_fst_le Y.2).trans (norm_snd_le Y))
  have h3 : ∀ i j, ‖Y.2.2 i j‖ ≤ ‖Y‖ := fun i j =>
    (entry_norm_le_norm _ i j).trans ((norm_snd_le Y.2).trans (norm_snd_le Y))
  have hterm : ∀ i j, ‖Y.1 i j‖ ^ 2 + ‖Y.2.1 i j‖ ^ 2 + ‖Y.2.2 i j‖ ^ 2 ≤ 3 * ‖Y‖ ^ 2 := by
    intro i j
    have a1 : ‖Y.1 i j‖ ^ 2 ≤ ‖Y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h1 i j) 2
    have a2 : ‖Y.2.1 i j‖ ^ 2 ≤ ‖Y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h2 i j) 2
    have a3 : ‖Y.2.2 i j‖ ^ 2 ≤ ‖Y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h3 i j) 2
    linarith
  unfold sqSum
  calc ∑ i : Fin 2, ∑ j : Fin 2, (‖Y.1 i j‖ ^ 2 + ‖Y.2.1 i j‖ ^ 2 + ‖Y.2.2 i j‖ ^ 2)
      ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, 3 * ‖Y‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = 12 * ‖Y‖ ^ 2 := by simp; ring

private theorem norm_le_sqrt_sqSum (Y : Ent × Ent × Ent) : ‖Y‖ ≤ Real.sqrt (sqSum Y) := by
  have hs : 0 ≤ Real.sqrt (sqSum Y) := Real.sqrt_nonneg _
  have hle : ∀ i j, ‖Y.1 i j‖ ^ 2 ≤ sqSum Y ∧ ‖Y.2.1 i j‖ ^ 2 ≤ sqSum Y ∧ ‖Y.2.2 i j‖ ^ 2 ≤ sqSum Y := by
    intro i j
    have hij : ‖Y.1 i j‖ ^ 2 + ‖Y.2.1 i j‖ ^ 2 + ‖Y.2.2 i j‖ ^ 2 ≤ sqSum Y := by
      unfold sqSum
      calc ‖Y.1 i j‖ ^ 2 + ‖Y.2.1 i j‖ ^ 2 + ‖Y.2.2 i j‖ ^ 2
          ≤ ∑ j' : Fin 2, (‖Y.1 i j'‖ ^ 2 + ‖Y.2.1 i j'‖ ^ 2 + ‖Y.2.2 i j'‖ ^ 2) :=
            Finset.single_le_sum (f := fun j' => ‖Y.1 i j'‖ ^ 2 + ‖Y.2.1 i j'‖ ^ 2 + ‖Y.2.2 i j'‖ ^ 2)
              (fun j' _ => by positivity) (Finset.mem_univ j)
        _ ≤ ∑ i' : Fin 2, ∑ j' : Fin 2, (‖Y.1 i' j'‖ ^ 2 + ‖Y.2.1 i' j'‖ ^ 2 + ‖Y.2.2 i' j'‖ ^ 2) :=
            Finset.single_le_sum
              (f := fun i' => ∑ j' : Fin 2, (‖Y.1 i' j'‖ ^ 2 + ‖Y.2.1 i' j'‖ ^ 2 + ‖Y.2.2 i' j'‖ ^ 2))
              (fun i' _ => by positivity) (Finset.mem_univ i)
    have p1 : 0 ≤ ‖Y.1 i j‖ ^ 2 := by positivity
    have p2 : 0 ≤ ‖Y.2.1 i j‖ ^ 2 := by positivity
    have p3 : 0 ≤ ‖Y.2.2 i j‖ ^ 2 := by positivity
    exact ⟨by linarith, by linarith, by linarith⟩
  have hb : ∀ (z : ℂ), ‖z‖ ^ 2 ≤ sqSum Y → ‖z‖ ≤ Real.sqrt (sqSum Y) := fun z hz =>
    (le_abs_self _).trans (Real.abs_le_sqrt hz)
  show ‖((Y.1, Y.2.1, Y.2.2) : Ent × Ent × Ent)‖ ≤ Real.sqrt (sqSum Y)
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le ?_ (max_le ?_ ?_)
  · exact norm_le_of_entries _ _ hs fun i j => hb _ (hle i j).1
  · exact norm_le_of_entries _ _ hs fun i j => hb _ (hle i j).2.1
  · exact norm_le_of_entries _ _ hs fun i j => hb _ (hle i j).2.2

section IntegralFamily

variable {E : Type} [NormedAddCommGroup E]
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (sc : Ω → ℝ) (X : Ω → E)
variable (Q : Type) [NormedAddCommGroup Q]

private theorem exists_bound_of_family {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : E × Q → F)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ M B₀ : ℝ, ∀ (c : ℝ) (x : E) (y : Q), ‖c • Ψ (x, y)‖ ≤ M * (if ‖x‖ ≤ B₀ then |c| else 0) := by
  obtain ⟨M, hM⟩ := hΨ.bounded_above_of_compact_support hΨc
  obtain ⟨B₀, hB₀⟩ := (hΨc : IsCompact (tsupport Ψ)).isBounded.exists_norm_le
  refine ⟨M, B₀, fun c x y => ?_⟩
  split_ifs with hx
  · rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM (x, y)) (abs_nonneg c)
  · have hz : Ψ (x, y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have h1 := hB₀ (x, y) hmem
      have h2 : ‖x‖ ≤ ‖((x, y) : E × Q)‖ := norm_fst_le (x, y)
      exact hx (h2.trans h1)
    simp [hz]

variable (hsc : AEStronglyMeasurable sc μ) (hX : AEStronglyMeasurable X μ)
  (hslab : ∀ B : ℝ, Integrable (fun ω => if ‖X ω‖ ≤ B then |sc ω| else 0) μ)

include hsc hX in
private theorem integrand_aestronglyMeasurable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : E × Q → F)
    (hΨ : Continuous Ψ) (y : Q) : AEStronglyMeasurable (fun ω => sc ω • Ψ (X ω, y)) μ :=
  hsc.smul (hΨ.comp_aestronglyMeasurable (hX.prodMk aestronglyMeasurable_const))

include hsc hX hslab in
private theorem integrand_integrable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : E × Q → F)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) (y : Q) : Integrable (fun ω => sc ω • Ψ (X ω, y)) μ := by
  obtain ⟨M, B₀, hMB⟩ := exists_bound_of_family Q Ψ hΨ hΨc
  refine ((hslab B₀).const_mul M).mono' (integrand_aestronglyMeasurable μ sc X Q hsc hX Ψ hΨ y) ?_
  exact Filter.Eventually.of_forall fun ω => hMB (sc ω) (X ω) y

variable [NormedSpace ℝ E] [NormedSpace ℝ Q]

private def partialQ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : E × Q → F) (z : E × Q) : Q →L[ℝ] F :=
  (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inr ℝ E Q)

private theorem partialQ_contDiff {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : E × Q → F)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) : ContDiff ℝ (⊤ : ℕ∞) (partialQ Q Ψ) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun z => (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inr ℝ E Q)
  exact (contDiff_infty_iff_fderiv.1 hΨ).2.clm_comp contDiff_const

private theorem partialQ_hasCompactSupport {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : E × Q → F)
    (hΨc : HasCompactSupport Ψ) : HasCompactSupport (partialQ Q Ψ) := by
  have h : HasCompactSupport
      ((fun L : E × Q →L[ℝ] F => L.comp (ContinuousLinearMap.inr ℝ E Q)) ∘ fderiv ℝ Ψ) :=
    (hΨc.fderiv ℝ).comp_left (by simp)
  exact h

private theorem partialQ_hasFDerivAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : E × Q → F)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (c : ℝ) (x : E) (y : Q) :
    HasFDerivAt (fun y : Q => c • Ψ (x, y)) (c • partialQ Q Ψ (x, y)) y := by
  have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (x, y)) (x, y) := ((contDiff_infty_iff_fderiv.1 hΨ).1 (x, y)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Q => (x, y)) (ContinuousLinearMap.inr ℝ E Q) y := hasFDerivAt_prodMk_right x y
  exact (h1.comp y h2).const_smul c

include hsc hX hslab in

private theorem integralFamily_hasFDerivAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : E × Q → F) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) (y₀ : Q) :
    HasFDerivAt (fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ) (∫ ω, sc ω • partialQ Q Ψ (X ω, y₀) ∂μ) y₀ := by
  have hΨ' := partialQ_contDiff Q Ψ hΨ
  have hΨ'c := partialQ_hasCompactSupport Q Ψ hΨc
  obtain ⟨M, B₀, hMB⟩ := exists_bound_of_family Q (partialQ Q Ψ) hΨ'.continuous hΨ'c
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun y ω => sc ω • partialQ Q Ψ (X ω, y))
    Filter.univ_mem ?_ ?_ ?_ ?_ ((hslab B₀).const_mul M) ?_
  · exact Filter.Eventually.of_forall fun y => integrand_aestronglyMeasurable μ sc X Q hsc hX Ψ hΨ.continuous y
  · exact integrand_integrable μ sc X Q hsc hX hslab Ψ hΨ.continuous hΨc y₀
  · exact integrand_aestronglyMeasurable μ sc X Q hsc hX (partialQ Q Ψ) hΨ'.continuous y₀
  · exact Filter.Eventually.of_forall fun ω y _ => hMB (sc ω) (X ω) y
  · exact Filter.Eventually.of_forall fun ω y _ => partialQ_hasFDerivAt Q Ψ hΨ (sc ω) (X ω) y

include hsc hX hslab in

private theorem contDiff_integral_family_nat (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ψ : E × Q → F),
      ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ → ContDiff ℝ n (fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ) := by
  induction n with
  | zero =>
    intro F _ _ _ Ψ hΨ hΨc
    have key : Continuous fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ :=
      continuous_iff_continuousAt.2 fun y₀ =>
        (integralFamily_hasFDerivAt μ sc X Q hsc hX hslab Ψ hΨ hΨc y₀).continuousAt
    exact_mod_cast (contDiff_zero.2 key : ContDiff ℝ 0 fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ)
  | succ n ih =>
    intro F _ _ _ Ψ hΨ hΨc
    have key := (contDiff_succ_iff_hasFDerivAt (n := n)).2 ⟨fun y : Q => ∫ ω, sc ω • partialQ Q Ψ (X ω, y) ∂μ,
      ih (Q →L[ℝ] F) (partialQ Q Ψ) (partialQ_contDiff Q Ψ hΨ) (partialQ_hasCompactSupport Q Ψ hΨc),
      fun y₀ => integralFamily_hasFDerivAt μ sc X Q hsc hX hslab Ψ hΨ hΨc y₀⟩
    exact_mod_cast key

include hsc hX hslab in
private theorem contDiff_integral_family (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : E × Q → F) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ) :=
  contDiff_infty.2 fun n => contDiff_integral_family_nat μ sc X Q hsc hX hslab n F Ψ hΨ hΨc

end IntegralFamily

private theorem engine {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (sc : Ω → ℝ) (X : Ω → E) (hsc : AEStronglyMeasurable sc μ) (hX : AEStronglyMeasurable X μ)
    (hslab : ∀ B : ℝ, Integrable (fun ω => if ‖X ω‖ ≤ B then |sc ω| else 0) μ)
    (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] (Ψ : E × Q → ℂ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Q => ∫ ω, sc ω • Ψ (X ω, y) ∂μ) :=
  contDiff_integral_family μ sc X Q hsc hX hslab ℂ Ψ hΨ hΨc

private def detNorm (P : Type) (q : Ent × P) : ℝ := ‖Matrix.det (Matrix.of q.1)‖

private theorem continuous_detNorm (P : Type) [TopologicalSpace P] : Continuous (detNorm P) := by
  have h : Continuous fun q : Ent × P => Matrix.of q.1 := by
    refine continuous_matrix fun i k => ?_
    simp only [Matrix.of_apply]
    exact (continuous_apply k).comp ((continuous_apply i).comp continuous_fst)
  exact h.matrix_det.norm

section Family

variable (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ)

private def family (q : ℝ × ℝ × P) : ℂ :=
  twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1

private theorem unitaryAverage_eq_boxIntegral (hΦ : Continuous Φ) (M : ℝ) (hM : ∀ z, ‖Φ z‖ ≤ M) (a₁ a₂ : ℝ)
    (h : 0 < a₁ ∧ 0 < a₂) (v : ℂ) (p : P) :
    unitaryAverage (fun k => Φ (Matrix.of.symm ((k⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries k : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ), p)) =
      (1 / (4 * Real.pi ^ 3) : ℝ) •
        ∫ b, (Real.sin b.2.1 * Real.cos b.2.1) • Φ (combine (entryTriple (v, b)) (a₁, a₂), p) ∂boxMeasure := by
  have hg : Continuous fun b : Box =>
      (Real.sin b.2.1 * Real.cos b.2.1) • Φ (combine (entryTriple (v, b)) (a₁, a₂), p) := by
    have h1 : Continuous fun b : Box => Real.sin b.2.1 * Real.cos b.2.1 := by fun_prop
    have h2 : Continuous fun b : Box => Φ (combine (entryTriple (v, b)) (a₁, a₂), p) :=
      hΦ.comp (((continuous_combine (a₁, a₂)).comp
        (continuous_entryTriple.comp (continuous_const.prodMk continuous_id))).prodMk continuous_const)
    exact h1.smul h2
  have hgM : ∀ b : Box, ‖(Real.sin b.2.1 * Real.cos b.2.1) • Φ (combine (entryTriple (v, b)) (a₁, a₂), p)‖ ≤ M := by
    intro b
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    calc |Real.sin b.2.1| * |Real.cos b.2.1| * ‖Φ (combine (entryTriple (v, b)) (a₁, a₂), p)‖ ≤ 1 * 1 * M := by
          gcongr
          · exact Real.abs_sin_le_one _
          · exact Real.abs_cos_le_one _
          · exact hM _
      _ = M := by ring
  rw [boxMeasure_integral_eq _ hg M hgM]
  unfold unitaryAverage
  simp only [entries_eq', Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

private theorem family_eq_integral (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (Ψ : (Ent × Ent × Ent) × (ℝ × ℝ × P) → ℂ) (hΨcont : Continuous Ψ) (hΨc : HasCompactSupport Ψ) (q : ℝ × ℝ × P)
    (hq : 0 < q.1 ∧ 0 < q.2.1)
    (hΨ : ∀ ω : Dom, Ψ (entryTriple ω, q) = Φ (combine (entryTriple ω) (q.1, q.2.1), q.2.2)) :
    family P Φ q = ∫ ω, density ω • Ψ (entryTriple ω, q) ∂domMeasure := by
  obtain ⟨M, hM⟩ := hΦ.bounded_above_of_compact_support hΦc
  have hint : Integrable (fun ω : Dom => density ω • Ψ (entryTriple ω, q)) domMeasure :=
    integrand_integrable domMeasure density entryTriple (ℝ × ℝ × P) density_aestronglyMeasurable
      entryTriple_aestronglyMeasurable slab Ψ hΨcont hΨc q
  unfold family twistedSplitTransform
  rw [dif_pos hq]
  unfold domMeasure at hint ⊢
  rw [integral_prod _ hint]
  congr 1
  funext v
  rw [unitaryAverage_eq_boxIntegral P Φ hΦ M hM q.1 q.2.1 hq v q.2.2, ← integral_smul]
  congr 1
  funext b
  rw [hΨ (v, b), smul_smul]
  rfl

private theorem family_eq_zero_of_slice (q : ℝ × ℝ × P)
    (h : ∀ (hq : 0 < q.1 ∧ 0 < q.2.1) (v : ℂ) (ψ η ξ₁ ξ₂ : ℝ),
      Φ (Matrix.of.symm (((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * twistedSplitElt q.1 q.2.1 v hq *
        conjEntries (unitaryElt ψ η ξ₁ ξ₂) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), q.2.2) = 0) :
    family P Φ q = 0 := by
  unfold family twistedSplitTransform
  split_ifs with hq
  · simp only [unitaryAverage, h hq]
    simp
  · rfl

private theorem exists_vanishing (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {x | IsUnit (Matrix.det (Matrix.of x.1))}) :
    ∃ (c C : ℝ) (K : Set P), 0 < c ∧ IsCompact K ∧
      ∀ q : ℝ × ℝ × P, (q.1 < c ∨ q.2.1 < c ∨ C < q.1 ∨ C < q.2.1 ∨ q.2.2 ∉ K) → family P Φ q = 0 := by
  have hcomp : IsCompact (tsupport Φ) := hΦc
  rcases (tsupport Φ).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, 1, ∅, one_pos, isCompact_empty, fun q _ => ?_⟩
    apply family_eq_zero_of_slice
    intro hq v ψ η ξ₁ ξ₂
    apply image_eq_zero_of_notMem_tsupport
    rw [hemp]
    exact Set.notMem_empty _
  · obtain ⟨x₀, hx₀, hmin⟩ := hcomp.exists_isMinOn hne (continuous_detNorm P).continuousOn
    obtain ⟨B₀, hB₀⟩ := hcomp.isBounded.exists_norm_le
    have hmpos : 0 < detNorm P x₀ := by
      have hunit : IsUnit (Matrix.det (Matrix.of x₀.1)) := hΦU hx₀
      show 0 < ‖Matrix.det (Matrix.of x₀.1)‖
      exact norm_pos_iff.mpr hunit.ne_zero
    have hB₁pos : 0 < max B₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have h4B : 0 < 4 * max B₀ 1 := by positivity
    refine ⟨detNorm P x₀ / (4 * max B₀ 1) * (detNorm P x₀ / (4 * max B₀ 1)), 4 * max B₀ 1 * (4 * max B₀ 1),
      Prod.snd '' tsupport Φ, by positivity, hcomp.image continuous_snd, fun q hout => ?_⟩
    apply family_eq_zero_of_slice
    intro hq v ψ η ξ₁ ξ₂
    rw [entries_eq']
    by_contra hne'
    have hmem : ((combine (entryTriple (v, (ψ, η, ξ₁, ξ₂))) (q.1, q.2.1), q.2.2) : Ent × P) ∈ tsupport Φ :=
      subset_tsupport Φ (Function.mem_support.mpr hne')
    have hxB : ‖combine (entryTriple (v, (ψ, η, ξ₁, ξ₂))) (q.1, q.2.1)‖ ≤ max B₀ 1 :=
      ((norm_fst_le _).trans (hB₀ _ hmem)).trans (le_max_left _ _)
    obtain ⟨hs₁, hs₂⟩ := sqrt_le_of_combine q.1 q.2.1 v (ψ, η, ξ₁, ξ₂) (max B₀ 1) hxB
    have hdet : detNorm P x₀ ≤ Real.sqrt q.1 * Real.sqrt q.2.1 := by
      have h1 := isMinOn_iff.mp hmin _ hmem
      have h2 : detNorm P ((combine (entryTriple (v, (ψ, η, ξ₁, ξ₂))) (q.1, q.2.1), q.2.2) : Ent × P) =
          Real.sqrt q.1 * Real.sqrt q.2.1 := by
        show ‖Matrix.det (Matrix.of (combine (entryTriple (v, (ψ, η, ξ₁, ξ₂))) (q.1, q.2.1)))‖ = _
        rw [combine_entryTriple, norm_det_conjugateAt, norm_det_splitMatrix]
      rw [h2] at h1
      exact h1
    have hsq₁ : Real.sqrt q.1 * Real.sqrt q.1 = q.1 := Real.mul_self_sqrt hq.1.le
    have hsq₂ : Real.sqrt q.2.1 * Real.sqrt q.2.1 = q.2.1 := Real.mul_self_sqrt hq.2.le
    have hr₁ : 0 ≤ Real.sqrt q.1 := Real.sqrt_nonneg _
    have hr₂ : 0 ≤ Real.sqrt q.2.1 := Real.sqrt_nonneg _
    have hl₁ : detNorm P x₀ / (4 * max B₀ 1) ≤ Real.sqrt q.1 := by
      rw [div_le_iff₀ h4B]
      calc detNorm P x₀ ≤ Real.sqrt q.1 * Real.sqrt q.2.1 := hdet
        _ ≤ Real.sqrt q.1 * (4 * max B₀ 1) := by gcongr
    have hl₂ : detNorm P x₀ / (4 * max B₀ 1) ≤ Real.sqrt q.2.1 := by
      rw [div_le_iff₀ h4B]
      calc detNorm P x₀ ≤ Real.sqrt q.1 * Real.sqrt q.2.1 := hdet
        _ ≤ 4 * max B₀ 1 * Real.sqrt q.2.1 := by gcongr
        _ = Real.sqrt q.2.1 * (4 * max B₀ 1) := mul_comm _ _
    have hc₀ : 0 ≤ detNorm P x₀ / (4 * max B₀ 1) := by positivity
    rcases hout with h | h | h | h | h
    · have : detNorm P x₀ / (4 * max B₀ 1) * (detNorm P x₀ / (4 * max B₀ 1)) ≤ q.1 := by
        rw [← hsq₁]
        exact mul_le_mul hl₁ hl₁ hc₀ hr₁
      exact absurd this (not_le.mpr h)
    · have : detNorm P x₀ / (4 * max B₀ 1) * (detNorm P x₀ / (4 * max B₀ 1)) ≤ q.2.1 := by
        rw [← hsq₂]
        exact mul_le_mul hl₂ hl₂ hc₀ hr₂
      exact absurd this (not_le.mpr h)
    · have : q.1 ≤ 4 * max B₀ 1 * (4 * max B₀ 1) := by
        rw [← hsq₁]
        exact mul_le_mul hs₁ hs₁ hr₁ h4B.le
      exact absurd this (not_le.mpr h)
    · have : q.2.1 ≤ 4 * max B₀ 1 * (4 * max B₀ 1) := by
        rw [← hsq₂]
        exact mul_le_mul hs₂ hs₂ hr₂ h4B.le
      exact absurd this (not_le.mpr h)
    · exact h ⟨_, hmem, rfl⟩

private theorem family_hasCompactSupport (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {x | IsUnit (Matrix.det (Matrix.of x.1))}) : HasCompactSupport (family P Φ) := by
  obtain ⟨c, C, K, hc, hK, hvan⟩ := exists_vanishing P Φ hΦ hΦc hΦU
  refine HasCompactSupport.of_support_subset_isCompact ((isCompact_Icc.prod (isCompact_Icc.prod hK)) :
    IsCompact (Set.Icc c C ×ˢ (Set.Icc c C ×ˢ K))) ?_
  intro q hq
  by_contra hnot
  apply hq
  apply hvan
  simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at hnot
  tauto

private theorem tsupport_family_subset (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {x | IsUnit (Matrix.det (Matrix.of x.1))}) :
    tsupport (family P Φ) ⊆ {q | q.1 * q.2.1 ≠ 0} := by
  obtain ⟨c, C, K, hc, hK, hvan⟩ := exists_vanishing P Φ hΦ hΦc hΦU
  have hclosed : IsClosed (Set.Icc c C ×ˢ (Set.Icc c C ×ˢ (Set.univ : Set P))) :=
    isClosed_Icc.prod (isClosed_Icc.prod isClosed_univ)
  have hsub : Function.support (family P Φ) ⊆ Set.Icc c C ×ˢ (Set.Icc c C ×ˢ (Set.univ : Set P)) := by
    intro q hq
    by_contra hnot
    apply hq
    apply hvan
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true, not_and_or, not_le] at hnot
    tauto
  intro q hq
  have hmem := closure_minimal hsub hclosed hq
  simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true] at hmem
  exact mul_ne_zero (lt_of_lt_of_le hc hmem.1.1).ne' (lt_of_lt_of_le hc hmem.2.1).ne'

variable [NormedSpace ℝ P]

private theorem exists_cutoff (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (q₀ : ℝ × ℝ × P)
    (hq₀ : 0 < q₀.1 ∧ 0 < q₀.2.1) :
    ∃ Ψ : (Ent × Ent × Ent) × (ℝ × ℝ × P) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧
      ∀ᶠ q in nhds q₀, ∀ ω : Dom, Ψ (entryTriple ω, q) = Φ (combine (entryTriple ω) (q.1, q.2.1), q.2.2) := by
  have hcomp : IsCompact (tsupport Φ) := hΦc
  obtain ⟨B₀, hB₀⟩ := hcomp.isBounded.exists_norm_le
  have hq₁ : 0 < q₀.1 := hq₀.1
  have hq₂ : 0 < q₀.2.1 := hq₀.2

  let χ₁ : ContDiffBump q₀.1 := ⟨q₀.1 / 4, q₀.1 / 2, by positivity, by linarith⟩
  let χ₂ : ContDiffBump q₀.2.1 := ⟨q₀.2.1 / 4, q₀.2.1 / 2, by positivity, by linarith⟩

  let R : ℝ := 4 * (1 + 4 * B₀)
  let χ₀ : ContDiffBump (0 : ℝ) := ⟨12 * R ^ 2 + 1, 12 * R ^ 2 + 2, by positivity, by linarith⟩
  refine ⟨fun z => (χ₁ z.2.1 * χ₂ z.2.2.1 * χ₀ (sqSum z.1)) • Φ (combine z.1 (z.2.1, z.2.2.1), z.2.2.2), ?_, ?_, ?_⟩
  ·
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : 0 < z.2.1 ∧ 0 < z.2.2.1
    · have h₁ : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Ent × Ent × Ent) × (ℝ × ℝ × P) => χ₁ z.2.1) z :=
        χ₁.contDiffAt.comp z contDiffAt_snd.fst
      have h₂ : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Ent × Ent × Ent) × (ℝ × ℝ × P) => χ₂ z.2.2.1) z :=
        χ₂.contDiffAt.comp z contDiffAt_snd.snd.fst
      have h₀ : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Ent × Ent × Ent) × (ℝ × ℝ × P) => χ₀ (sqSum z.1)) z :=
        χ₀.contDiffAt.comp z (contDiff_sqSum.contDiffAt.comp z contDiffAt_fst)
      have hs₁ : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Ent × Ent × Ent) × (ℝ × ℝ × P) => (Real.sqrt z.2.1 : ℂ)) z :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp z ((Real.contDiffAt_sqrt hz.1.ne').comp z contDiffAt_snd.fst)
      have hs₂ : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Ent × Ent × Ent) × (ℝ × ℝ × P) => (Real.sqrt z.2.2.1 : ℂ)) z :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp z
          ((Real.contDiffAt_sqrt hz.2.ne').comp z contDiffAt_snd.snd.fst)
      have hc : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z : (Ent × Ent × Ent) × (ℝ × ℝ × P) => combine z.1 (z.2.1, z.2.2.1)) z := by
        show ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Ent × Ent × Ent) × (ℝ × ℝ × P) =>
          (Real.sqrt z.2.1 : ℂ) • z.1.1 + (Real.sqrt z.2.2.1 : ℂ) • z.1.2.1 + z.1.2.2) z
        exact ((hs₁.smul contDiffAt_fst.fst).add (hs₂.smul contDiffAt_fst.snd.fst)).add contDiffAt_fst.snd.snd
      have hΦ' : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z : (Ent × Ent × Ent) × (ℝ × ℝ × P) => Φ (combine z.1 (z.2.1, z.2.2.1), z.2.2.2)) z :=
        hΦ.contDiffAt.comp z (hc.prodMk contDiffAt_snd.snd.snd)
      exact ((h₁.mul h₂).mul h₀).smul hΦ'
    ·
      have hopen : IsOpen {w : (Ent × Ent × Ent) × (ℝ × ℝ × P) | w.2.1 < q₀.1 / 2 ∨ w.2.2.1 < q₀.2.1 / 2} :=
        (isOpen_lt (continuous_fst.comp continuous_snd) continuous_const).union
          (isOpen_lt (continuous_fst.comp (continuous_snd.comp continuous_snd)) continuous_const)
      have hmem : z ∈ {w : (Ent × Ent × Ent) × (ℝ × ℝ × P) | w.2.1 < q₀.1 / 2 ∨ w.2.2.1 < q₀.2.1 / 2} := by
        by_contra hcon
        simp only [Set.mem_setOf_eq, not_or, not_lt] at hcon
        exact hz ⟨by linarith [hcon.1], by linarith [hcon.2]⟩
      have hev : (fun z : (Ent × Ent × Ent) × (ℝ × ℝ × P) =>
          (χ₁ z.2.1 * χ₂ z.2.2.1 * χ₀ (sqSum z.1)) • Φ (combine z.1 (z.2.1, z.2.2.1), z.2.2.2)) =ᶠ[nhds z]
            fun _ => (0 : ℂ) := by
        filter_upwards [hopen.mem_nhds hmem] with w hw
        rcases hw with hw | hw
        · have h0 : χ₁ w.2.1 = 0 := by
            apply χ₁.zero_of_le_dist
            rw [Real.dist_eq, abs_of_nonpos (by linarith)]
            show q₀.1 / 2 ≤ -(w.2.1 - q₀.1)
            linarith
          simp [h0]
        · have h0 : χ₂ w.2.2.1 = 0 := by
            apply χ₂.zero_of_le_dist
            rw [Real.dist_eq, abs_of_nonpos (by linarith)]
            show q₀.2.1 / 2 ≤ -(w.2.2.1 - q₀.2.1)
            linarith
          simp [h0]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  ·
    have hK : IsCompact ((Metric.closedBall (0 : Ent × Ent × Ent) (Real.sqrt (12 * R ^ 2 + 2))) ×ˢ
        (Metric.closedBall q₀.1 (q₀.1 / 2) ×ˢ (Metric.closedBall q₀.2.1 (q₀.2.1 / 2) ×ˢ (Prod.snd '' tsupport Φ)))) :=
      (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
        ((isCompact_closedBall _ _).prod (hcomp.image continuous_snd)))
    refine HasCompactSupport.of_support_subset_isCompact hK ?_
    intro z hz
    rw [Function.mem_support] at hz
    have hsc : χ₁ z.2.1 * χ₂ z.2.2.1 * χ₀ (sqSum z.1) ≠ 0 := left_ne_zero_of_smul hz
    have hΦz : Φ (combine z.1 (z.2.1, z.2.2.1), z.2.2.2) ≠ 0 := right_ne_zero_of_smul hz
    have h₁ : χ₁ z.2.1 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hsc)
    have h₂ : χ₂ z.2.2.1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hsc)
    have h₀ : χ₀ (sqSum z.1) ≠ 0 := right_ne_zero_of_mul hsc
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      have hin : sqSum z.1 ∈ Metric.ball (0 : ℝ) χ₀.rOut := by
        rw [← χ₀.support_eq]
        exact Function.mem_support.mpr h₀
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (sqSum_nonneg _)] at hin
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_le_sqrt_sqSum z.1).trans (Real.sqrt_le_sqrt hin.le)
    · have hin : z.2.1 ∈ Metric.ball q₀.1 χ₁.rOut := by
        rw [← χ₁.support_eq]
        exact Function.mem_support.mpr h₁
      exact Metric.ball_subset_closedBall hin
    · have hin : z.2.2.1 ∈ Metric.ball q₀.2.1 χ₂.rOut := by
        rw [← χ₂.support_eq]
        exact Function.mem_support.mpr h₂
      exact Metric.ball_subset_closedBall hin
    · exact ⟨_, subset_tsupport Φ (Function.mem_support.mpr hΦz), rfl⟩
  ·
    have h₁ : ∀ᶠ q : ℝ × ℝ × P in nhds q₀, χ₁ q.1 = 1 := by
      have := (continuous_fst.tendsto q₀).eventually χ₁.eventuallyEq_one
      filter_upwards [this] with q hq using hq
    have h₂ : ∀ᶠ q : ℝ × ℝ × P in nhds q₀, χ₂ q.2.1 = 1 := by
      have := ((continuous_fst.comp continuous_snd).tendsto q₀).eventually χ₂.eventuallyEq_one
      filter_upwards [this] with q hq using hq
    filter_upwards [h₁, h₂] with q hq₁ hq₂
    rintro ⟨v, b⟩
    show (χ₁ q.1 * χ₂ q.2.1 * χ₀ (sqSum (entryTriple (v, b)))) • Φ (combine (entryTriple (v, b)) (q.1, q.2.1), q.2.2) =
      Φ (combine (entryTriple (v, b)) (q.1, q.2.1), q.2.2)
    rw [hq₁, hq₂, one_mul, one_mul]
    by_cases hΦ0 : Φ (combine (entryTriple (v, b)) (q.1, q.2.1), q.2.2) = 0
    · simp [hΦ0]
    · have hmem : ((combine (entryTriple (v, b)) (q.1, q.2.1), q.2.2) : Ent × P) ∈ tsupport Φ :=
        subset_tsupport Φ (Function.mem_support.mpr hΦ0)
      have hcb : ‖combine (entryTriple (v, b)) (q.1, q.2.1)‖ ≤ B₀ := (norm_fst_le _).trans (hB₀ _ hmem)
      have hv : ‖v‖ ≤ 4 * B₀ := norm_fst_le_of_combine q.1 q.2.1 v b B₀ hcb
      have hT : ‖entryTriple (v, b)‖ ≤ R := by
        refine (norm_entryTriple_le (v, b)).trans ?_
        show 4 * (1 + ‖v‖) ≤ 4 * (1 + 4 * B₀)
        linarith
      have hR : 0 ≤ R := (norm_nonneg _).trans hT
      have hsq : sqSum (entryTriple (v, b)) ≤ 12 * R ^ 2 := by
        refine (sqSum_le _).trans ?_
        have := pow_le_pow_left₀ (norm_nonneg _) hT 2
        linarith
      have h0 : χ₀ (sqSum (entryTriple (v, b))) = 1 := by
        apply χ₀.one_of_mem_closedBall
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (sqSum_nonneg _)]
        show sqSum (entryTriple (v, b)) ≤ 12 * R ^ 2 + 1
        linarith
      simp [h0]

private theorem contDiffAt_of_pos (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (q₀ : ℝ × ℝ × P)
    (hq₀ : 0 < q₀.1 ∧ 0 < q₀.2.1) : ContDiffAt ℝ (⊤ : ℕ∞) (family P Φ) q₀ := by
  obtain ⟨Ψ, hΨ, hΨc, hev⟩ := exists_cutoff P Φ hΦ hΦc q₀ hq₀
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × P => ∫ ω, density ω • Ψ (entryTriple ω, q) ∂domMeasure) :=
    engine domMeasure density entryTriple density_aestronglyMeasurable entryTriple_aestronglyMeasurable slab
      (ℝ × ℝ × P) Ψ hΨ hΨc
  have hpos : ∀ᶠ q in nhds q₀, 0 < q.1 ∧ 0 < q.2.1 := by
    have h1 : ∀ᶠ q : ℝ × ℝ × P in nhds q₀, 0 < q.1 :=
      (continuous_fst.tendsto q₀).eventually (lt_mem_nhds hq₀.1)
    have h2 : ∀ᶠ q : ℝ × ℝ × P in nhds q₀, 0 < q.2.1 :=
      ((continuous_fst.comp continuous_snd).tendsto q₀).eventually (lt_mem_nhds hq₀.2)
    exact h1.and h2
  refine hsmooth.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hev, hpos] with q hq hqpos
  exact family_eq_integral P Φ hΦ.continuous hΦc Ψ hΨ.continuous hΨc q hqpos hq

private theorem family_contDiff (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {x | IsUnit (Matrix.det (Matrix.of x.1))}) : ContDiff ℝ (⊤ : ℕ∞) (family P Φ) := by
  obtain ⟨c, C, K, hc, hK, hvan⟩ := exists_vanishing P Φ hΦ.continuous hΦc hΦU
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases hq₀ : 0 < q₀.1 ∧ 0 < q₀.2.1
  · exact contDiffAt_of_pos P Φ hΦ hΦc q₀ hq₀
  · have hmem : q₀ ∈ {q : ℝ × ℝ × P | q.1 < c ∨ q.2.1 < c ∨ C < q.1 ∨ C < q.2.1 ∨ q.2.2 ∉ K} := by
      rw [not_and_or] at hq₀
      rcases hq₀ with h | h
      · exact Or.inl (lt_of_le_of_lt (not_lt.mp h) hc)
      · exact Or.inr (Or.inl (lt_of_le_of_lt (not_lt.mp h) hc))
    have hzero : family P Φ =ᶠ[nhds q₀] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_vanishingSet c C K hK).mem_nhds hmem] with q hq
      exact hvan q hq
    exact contDiffAt_const.congr_of_eventuallyEq hzero

end Family

namespace UnitaryChart

private def rowElt (z : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z 0, z 1; -(starRingEnd ℂ) (z 1), (starRingEnd ℂ) (z 0)]

private def sq (z : Fin 2 → ℂ) : ℝ :=
  Complex.normSq (z 0) + Complex.normSq (z 1)

private def chartRow (η ξ₁ ξ₂ : ℝ) : Fin 2 → ℂ :=
  ![(Real.cos η : ℂ) * Complex.exp (ξ₁ * Complex.I), (Real.sin η : ℂ) * Complex.exp (ξ₂ * Complex.I)]

private def chartIntegral (G : (Fin 2 → ℂ) → ℂ) : ℂ :=
  ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
    (Real.sin η * Real.cos η : ℂ) * G (chartRow η ξ₁ ξ₂)

private def shellIntegral (G : (Fin 2 → ℂ) → ℂ) : ℂ :=
  ∫ z : Fin 2 → ℂ, Set.indicator (Set.Icc (1 : ℝ) 4) (fun _ => (1 : ℂ)) (sq z) *
    G (((Real.sqrt (sq z))⁻¹ : ℝ) • z)

private def onRow (F : GL (Fin 2) ℂ → ℂ) (c : ℂ) (z : Fin 2 → ℂ) : ℂ :=
  if h : (c • rowElt z).det ≠ 0 then F (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0

private theorem det_rowElt (z : Fin 2 → ℂ) : (rowElt z).det = (sq z : ℝ) := by
  simp only [rowElt, Matrix.det_fin_two_of, sq, Complex.ofReal_add, ← Complex.mul_conj]
  ring

private theorem sq_chartRow (η ξ₁ ξ₂ : ℝ) : sq (chartRow η ξ₁ ξ₂) = 1 := by
  have h₁ : Complex.normSq (Complex.exp (ξ₁ * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  have h₂ : Complex.normSq (Complex.exp (ξ₂ * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  simp only [sq, chartRow, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_mul,
    Complex.normSq_ofReal, h₁, h₂, mul_one]
  nlinarith [Real.cos_sq_add_sin_sq η]

private theorem det_smul_rowElt (c : ℂ) (z : Fin 2 → ℂ) : (c • rowElt z).det = c ^ 2 * (sq z : ℝ) := by
  rw [Matrix.det_smul, det_rowElt, Fintype.card_fin]

private theorem det_smul_rowElt_ne_zero_iff (c : ℂ) (hc : c ≠ 0) (z : Fin 2 → ℂ) :
    (c • rowElt z).det ≠ 0 ↔ sq z ≠ 0 := by
  rw [det_smul_rowElt]
  simp [hc]

private theorem coe_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Complex.exp (ψ * Complex.I) • rowElt (chartRow η ξ₁ ξ₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-Complex.ofReal_sin, -Complex.ofReal_cos, unitaryElt, rowElt, chartRow, ← Complex.exp_conj,
      Complex.conj_ofReal, Complex.conj_I]

private theorem unitaryAverage_eq (F : GL (Fin 2) ℂ → ℂ) :
    unitaryAverage F =
      (1 / (4 * Real.pi ^ 3) : ℂ) *
        ∫ ψ in (0 : ℝ)..(2 * Real.pi), chartIntegral (onRow F (Complex.exp (ψ * Complex.I))) := by
  unfold unitaryAverage chartIntegral
  congr 1
  refine intervalIntegral.integral_congr fun ψ _ => ?_
  refine intervalIntegral.integral_congr fun η _ => ?_
  refine intervalIntegral.integral_congr fun ξ₁ _ => ?_
  refine intervalIntegral.integral_congr fun ξ₂ _ => ?_
  congr 1
  have hdet : (Complex.exp (ψ * Complex.I) • rowElt (chartRow η ξ₁ ξ₂)).det ≠ 0 := by
    rw [det_smul_rowElt_ne_zero_iff _ (Complex.exp_ne_zero _), sq_chartRow]
    exact one_ne_zero
  rw [onRow, dif_pos hdet]
  congr 1
  exact Units.ext (coe_unitaryElt ψ η ξ₁ ξ₂)

private theorem eq_rowElt_of_unitary_of_det (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : star N * N = 1) (hdet : N.det = 1) :
    N = rowElt (N 0) := by
  have hadj : N.adjugate = star N := by
    have h1 : N * N.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
    exact (Matrix.inv_eq_right_inv h1).symm ▸ (Matrix.inv_eq_left_inv hN)
  have h := hadj
  rw [Matrix.adjugate_fin_two, Matrix.star_eq_conjTranspose] at h
  have h00 := congrFun (congrFun h 1) 1
  have h10 := congrFun (congrFun h 0) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.conjTranspose_apply] at h00 h10
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowElt]
  ·
    have := congrArg (starRingEnd ℂ) h10
    simp only [map_neg, Complex.star_def, Complex.conj_conj] at this
    exact this.symm
  ·
    have := congrArg (starRingEnd ℂ) h00
    simp only [Complex.star_def, Complex.conj_conj] at this
    exact this.symm

private theorem exists_eq_smul_rowElt_matrix (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : star M * M = 1) :
    ∃ (β : ℝ) (w : Fin 2 → ℂ), sq w = 1 ∧ M = Complex.exp (β * Complex.I) • rowElt w := by
  have hnorm : ‖M.det‖ = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at h
    have h' : Complex.normSq M.det = 1 := by
      have := h
      rw [Complex.star_def, mul_comm, Complex.mul_conj] at this
      exact_mod_cast this
    rw [Complex.normSq_eq_norm_sq] at h'
    nlinarith [norm_nonneg M.det]
  set θ := Complex.arg M.det with hθ
  have hdetθ : M.det = Complex.exp (θ * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I M.det
    rw [hnorm, Complex.ofReal_one, one_mul] at this
    rw [hθ]
    exact this.symm
  set c : ℂ := Complex.exp ((θ / 2 : ℝ) * Complex.I) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcc : c * c = M.det := by
    rw [hdetθ, hc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcnorm : Complex.normSq c = 1 := by
    rw [hc, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  set N : Matrix (Fin 2) (Fin 2) ℂ := c⁻¹ • M with hNdef
  have hNu : star N * N = 1 := by
    have h1 : (starRingEnd ℂ) c⁻¹ * c⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, mul_comm, Complex.mul_conj, hcnorm]
      simp
    rw [hNdef, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM, Complex.star_def, h1, one_smul]
  have hNdet : N.det = 1 := by
    rw [hNdef, Matrix.det_smul, Fintype.card_fin, ← hcc]
    field_simp
  have hNrow : N = rowElt (N 0) := eq_rowElt_of_unitary_of_det N hNu hNdet
  refine ⟨θ / 2, N 0, ?_, ?_⟩
  · have h := hNdet
    rw [hNrow, det_rowElt] at h
    exact_mod_cast h
  · rw [← hNrow, hNdef, smul_smul, mul_inv_cancel₀ hc0, one_smul]

private theorem exists_eq_smul_rowElt_of_unitary (k : GL (Fin 2) ℂ)
    (hk : star (k : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    ∃ (β : ℝ) (w : Fin 2 → ℂ), sq w = 1 ∧
      (k : Matrix (Fin 2) (Fin 2) ℂ) = Complex.exp (β * Complex.I) • rowElt w :=
  exists_eq_smul_rowElt_matrix _ hk

private theorem rowElt_mul_rowElt (z w : Fin 2 → ℂ) :
    rowElt z * rowElt w = rowElt (Matrix.vecMul z (rowElt w)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowElt, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_add, map_mul, map_neg]
  ring

private def rightMap (w : Fin 2 → ℂ) : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) :=
  ((rowElt w).vecMulLinear).restrictScalars ℝ

private def flipComponent : Fin 2 → (ℂ →ₗ[ℝ] ℂ) :=
  ![LinearMap.id, -Complex.conjAe.toLinearMap]

private def flipMap : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) :=
  LinearMap.pi fun i => (flipComponent i).comp (LinearMap.proj i)

private def leftMap (w : Fin 2 → ℂ) : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) :=
  flipMap.comp ((rightMap (flipMap w)).comp flipMap)

private theorem rightMap_apply (w z : Fin 2 → ℂ) : rightMap w z = Matrix.vecMul z (rowElt w) := by
  simp [rightMap]

private theorem flipMap_apply (z : Fin 2 → ℂ) : flipMap z = ![z 0, -(starRingEnd ℂ) (z 1)] := by
  ext i
  fin_cases i <;> simp [flipMap, flipComponent]

private theorem rowElt_mul_rowElt' (w z : Fin 2 → ℂ) : rowElt w * rowElt z = rowElt (leftMap w z) := by
  simp only [leftMap, LinearMap.comp_apply, rightMap_apply, flipMap_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowElt, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_add, map_mul, map_neg] <;>
    ring

private theorem det_rightMap (w : Fin 2 → ℂ) (hw : sq w = 1) : LinearMap.det (rightMap w) = 1 := by
  have hdet : LinearMap.det (rowElt w).vecMulLinear = 1 := by
    rw [← Matrix.transpose_transpose (rowElt w), Matrix.vecMulLinear_transpose, ← Matrix.toLin'_apply',
      LinearMap.det_toLin', Matrix.det_transpose, det_rowElt, hw, Complex.ofReal_one]
  rw [rightMap, LinearMap.det_restrictScalars, hdet, map_one]

private theorem flipMap_comp_flipMap : flipMap.comp flipMap = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply, flipMap_apply, flipMap_apply, LinearMap.id_apply]
  ext i
  fin_cases i <;> simp

private theorem det_leftMap (w : Fin 2 → ℂ) (hw : sq w = 1) : LinearMap.det (leftMap w) = 1 := by
  have hw' : sq (flipMap w) = 1 := by
    simpa [sq, flipMap_apply, Complex.normSq_conj] using hw
  have hff : LinearMap.det flipMap * LinearMap.det flipMap = 1 := by
    rw [← LinearMap.det_comp, flipMap_comp_flipMap, LinearMap.det_id]
  rw [leftMap, LinearMap.det_comp, LinearMap.det_comp, det_rightMap _ hw', one_mul]
  exact hff

private theorem sq_rightMap (w : Fin 2 → ℂ) (hw : sq w = 1) (z : Fin 2 → ℂ) : sq (rightMap w z) = sq z := by
  have h := congrArg Matrix.det (rowElt_mul_rowElt z w)
  rw [Matrix.det_mul, det_rowElt, det_rowElt, det_rowElt, hw, Complex.ofReal_one, mul_one] at h
  rw [rightMap_apply]
  exact_mod_cast h.symm

private theorem sq_leftMap (w : Fin 2 → ℂ) (hw : sq w = 1) (z : Fin 2 → ℂ) : sq (leftMap w z) = sq z := by
  have h := congrArg Matrix.det (rowElt_mul_rowElt' w z)
  rw [Matrix.det_mul, det_rowElt, det_rowElt, det_rowElt, hw, Complex.ofReal_one, one_mul] at h
  exact_mod_cast h.symm

private theorem continuousOn_onRow (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F) (c : ℂ) (hc : c ≠ 0) :
    ContinuousOn (onRow F c) {z | sq z ≠ 0} := by
  have hrow : Continuous rowElt := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [rowElt, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact (Complex.continuous_conj.comp (continuous_apply 1)).neg
    · exact Complex.continuous_conj.comp (continuous_apply 0)
  rw [continuousOn_iff_continuous_restrict]
  have hdet : ∀ z : {z : Fin 2 → ℂ // sq z ≠ 0}, (c • rowElt z.1).det ≠ 0 :=
    fun z => (det_smul_rowElt_ne_zero_iff c hc z.1).2 z.2
  set g : {z : Fin 2 → ℂ // sq z ≠ 0} → GL (Fin 2) ℂ :=
    fun z => Matrix.GeneralLinearGroup.mkOfDetNeZero (c • rowElt z.1) (hdet z) with hg
  have hval : Continuous fun z : {z : Fin 2 → ℂ // sq z ≠ 0} => (c • rowElt z.1) :=
    (hrow.comp continuous_subtype_val).const_smul c
  have hdetc : Continuous fun z : {z : Fin 2 → ℂ // sq z ≠ 0} => (c • rowElt z.1).det :=
    hval.matrix_det
  have hg_cont : Continuous g := by
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    have : (fun z : {z : Fin 2 → ℂ // sq z ≠ 0} => ((g z)⁻¹ : GL (Fin 2) ℂ).val) =
        fun z => Ring.inverse (c • rowElt z.1).det • (c • rowElt z.1).adjugate := by
      funext z
      rw [Matrix.coe_units_inv, Matrix.inv_def]
      rfl
    rw [this]
    refine Continuous.fun_smul ?_ hval.matrix_adjugate
    have : (fun z : {z : Fin 2 → ℂ // sq z ≠ 0} => Ring.inverse (c • rowElt z.1).det) =
        fun z => ((c • rowElt z.1).det)⁻¹ := by
      funext z
      exact congrFun Ring.inverse_eq_inv' _
    rw [this]
    exact hdetc.inv₀ hdet
  have hres : Set.domRestrict {z : Fin 2 → ℂ | sq z ≠ 0} (onRow F c) = F ∘ g := by
    funext z
    simp only [Set.domRestrict_apply, Function.comp_apply, hg, onRow, dif_pos (hdet z)]
  rw [hres]
  exact hF.comp hg_cont

private def shellFn (G : (Fin 2 → ℂ) → ℂ) (z : Fin 2 → ℂ) : ℂ :=
  Set.indicator (Set.Icc (1 : ℝ) 4) (fun _ => (1 : ℂ)) (sq z) * G (((Real.sqrt (sq z))⁻¹ : ℝ) • z)

private theorem shellIntegral_eq_integral (G : (Fin 2 → ℂ) → ℂ) :
    shellIntegral G = ∫ z, shellFn G z :=
  rfl

private def polarFn (G : (Fin 2 → ℂ) → ℂ) (p : Fin 2 → ℝ × ℝ) : ℂ :=
  (Set.univ.pi fun _ : Fin 2 => Complex.polarCoord.target).indicator
    (fun q => (∏ i, (q i).1) • shellFn G (fun i => Complex.polarCoord.symm (q i))) p

private theorem shellIntegral_eq_integral_polarFn (G : (Fin 2 → ℂ) → ℂ) :
    shellIntegral G = ∫ p, polarFn G p := by
  rw [shellIntegral_eq_integral, ← Complex.integral_comp_pi_polarCoord_symm,
    ← integral_indicator (MeasurableSet.univ_pi fun _ => Complex.polarCoord.open_target.measurableSet)]
  rfl

private def quad : (Fin 2 → ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2)).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow)

private theorem volume_preserving_quad : MeasurePreserving quad :=
  (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 2)).trans
    ((volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ))

private theorem quad_symm_apply (a θ : ℝ × ℝ) :
    quad.symm (a, θ) = fun i => ((![a.1, a.2] : Fin 2 → ℝ) i, (![θ.1, θ.2] : Fin 2 → ℝ) i) :=
  rfl

private theorem integral_polarFn_eq (G : (Fin 2 → ℂ) → ℂ) :
    ∫ p, polarFn G p = ∫ q, polarFn G (quad.symm q) :=
  (volume_preserving_quad.symm.integral_comp' (polarFn G)).symm

private theorem integral_comp_polarCoord_symm_fst (f : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) :
    (∫ p in polarCoord.target ×ˢ (Set.univ : Set (ℝ × ℝ)), p.1.1 • f (polarCoord.symm p.1, p.2)) =
      ∫ p, f p := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hs : MeasurableSet (polarCoord.target ×ˢ (Set.univ : Set (ℝ × ℝ))) :=
    polarCoord.open_target.measurableSet.prod MeasurableSet.univ
  have hderiv : ∀ p ∈ polarCoord.target ×ˢ (Set.univ : Set (ℝ × ℝ)),
      HasFDerivWithinAt (Prod.map polarCoord.symm id)
        ((fderivPolarCoordSymm p.1).prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ)))
        (polarCoord.target ×ˢ (Set.univ : Set (ℝ × ℝ))) p :=
    fun p _ => ((hasFDerivAt_polarCoord_symm p.1).prodMap p (hasFDerivAt_id p.2)).hasFDerivWithinAt
  have hinj : Set.InjOn (Prod.map polarCoord.symm id) (polarCoord.target ×ˢ (Set.univ : Set (ℝ × ℝ))) :=
    polarCoord.symm.injOn.prodMap (Set.injOn_id _)
  have hdet : ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
      ((fderivPolarCoordSymm p.1).prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ))).det = p.1.1 := by
    intro p
    have h : ((fderivPolarCoordSymm p.1).prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ))).toLinearMap =
        (fderivPolarCoordSymm p.1).toLinearMap.prodMap LinearMap.id := rfl
    rw [ContinuousLinearMap.det, h, LinearMap.det_prodMap, LinearMap.det_id, mul_one,
      ← ContinuousLinearMap.det, det_fderivPolarCoordSymm]
  have himage : Prod.map polarCoord.symm id '' (polarCoord.target ×ˢ (Set.univ : Set (ℝ × ℝ))) =ᵐ[volume]
      (Set.univ : Set ((ℝ × ℝ) × (ℝ × ℝ))) := by
    rw [Set.prodMap_image_prod, Set.image_id, polarCoord.symm_image_target_eq_source,
      ← @Set.univ_prod_univ (ℝ × ℝ) (ℝ × ℝ), Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq polarCoord_source_ae_eq_univ Filter.EventuallyEq.rfl
  rw [← setIntegral_univ (f := f), ← setIntegral_congr_set himage,
    integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv hinj f]
  refine setIntegral_congr_fun hs fun p hp => ?_
  rw [hdet, abs_of_pos hp.1.1]
  rfl

private theorem sq_polar (u v : Fin 2 → ℝ) :
    sq (fun i => Complex.polarCoord.symm (u i, v i)) = u 0 ^ 2 + u 1 ^ 2 := by
  simp only [sq, Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, sq_abs]

private theorem smul_polar (c : ℝ) (u v : Fin 2 → ℝ) :
    (c • fun i => Complex.polarCoord.symm (u i, v i)) = fun i => Complex.polarCoord.symm (c * u i, v i) := by
  funext i
  simp only [Pi.smul_apply, Complex.polarCoord_symm_apply, Complex.real_smul, Complex.ofReal_mul, mul_assoc]

private theorem chartRow_eq (η ξ₁ ξ₂ : ℝ) :
    chartRow η ξ₁ ξ₂ =
      ![Complex.polarCoord.symm (Real.cos η, ξ₁), Complex.polarCoord.symm (Real.sin η, ξ₂)] := by
  simp only [chartRow, Complex.polarCoord_symm_apply, Complex.exp_mul_I, Complex.ofReal_cos,
    Complex.ofReal_sin]

private theorem sq_chartRow_eq_one (η ξ₁ ξ₂ : ℝ) : sq (chartRow η ξ₁ ξ₂) = 1 := by
  rw [chartRow_eq]
  simp only [sq, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_eq_norm_sq,
    Complex.norm_polarCoord_symm, sq_abs, Real.cos_sq_add_sin_sq]

private theorem chartRow_add_two_pi_left (η ξ₁ ξ₂ : ℝ) :
    chartRow η (ξ₁ + 2 * Real.pi) ξ₂ = chartRow η ξ₁ ξ₂ := by
  have h : Complex.exp (↑(ξ₁ + 2 * Real.pi) * Complex.I) = Complex.exp (↑ξ₁ * Complex.I) := by
    push_cast
    exact Complex.exp_mul_I_periodic _
  simp only [chartRow, h]

private theorem chartRow_add_two_pi_right (η ξ₁ ξ₂ : ℝ) :
    chartRow η ξ₁ (ξ₂ + 2 * Real.pi) = chartRow η ξ₁ ξ₂ := by
  have h : Complex.exp (↑(ξ₂ + 2 * Real.pi) * Complex.I) = Complex.exp (↑ξ₂ * Complex.I) := by
    push_cast
    exact Complex.exp_mul_I_periodic _
  simp only [chartRow, h]

private theorem quadrant_iff {ρ η : ℝ} (hρ : 0 < ρ) (hη : η ∈ Set.Ioo (-Real.pi) Real.pi) :
    (0 < ρ * Real.cos η ∧ 0 < ρ * Real.sin η) ↔ η ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [mul_pos_iff_of_pos_left hρ, mul_pos_iff_of_pos_left hρ]
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨?_, ?_⟩
    · by_contra h
      have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (not_lt.1 h) hη.1.le
      linarith
    · by_contra h
      have := Real.cos_nonpos_of_pi_div_two_le_of_le (not_lt.1 h) (by linarith [hη.2, Real.pi_pos])
      linarith
  · rintro ⟨h0, h2⟩
    exact ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩,
      Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])⟩

private def radFn (ρ : ℝ) : ℂ :=
  ((Set.indicator (Set.Icc (1 : ℝ) 2) (fun r => r ^ 3) ρ : ℝ) : ℂ)

private theorem integral_radFn : ∫ ρ, radFn ρ = ((∫ ρ in (1 : ℝ)..2, ρ ^ 3 : ℝ) : ℂ) := by
  unfold radFn
  rw [integral_complex_ofReal, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]

private theorem radConst_pos : 0 < ∫ ρ in (1 : ℝ)..2, ρ ^ 3 :=
  intervalIntegral.intervalIntegral_pos_of_pos_on ((continuous_pow 3).intervalIntegrable 1 2)
    (fun ρ hρ => pow_pos (by linarith [hρ.1]) 3) (by norm_num)

private def angBox : Set (ℝ × (ℝ × ℝ)) :=
  Set.Ioo 0 (Real.pi / 2) ×ˢ (Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi)

private theorem measurableSet_angBox : MeasurableSet angBox :=
  measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)

private def angFn (G : (Fin 2 → ℂ) → ℂ) (v : ℝ × (ℝ × ℝ)) : ℂ :=
  (Real.sin v.1 * Real.cos v.1 : ℂ) * G (chartRow v.1 v.2.1 v.2.2)

private theorem polarFn_point (G : (Fin 2 → ℂ) → ℂ) {ρ η : ℝ} (hρ : 0 < ρ)
    (hη : η ∈ Set.Ioo (-Real.pi) Real.pi) (θ : ℝ × ℝ) :
    ρ • polarFn G (quad.symm (polarCoord.symm (ρ, η), θ)) = radFn ρ * angBox.indicator (angFn G) (η, θ) := by
  have hpt : quad.symm (polarCoord.symm (ρ, η), θ) =
      fun i => ((![ρ * Real.cos η, ρ * Real.sin η] : Fin 2 → ℝ) i, (![θ.1, θ.2] : Fin 2 → ℝ) i) := by
    rw [quad_symm_apply]
    rfl
  have hmem : ((fun i => ((![ρ * Real.cos η, ρ * Real.sin η] : Fin 2 → ℝ) i, (![θ.1, θ.2] : Fin 2 → ℝ) i)) ∈
      Set.univ.pi fun _ : Fin 2 => Complex.polarCoord.target) ↔ (η, θ) ∈ angBox := by
    rw [Set.mem_univ_pi, Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.polarCoord_target, angBox,
      Set.mem_prod, Set.mem_Ioi, ← quadrant_iff hρ hη]
    tauto
  have hsq : sq (fun i => Complex.polarCoord.symm
      (((![ρ * Real.cos η, ρ * Real.sin η] : Fin 2 → ℝ) i), ((![θ.1, θ.2] : Fin 2 → ℝ) i))) = ρ ^ 2 := by
    rw [sq_polar]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination ρ ^ 2 * Real.cos_sq_add_sin_sq η
  have hrow : (ρ⁻¹ • fun i => Complex.polarCoord.symm
      (((![ρ * Real.cos η, ρ * Real.sin η] : Fin 2 → ℝ) i), ((![θ.1, θ.2] : Fin 2 → ℝ) i))) =
      chartRow η θ.1 θ.2 := by
    rw [smul_polar, chartRow_eq]
    funext i
    fin_cases i <;> simp [hρ.ne']
  rw [hpt]
  unfold polarFn
  by_cases hbox : (η, θ) ∈ angBox
  · rw [Set.indicator_of_mem (hmem.2 hbox), Set.indicator_of_mem hbox]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [shellFn]
    rw [hsq, Real.sqrt_sq hρ.le, hrow]
    simp only [radFn, angFn]
    by_cases hρ' : ρ ∈ Set.Icc (1 : ℝ) 2
    · have hρ2 : ρ ^ 2 ∈ Set.Icc (1 : ℝ) 4 := ⟨by nlinarith [hρ'.1, hρ'.2], by nlinarith [hρ'.1, hρ'.2]⟩
      rw [Set.indicator_of_mem hρ2, Set.indicator_of_mem hρ']
      simp only [Complex.real_smul]
      push_cast
      ring
    · have hρ2 : ρ ^ 2 ∉ Set.Icc (1 : ℝ) 4 := fun h =>
        hρ' ⟨by nlinarith [h.1, h.2, hρ], by nlinarith [h.1, h.2, hρ]⟩
      rw [Set.indicator_of_notMem hρ2, Set.indicator_of_notMem hρ']
      simp
  · have hS := fun h => hbox (hmem.1 h)
    rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hbox, smul_zero, mul_zero]

private theorem continuous_angFn (G : (Fin 2 → ℂ) → ℂ) (hG : ContinuousOn G {z | sq z ≠ 0}) :
    Continuous (angFn G) := by
  have hr : Continuous fun v : ℝ × (ℝ × ℝ) => chartRow v.1 v.2.1 v.2.2 := by
    unfold chartRow
    fun_prop
  have hc : Continuous fun v : ℝ × (ℝ × ℝ) => G (chartRow v.1 v.2.1 v.2.2) :=
    hG.comp_continuous hr fun v => by simp [sq_chartRow_eq_one]
  have hs : Continuous fun v : ℝ × (ℝ × ℝ) => (Real.sin v.1 * Real.cos v.1 : ℂ) := by
    fun_prop
  exact hs.mul hc

private theorem integral_angBox (G : (Fin 2 → ℂ) → ℂ) (hG : ContinuousOn G {z | sq z ≠ 0}) :
    ∫ v in angBox, angFn G v =
      ∫ η in Set.Ioo 0 (Real.pi / 2), ∫ θ₀ in Set.Ioo (-Real.pi) Real.pi, ∫ θ₁ in Set.Ioo (-Real.pi) Real.pi,
        angFn G (η, (θ₀, θ₁)) := by
  have hc := continuous_angFn G hG
  haveI : Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hK : IsCompact (Set.Icc 0 (Real.pi / 2) ×ˢ (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hsub : angBox ⊆ Set.Icc 0 (Real.pi / 2) ×ˢ (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi) :=
    Set.prod_mono Set.Ioo_subset_Icc_self (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
  have h1 : IntegrableOn (angFn G) angBox ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) :=
    (hc.continuousOn.integrableOn_compact hK).mono_set hsub
  rw [Measure.volume_eq_prod, angBox, setIntegral_prod _ h1]
  refine setIntegral_congr_fun measurableSet_Ioo fun η _ => ?_
  have hK' : IsCompact (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hsub' : Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆
      Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi :=
    Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  have h2 : IntegrableOn (fun θ : ℝ × ℝ => angFn G (η, θ)) (Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    ((hc.comp (Continuous.prodMk_right η)).continuousOn.integrableOn_compact hK').mono_set hsub'
  show ∫ θ in Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioo (-Real.pi) Real.pi, angFn G (η, θ) = _
  rw [Measure.volume_eq_prod, setIntegral_prod _ h2]

private theorem setIntegral_Ioo_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ) :
    ∫ x in Set.Ioo a b, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

private theorem intervalIntegral_two_pi_shift {f : ℝ → ℂ} (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ x in (-Real.pi)..Real.pi, f x = ∫ x in (0 : ℝ)..2 * Real.pi, f x := by
  have h := hf.intervalIntegral_add_eq (-Real.pi) 0
  rwa [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h

private theorem angFn_periodic_inner (G : (Fin 2 → ℂ) → ℂ) (η θ₀ : ℝ) :
    Function.Periodic (fun θ₁ => angFn G (η, (θ₀, θ₁))) (2 * Real.pi) := fun θ₁ => by
  simp only [angFn, chartRow_add_two_pi_right]

private theorem angFn_periodic_outer (G : (Fin 2 → ℂ) → ℂ) (η : ℝ) :
    Function.Periodic (fun θ₀ => ∫ θ₁ in (0 : ℝ)..2 * Real.pi, angFn G (η, (θ₀, θ₁))) (2 * Real.pi) :=
  fun θ₀ => by
  simp only [angFn, chartRow_add_two_pi_left]

private theorem exists_shellIntegral_eq :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ G : (Fin 2 → ℂ) → ℂ, ContinuousOn G {z | sq z ≠ 0} →
      shellIntegral G = C * chartIntegral G := by
  refine ⟨((∫ ρ in (1 : ℝ)..2, ρ ^ 3 : ℝ) : ℂ), Complex.ofReal_ne_zero.2 radConst_pos.ne', ?_⟩
  intro G hG
  have hππ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  calc shellIntegral G
      = ∫ p, polarFn G p := shellIntegral_eq_integral_polarFn G
    _ = ∫ q, polarFn G (quad.symm q) := integral_polarFn_eq G
    _ = ∫ p in polarCoord.target ×ˢ (Set.univ : Set (ℝ × ℝ)),
          p.1.1 • polarFn G (quad.symm (polarCoord.symm p.1, p.2)) :=
        (integral_comp_polarCoord_symm_fst fun q => polarFn G (quad.symm q)).symm
    _ = ∫ p in polarCoord.target ×ˢ (Set.univ : Set (ℝ × ℝ)),
          radFn p.1.1 * angBox.indicator (angFn G) (p.1.2, p.2) := by
        refine setIntegral_congr_fun (polarCoord.open_target.measurableSet.prod MeasurableSet.univ) ?_
        rintro ⟨⟨ρ, η⟩, θ⟩ ⟨⟨hρ, hη⟩, -⟩
        exact polarFn_point G hρ hη θ
    _ = ∫ p : (ℝ × ℝ) × (ℝ × ℝ), radFn p.1.1 * angBox.indicator (angFn G) (p.1.2, p.2) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
        by_cases hρ : 0 < p.1.1
        · have hη : p.1.2 ∉ Set.Ioo (-Real.pi) Real.pi := fun hη => hp ⟨⟨hρ, hη⟩, Set.mem_univ _⟩
          have hbox : (p.1.2, p.2) ∉ angBox := by
            intro h
            have h' : p.1.2 ∈ Set.Ioo 0 (Real.pi / 2) := h.1
            exact hη ⟨by linarith [h'.1, Real.pi_pos], by linarith [h'.2, Real.pi_pos]⟩
          rw [Set.indicator_of_notMem hbox, mul_zero]
        · have h1 : p.1.1 ∉ Set.Icc (1 : ℝ) 2 := fun h => hρ (by linarith [h.1])
          simp [radFn, Set.indicator_of_notMem h1]
    _ = ∫ u : ℝ × (ℝ × (ℝ × ℝ)), radFn u.1 * angBox.indicator (angFn G) u.2 := by
        rw [← (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ × ℝ)).integral_comp']
        rfl
    _ = (∫ ρ, radFn ρ) * ∫ v, angBox.indicator (angFn G) v := by
        rw [Measure.volume_eq_prod]
        exact integral_prod_mul radFn (angBox.indicator (angFn G))
    _ = ((∫ ρ in (1 : ℝ)..2, ρ ^ 3 : ℝ) : ℂ) * ∫ v in angBox, angFn G v := by
        rw [integral_radFn, integral_indicator measurableSet_angBox]
    _ = ((∫ ρ in (1 : ℝ)..2, ρ ^ 3 : ℝ) : ℂ) *
          ∫ η in (0 : ℝ)..Real.pi / 2, ∫ θ₀ in (0 : ℝ)..2 * Real.pi, ∫ θ₁ in (0 : ℝ)..2 * Real.pi,
            angFn G (η, (θ₀, θ₁)) := by
        rw [integral_angBox G hG]
        simp only [setIntegral_Ioo_eq_intervalIntegral hππ, setIntegral_Ioo_eq_intervalIntegral hπ2,
          intervalIntegral_two_pi_shift (angFn_periodic_inner G _ _),
          intervalIntegral_two_pi_shift (angFn_periodic_outer G _)]
    _ = ((∫ ρ in (1 : ℝ)..2, ρ ^ 3 : ℝ) : ℂ) * chartIntegral G := rfl

private theorem shellIntegral_comp (Λ : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ))
    (hdet : LinearMap.det Λ = 1 ∨ LinearMap.det Λ = -1) (hsq : ∀ z, sq (Λ z) = sq z)
    (G : (Fin 2 → ℂ) → ℂ) (hG : ContinuousOn G {z | sq z ≠ 0}) :
    shellIntegral (fun z => G (Λ z)) = shellIntegral G := by
  have _ := hG
  have hdet0 : LinearMap.det Λ ≠ 0 := by
    rcases hdet with h | h <;> norm_num [h]
  have habs : |(LinearMap.det Λ)⁻¹| = 1 := by
    rcases hdet with h | h <;> norm_num [h]
  have hmp : MeasurePreserving Λ volume volume := by
    refine ⟨Λ.continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0, habs, ENNReal.ofReal_one, one_smul]
  have hemb : MeasurableEmbedding Λ :=
    (LinearMap.equivOfDetNeZero Λ hdet0).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  rw [shellIntegral_eq_integral, shellIntegral_eq_integral, ← hmp.integral_comp hemb (shellFn G)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [shellFn, hsq, LinearMap.map_smul]

private theorem chartIntegral_comp (Λ : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ))
    (hdet : LinearMap.det Λ = 1 ∨ LinearMap.det Λ = -1) (hsq : ∀ z, sq (Λ z) = sq z)
    (G : (Fin 2 → ℂ) → ℂ) (hG : ContinuousOn G {z | sq z ≠ 0}) :
    chartIntegral (fun z => G (Λ z)) = chartIntegral G := by
  obtain ⟨C, hC, hshell⟩ := exists_shellIntegral_eq
  have hGΛ : ContinuousOn (fun z => G (Λ z)) {z | sq z ≠ 0} := by
    refine hG.comp Λ.continuous_of_finiteDimensional.continuousOn ?_
    intro z hz
    simpa [Set.mem_setOf_eq, hsq] using hz
  have h1 := hshell _ hGΛ
  have h2 := hshell G hG
  rw [shellIntegral_comp Λ hdet hsq G hG, h2] at h1
  exact (mul_left_cancel₀ hC h1).symm

private theorem onRow_translate (F : GL (Fin 2) ℂ → ℂ) (k₀ k₁ : GL (Fin 2) ℂ) (α β : ℝ) (w₀ w₁ : Fin 2 → ℂ)
    (h₀ : (k₀ : Matrix (Fin 2) (Fin 2) ℂ) = Complex.exp (α * Complex.I) • rowElt w₀)
    (h₁ : (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = Complex.exp (β * Complex.I) • rowElt w₁)
    (hw₀ : sq w₀ = 1) (hw₁ : sq w₁ = 1) (ψ : ℝ) (z : Fin 2 → ℂ) :
    onRow (fun k => F (k₀ * k * k₁)) (Complex.exp (ψ * Complex.I)) z =
      onRow F (Complex.exp ((ψ + (α + β : ℝ)) * Complex.I)) (rightMap w₁ (leftMap w₀ z)) := by
  have hsq : sq (rightMap w₁ (leftMap w₀ z)) = sq z := by rw [sq_rightMap w₁ hw₁, sq_leftMap w₀ hw₀]
  by_cases hz : sq z = 0
  · have hA : ¬ (Complex.exp (ψ * Complex.I) • rowElt z).det ≠ 0 := by
      rw [det_smul_rowElt_ne_zero_iff _ (Complex.exp_ne_zero _)]; exact not_not.mpr hz
    have hB : ¬ (Complex.exp ((ψ + (α + β : ℝ)) * Complex.I) • rowElt (rightMap w₁ (leftMap w₀ z))).det ≠ 0 := by
      rw [det_smul_rowElt_ne_zero_iff _ (Complex.exp_ne_zero _), hsq]; exact not_not.mpr hz
    simp only [onRow, dif_neg hA, dif_neg hB]
  · have hA : (Complex.exp (ψ * Complex.I) • rowElt z).det ≠ 0 := by
      rw [det_smul_rowElt_ne_zero_iff _ (Complex.exp_ne_zero _)]; exact hz
    have hB : (Complex.exp ((ψ + (α + β : ℝ)) * Complex.I) • rowElt (rightMap w₁ (leftMap w₀ z))).det ≠ 0 := by
      rw [det_smul_rowElt_ne_zero_iff _ (Complex.exp_ne_zero _), hsq]; exact hz
    simp only [onRow, dif_pos hA, dif_pos hB]
    congr 1
    apply Units.ext
    change (k₀ : Matrix (Fin 2) (Fin 2) ℂ) * (Complex.exp (ψ * Complex.I) • rowElt z) *
        (k₁ : Matrix (Fin 2) (Fin 2) ℂ) =
      Complex.exp ((ψ + (α + β : ℝ)) * Complex.I) • rowElt (rightMap w₁ (leftMap w₀ z))
    rw [h₀, h₁, rightMap_apply, ← rowElt_mul_rowElt, ← rowElt_mul_rowElt', Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring

private theorem integral_shift (F : GL (Fin 2) ℂ → ℂ) (t : ℝ) :
    (∫ ψ in (0 : ℝ)..(2 * Real.pi), chartIntegral (onRow F (Complex.exp ((ψ + t) * Complex.I)))) =
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), chartIntegral (onRow F (Complex.exp (ψ * Complex.I))) := by
  set h : ℝ → ℂ := fun ψ => chartIntegral (onRow F (Complex.exp (ψ * Complex.I))) with hh
  have hper : Function.Periodic h (2 * Real.pi) := by
    intro ψ
    simp only [hh, Complex.ofReal_add, add_mul, Complex.exp_add]
    congr 3
    push_cast
    rw [Complex.exp_two_pi_mul_I, mul_one]
  have hL : (∫ ψ in (0 : ℝ)..(2 * Real.pi), chartIntegral (onRow F (Complex.exp ((ψ + t) * Complex.I)))) =
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), h (ψ + t) := by
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    simp only [hh, Complex.ofReal_add]
  rw [hL, intervalIntegral.integral_comp_add_right h t, zero_add]
  have := hper.intervalIntegral_add_eq t 0
  rw [zero_add] at this
  rw [add_comm] at this
  exact this

end UnitaryChart

section Symmetry

open UnitaryChart in

private theorem unitaryAverage_translate (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F)
    (k₀ k₁ : GL (Fin 2) ℂ)
    (h₀ : star (k₀ : Matrix (Fin 2) (Fin 2) ℂ) * (k₀ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (h₁ : star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    unitaryAverage (fun k => F (k₀ * k * k₁)) = unitaryAverage F := by
  obtain ⟨α, w₀, hw₀, hk₀⟩ := exists_eq_smul_rowElt_of_unitary k₀ h₀
  obtain ⟨β, w₁, hw₁, hk₁⟩ := exists_eq_smul_rowElt_of_unitary k₁ h₁
  rw [unitaryAverage_eq, unitaryAverage_eq F]
  congr 1
  rw [← integral_shift F (α + β)]
  refine intervalIntegral.integral_congr fun ψ _ => ?_
  have hexp : Complex.exp ((ψ + (α + β : ℝ)) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hcont := continuousOn_onRow F hF _ hexp
  calc chartIntegral (onRow (fun k => F (k₀ * k * k₁)) (Complex.exp (ψ * Complex.I)))
      = chartIntegral (fun z =>
          onRow F (Complex.exp ((ψ + (α + β : ℝ)) * Complex.I)) (rightMap w₁ (leftMap w₀ z))) := by
        unfold chartIntegral
        simp only [onRow_translate F k₀ k₁ α β w₀ w₁ hk₀ hk₁ hw₀ hw₁]
    _ = chartIntegral (fun z => onRow F (Complex.exp ((ψ + (α + β : ℝ)) * Complex.I)) (rightMap w₁ z)) :=
        chartIntegral_comp (leftMap w₀) (Or.inl (det_leftMap w₀ hw₀)) (sq_leftMap w₀ hw₀) _
          (hcont.comp (rightMap w₁).continuous_of_finiteDimensional.continuousOn
            (fun z hz => by simpa [Set.mem_setOf_eq, sq_rightMap w₁ hw₁] using hz))
    _ = chartIntegral (onRow F (Complex.exp ((ψ + (α + β : ℝ)) * Complex.I))) :=
        chartIntegral_comp (rightMap w₁) (Or.inl (det_rightMap w₁ hw₁)) (sq_rightMap w₁ hw₁) _ hcont

private theorem unitaryAverage_mul_left (G : GL (Fin 2) ℂ → ℂ) (hG : Continuous G) (V : GL (Fin 2) ℂ)
    (hV : star (V : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    unitaryAverage (fun k => G (V * k)) = unitaryAverage G := by
  have h := unitaryAverage_translate G hG V 1 hV (by simp)
  simpa only [mul_one] using h

private theorem conjEntries_mul (g k : GL (Fin 2) ℂ) : conjEntries (g * k) = conjEntries g * conjEntries k :=
  map_mul (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) g k

private def certScale (c : ℂ) : ℂ :=
  (((Real.sqrt (1 + Complex.normSq c)) : ℝ) : ℂ)⁻¹

private theorem conj_certScale (c : ℂ) : (starRingEnd ℂ) (certScale c) = certScale c := by
  simp [certScale, Complex.conj_ofReal]

private theorem certScale_key (c : ℂ) : certScale c * certScale c * (1 + (starRingEnd ℂ) c * c) = 1 := by
  have h0 : (0 : ℝ) ≤ 1 + Complex.normSq c := add_nonneg zero_le_one (Complex.normSq_nonneg c)
  have hpos : (0 : ℝ) < 1 + Complex.normSq c := add_pos_of_pos_of_nonneg one_pos (Complex.normSq_nonneg c)
  have hs : (((Real.sqrt (1 + Complex.normSq c)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have hsq : (((Real.sqrt (1 + Complex.normSq c)) : ℝ) : ℂ) * ((Real.sqrt (1 + Complex.normSq c) : ℝ) : ℂ) =
      1 + (starRingEnd ℂ) c * c := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
    push_cast [Complex.normSq_eq_conj_mul_self]
    ring
  rw [certScale, ← hsq, ← mul_inv, inv_mul_cancel₀ (mul_ne_zero hs hs)]

private def certMatrix (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![certScale c * (starRingEnd ℂ) c, -certScale c; certScale c, certScale c * c]

private theorem certMatrix_det (c : ℂ) : (certMatrix c).det = 1 := by
  rw [certMatrix, Matrix.det_fin_two_of]
  linear_combination certScale_key c

private theorem certMatrix_det_ne_zero (c : ℂ) : (certMatrix c).det ≠ 0 := by
  rw [certMatrix_det]
  exact one_ne_zero

private theorem certMatrix_unitary (c : ℂ) : star (certMatrix c) * certMatrix c = 1 := by
  have key := certScale_key c
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [certMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      conj_certScale]
  all_goals first | ring1 | linear_combination key

private theorem cert_identity (s₁ s₂ : ℂ) (v c : ℂ) (hc : c * s₁ - (starRingEnd ℂ) c * s₂ = -v) :
    !![s₁, v; 0, s₂] * (certMatrix c).map (starRingEnd ℂ) = certMatrix c * !![s₂, v; 0, s₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [certMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, conj_certScale]
  all_goals first | ring1 | linear_combination (certScale c) * hc | linear_combination (-certScale c) * hc

private theorem exists_cert_scalar (s₁ s₂ : ℝ) (hs : s₁ ≠ s₂) (hpos : 0 < s₁ + s₂) (v : ℂ) :
    ∃ c : ℂ, c * (s₁ : ℂ) - (starRingEnd ℂ) c * (s₂ : ℂ) = -v := by
  refine ⟨⟨-v.re / (s₁ - s₂), -v.im / (s₁ + s₂)⟩, ?_⟩
  have h1 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hs
  have h2 : s₁ + s₂ ≠ 0 := hpos.ne'
  apply Complex.ext
  · simp [Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  · simp [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    field_simp
    ring

private theorem continuous_conjEntries : Continuous conjEntries := by
  rw [Units.continuous_iff]
  constructor
  · exact Units.continuous_val.matrix_map Complex.continuous_conj
  · have : (fun g : GL (Fin 2) ℂ => ((conjEntries g)⁻¹ : GL (Fin 2) ℂ).val) =
        fun g => ((g⁻¹ : GL (Fin 2) ℂ).val).map (starRingEnd ℂ) := by
      funext g
      exact Units.coe_map_inv _ g
    rw [this]
    exact Units.continuous_coe_inv.matrix_map Complex.continuous_conj

private theorem continuous_conjugated (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (N : GL (Fin 2) ℂ) :
    Continuous fun k : GL (Fin 2) ℂ => φ (k⁻¹ * N * conjEntries k) :=
  hφ.comp ((continuous_inv.mul continuous_const).mul continuous_conjEntries)

private theorem exists_certificate (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (hne : a₁ ≠ a₂) (v : ℂ) :
    ∃ V : GL (Fin 2) ℂ, star (V : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      V⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries V = twistedSplitElt a₂ a₁ v ⟨h.2, h.1⟩ := by
  have hs : Real.sqrt a₁ ≠ Real.sqrt a₂ := fun heq =>
    hne ((Real.sqrt_inj h.1.le h.2.le).mp heq)
  have hpos : 0 < Real.sqrt a₁ + Real.sqrt a₂ := add_pos (Real.sqrt_pos.mpr h.1) (Real.sqrt_pos.mpr h.2)
  obtain ⟨c, hc⟩ := exists_cert_scalar (Real.sqrt a₁) (Real.sqrt a₂) hs hpos v
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (certMatrix c) (certMatrix_det_ne_zero c), certMatrix_unitary c, ?_⟩
  set V : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero (certMatrix c) (certMatrix_det_ne_zero c) with hV
  have hmul : twistedSplitElt a₁ a₂ v h * conjEntries V = V * twistedSplitElt a₂ a₁ v ⟨h.2, h.1⟩ := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, twistedSplitElt_val,
      twistedSplitElt_val, conjEntries_val]
    exact cert_identity _ _ v c hc
  rw [mul_assoc, hmul, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem conj_mul (N : GL (Fin 2) ℂ) (V k : GL (Fin 2) ℂ) :
    (V * k)⁻¹ * N * conjEntries (V * k) = k⁻¹ * (V⁻¹ * N * conjEntries V) * conjEntries k := by
  rw [conjEntries_mul, mul_inv_rev]
  simp only [mul_assoc]

private theorem transform_swap_of_ne (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (a₁ a₂ : ℝ)
    (h : 0 < a₁ ∧ 0 < a₂) (hne : a₁ ≠ a₂) :
    twistedSplitTransform φ a₂ a₁ = twistedSplitTransform φ a₁ a₂ := by
  simp only [twistedSplitTransform, dif_pos h, dif_pos (And.intro h.2 h.1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show unitaryAverage (fun k => φ (k⁻¹ * twistedSplitElt a₂ a₁ v ⟨h.2, h.1⟩ * conjEntries k)) =
    unitaryAverage (fun k => φ (k⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries k))
  obtain ⟨V, hV, hVN⟩ := exists_certificate a₁ a₂ h hne v
  rw [← unitaryAverage_mul_left _ (continuous_conjugated φ hφ (twistedSplitElt a₁ a₂ v h)) V hV]
  congr 1
  funext k
  show φ (k⁻¹ * twistedSplitElt a₂ a₁ v ⟨h.2, h.1⟩ * conjEntries k) =
    φ ((V * k)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (V * k))
  rw [conj_mul, hVN]

private theorem transform_swap (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (a₁ a₂ : ℝ) :
    twistedSplitTransform φ a₂ a₁ = twistedSplitTransform φ a₁ a₂ := by
  by_cases hne : a₁ = a₂
  · subst hne
    rfl
  by_cases h : 0 < a₁ ∧ 0 < a₂
  · exact transform_swap_of_ne φ hφ a₁ a₂ h hne
  · have h' : ¬ (0 < a₂ ∧ 0 < a₁) := fun h' => h ⟨h'.2, h'.1⟩
    simp only [twistedSplitTransform, dif_neg h, dif_neg h']

private theorem continuous_slice (P : Type) [NormedAddCommGroup P] (Φ : Ent × P → ℂ) (hΦ : Continuous Φ)
    (p : P) : Continuous fun g : GL (Fin 2) ℂ => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p) :=
  hΦ.comp (Units.continuous_val.prodMk continuous_const)

end Symmetry

end TwistedSplitSmooth
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_contDiff_twistedSplitTransform.TwistedSplitSmooth"

open TwistedSplitSmooth in

theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × P =>
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1) ∧
      HasCompactSupport (fun q : ℝ × ℝ × P =>
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1) ∧
      tsupport (fun q : ℝ × ℝ × P =>
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1) ⊆
        {q | q.1 * q.2.1 ≠ 0} ∧
      ∀ (a₁ a₂ : ℝ) (p : P),
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₂ a₁ =
          twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₁ a₂ := by
  refine ⟨family_contDiff P Φ hΦ hΦc hΦU, family_hasCompactSupport P Φ hΦ.continuous hΦc hΦU,
    tsupport_family_subset P Φ hΦ.continuous hΦc hΦU, ?_⟩
  intro a₁ a₂ p
  exact transform_swap _ (continuous_slice P Φ hΦ.continuous p) a₁ a₂

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_contDiff_twistedSplitTransform.TwistedSplitSmooth"

end S_AutomorphicForm_GL2Twisted_contDiff_twistedSplitTransform
end P2MW
export P2MW.S_AutomorphicForm_GL2Twisted_contDiff_twistedSplitTransform (solution)
