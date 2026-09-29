-- Prove2me | solution 1 for AutomorphicForm.GL2Real.map_ellipticProduct_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/84d73fd9-282a-5a52-8e3e-9e45e6f9f844

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_map_ellipticProduct_neg
set_option autoImplicit false
open MeasureTheory
p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_map_ellipticProduct_neg.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_map_ellipticProduct_neg.AutomorphicForm.GL2Real"

namespace AutomorphicForm
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "upperTriangular upperHalfPlaneElt ellipticElt"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

private noncomputable def partialTable (Φ : (Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ) (p : Fin 2 → Fin 2 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.of fun ij kl =>
    deriv
      (fun s : ℝ =>
        Φ (p + s • (Pi.single kl.1 (Pi.single kl.2 (1 : ℝ) : Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ)) ij.1 ij.2) 0

private theorem deriv_comp_line_apply (Φ : (Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (hΦ : DifferentiableAt ℝ Φ p) (v : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    deriv (fun s : ℝ => Φ (p + s • v) i j) 0 = fderiv ℝ Φ p v i j := by
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id' (x := (0 : ℝ))).smul_const v).const_add p
  have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ p) ((fun s : ℝ => p + s • v) 0) := by
    simpa using hΦ.hasFDerivAt
  have hv : HasDerivAt (fun s : ℝ => Φ (p + s • v)) (fderiv ℝ Φ p v) 0 :=
    hΦ'.comp_hasDerivAt (0 : ℝ) hline
  exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hv i) j).deriv

private theorem det_fderiv_eq_det_partialTable (Φ : (Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (hΦ : DifferentiableAt ℝ Φ p) :
    (fderiv ℝ Φ p).det = (partialTable Φ p).det := by
  unfold ContinuousLinearMap.det
  rw [← LinearMap.det_toMatrix (Pi.basis fun _ : Fin 2 => Pi.basisFun ℝ (Fin 2)),
    ← Matrix.det_reindex_self (Equiv.sigmaEquivProd (Fin 2) (Fin 2))]
  congr 1
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, partialTable, LinearMap.toMatrix_apply, Pi.basis_apply,
    Pi.basisFun_apply, deriv_comp_line_apply Φ p hΦ]

private noncomputable def ellipticProductNeg : (Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ :=
  fun p : Fin 2 → Fin 2 → ℝ => Matrix.of.symm
      (((if h : 0 < p 0 0 ∧ 0 < p 1 0 then
            ellipticElt (p 0 0) (p 0 1) h.1 *
              (upperHalfPlaneElt (p 1 1) (p 1 0) h.2 *
                upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)))⁻¹
          else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))

private theorem upperHalfPlaneElt_inv (x y : ℝ) (hy : 0 < y) :
    (upperHalfPlaneElt x y hy)⁻¹ = upperHalfPlaneElt (-x / y) y⁻¹ (inv_pos.2 hy) := by
  refine inv_eq_of_mul_eq_one_right ?_
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [upperHalfPlaneElt, Matrix.mul_apply, Fin.sum_univ_two, hy.ne']
    field_simp
    ring

private theorem upperTriangular_one_neg_one_inv :
    (upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)))⁻¹ =
      upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)) := by
  refine inv_eq_of_mul_eq_one_right ?_
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [upperTriangular, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_coe_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = a₁ * a₂ := by
  rw [show ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] from rfl,
    Matrix.det_fin_two_of]
  ring

private theorem det_coe_upperHalfPlaneElt (x y : ℝ) (hy : 0 < y) :
    ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = y := by
  rw [show ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![y, x; 0, 1] from rfl,
    Matrix.det_fin_two_of]
  ring

private theorem det_coe_ellipticElt (r θ : ℝ) (hr : 0 < r) :
    ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = r ^ 2 := by
  rw [show ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] from rfl, Matrix.det_fin_two_of]
  linear_combination (r ^ 2) * Real.cos_sq_add_sin_sq θ

private theorem det_of_ellipticProductNeg (p : Fin 2 → Fin 2 → ℝ) (hp : 0 < p 0 0 ∧ 0 < p 1 0) :
    (Matrix.of (ellipticProductNeg p)).det = -(p 0 0 ^ 2 / p 1 0) := by
  simp only [ellipticProductNeg, Equiv.apply_symm_apply, dif_pos hp, mul_inv_rev, upperTriangular_one_neg_one_inv,
    upperHalfPlaneElt_inv, Units.val_mul, Matrix.det_mul, det_coe_upperHalfPlaneElt, det_coe_ellipticElt,
    det_coe_upperTriangular]
  rw [div_eq_mul_inv]
  ring

private def ellipticProductDomain : Set (Fin 2 → Fin 2 → ℝ) :=
  {p : Fin 2 → Fin 2 → ℝ | 0 < p 0 0 ∧ 0 < p 1 0 ∧ 0 < p 0 1 ∧ p 0 1 < 2 * Real.pi}

private theorem measurableSet_ellipticProductDomain :
    MeasurableSet ellipticProductDomain := by
  refine IsOpen.measurableSet ?_
  unfold ellipticProductDomain
  simp only [Set.setOf_and]
  exact (isOpen_lt continuous_const (by fun_prop)).inter
    ((isOpen_lt continuous_const (by fun_prop)).inter
      ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const)))

private theorem isOpen_ellipticGuard : IsOpen {q : Fin 2 → Fin 2 → ℝ | 0 < q 0 0 ∧ 0 < q 1 0} := by
  simp only [Set.setOf_and]
  exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))

private noncomputable def ellipticProductNegEntries (p : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![p 0 0 * Real.cos (p 0 1) / p 1 0,
      p 0 0 * Real.cos (p 0 1) * (-(p 1 1 / p 1 0)) - p 0 0 * Real.sin (p 0 1)],
    ![-(p 0 0 * Real.sin (p 0 1)) / p 1 0,
      -(p 0 0 * Real.sin (p 0 1)) * (-(p 1 1 / p 1 0)) - p 0 0 * Real.cos (p 0 1)]]

private theorem ellipticProductNeg_eq_entries (p : Fin 2 → Fin 2 → ℝ) (hp : 0 < p 0 0 ∧ 0 < p 1 0) :
    ellipticProductNeg p = ellipticProductNegEntries p := by
  simp only [ellipticProductNeg, dif_pos hp]
  rw [Equiv.symm_apply_eq, mul_inv_rev, upperTriangular_one_neg_one_inv, upperHalfPlaneElt_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperHalfPlaneElt, upperTriangular, ellipticElt, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      ellipticProductNegEntries] <;> ring

private theorem ellipticProductNeg_eventuallyEq_entries (p : Fin 2 → Fin 2 → ℝ) (hp : 0 < p 0 0 ∧ 0 < p 1 0) :
    ellipticProductNeg =ᶠ[nhds p] ellipticProductNegEntries :=
  Filter.eventuallyEq_of_mem (isOpen_ellipticGuard.mem_nhds hp) fun q hq => ellipticProductNeg_eq_entries q hq

private theorem differentiableAt_ellipticProductNegEntries (p : Fin 2 → Fin 2 → ℝ) (hy : p 1 0 ≠ 0) :
    DifferentiableAt ℝ ellipticProductNegEntries p := by
  refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [ellipticProductNegEntries] <;> simp <;> fun_prop (disch := simp [hy])

private theorem differentiableAt_ellipticProductNeg (p : Fin 2 → Fin 2 → ℝ) (hp : p ∈ ellipticProductDomain) :
    DifferentiableAt ℝ ellipticProductNeg p :=
  (differentiableAt_ellipticProductNegEntries p hp.2.1.ne').congr_of_eventuallyEq
    (ellipticProductNeg_eventuallyEq_entries p ⟨hp.1, hp.2.1⟩)

private theorem volume_lowerLeft_eq_zero :
    volume {m : Fin 2 → Fin 2 → ℝ | m 1 0 = 0} = 0 := by
  haveI : (volume : Measure (Fin 2 → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin 2 → Fin 2 → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let φ : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
      (LinearMap.proj (1 : Fin 2) : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  have hker : (LinearMap.ker φ : Set (Fin 2 → Fin 2 → ℝ)) = {m : Fin 2 → Fin 2 → ℝ | m 1 0 = 0} := by
    ext m
    simp [φ]
  rw [← hker]
  refine Measure.addHaar_submodule volume (LinearMap.ker φ) fun htop => ?_
  have hmem : (fun _ _ => (1 : ℝ)) ∈ LinearMap.ker φ := by
    rw [htop]
    exact Submodule.mem_top
  simp [φ] at hmem

private def slotEquiv : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv (m := 2) (n := 2)).symm

private theorem det_partialTable_eq_det_of (Φ : (Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ)
    (p : Fin 2 → Fin 2 → ℝ) :
    (partialTable Φ p).det = Matrix.det !![
      partialTable Φ p (0, 0) (0, 0), partialTable Φ p (0, 0) (0, 1),
        partialTable Φ p (0, 0) (1, 0), partialTable Φ p (0, 0) (1, 1);
      partialTable Φ p (0, 1) (0, 0), partialTable Φ p (0, 1) (0, 1),
        partialTable Φ p (0, 1) (1, 0), partialTable Φ p (0, 1) (1, 1);
      partialTable Φ p (1, 0) (0, 0), partialTable Φ p (1, 0) (0, 1),
        partialTable Φ p (1, 0) (1, 0), partialTable Φ p (1, 0) (1, 1);
      partialTable Φ p (1, 1) (0, 0), partialTable Φ p (1, 1) (0, 1),
        partialTable Φ p (1, 1) (1, 0), partialTable Φ p (1, 1) (1, 1)] := by
  rw [← Matrix.det_submatrix_equiv_self slotEquiv (partialTable Φ p)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem det_of_fin_four (a b c d e f g h i j k l m n o q : ℝ) :
    Matrix.det !![a, b, c, d; e, f, g, h; i, j, k, l; m, n, o, q] =
      a * (f * (k * q - l * o) - g * (j * q - l * n) + h * (j * o - k * n)) - b * (e * (k * q - l * o) - g * (i *
        q - l * m) + h * (i * o - k * m)) + c * (e * (j * q - l * n) - f * (i * q - l * m) + h * (i * n - j * m)) -
        d * (e * (j * o - k * n) - f * (i * o - k * m) + g * (i * n - j * m)) := by
  have h1 : (1 : Fin 4).succAbove 2 = 3 := by decide
  have h2 : (2 : Fin 4).succAbove 2 = 3 := by decide
  have h3 : (3 : Fin 4).succAbove 2 = 2 := by decide
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, h1, h2, h3]
  ring

private theorem ellipticProductNeg_partial_00_00 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (0, 0) (0, 0) = Real.cos (p 0 1) * (p 1 0)⁻¹ := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_00_01 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (0, 0) (0, 1) = -p 0 0 * Real.sin (p 0 1) * (p 1 0)⁻¹ := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_00_10 (p : Fin 2 → Fin 2 → ℝ) (hy : p 1 0 ≠ 0) :
    partialTable ellipticProductNegEntries p (0, 0) (1, 0) = -Real.cos (p 0 1) * p 0 0 * (p 1 0)⁻¹ ^ 2 := by
  conv_lhs =>
    simp (disch := (first | fun_prop (disch := simp [hy]) | simp [hy])) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_00_11 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (0, 0) (1, 1) = 0 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_01_00 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (0, 1) (0, 0) =
      (-Real.cos (p 0 1) * p 1 1 * (p 1 0)⁻¹ - Real.sin (p 0 1)) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_01_01 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (0, 1) (0, 1) =
      (-Real.cos (p 0 1) * p 0 0 + p 0 0 * p 1 1 * Real.sin (p 0 1) * (p 1 0)⁻¹) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_01_10 (p : Fin 2 → Fin 2 → ℝ) (hy : p 1 0 ≠ 0) :
    partialTable ellipticProductNegEntries p (0, 1) (1, 0) = Real.cos (p 0 1) * p 0 0 * p 1 1 * (p 1 0)⁻¹ ^ 2 := by
  conv_lhs =>
    simp (disch := (first | fun_prop (disch := simp [hy]) | simp [hy])) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_01_11 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (0, 1) (1, 1) = -Real.cos (p 0 1) * p 0 0 * (p 1 0)⁻¹ := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_10_00 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (1, 0) (0, 0) = -Real.sin (p 0 1) * (p 1 0)⁻¹ := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_10_01 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (1, 0) (0, 1) = -Real.cos (p 0 1) * p 0 0 * (p 1 0)⁻¹ := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_10_10 (p : Fin 2 → Fin 2 → ℝ) (hy : p 1 0 ≠ 0) :
    partialTable ellipticProductNegEntries p (1, 0) (1, 0) = p 0 0 * Real.sin (p 0 1) * (p 1 0)⁻¹ ^ 2 := by
  conv_lhs =>
    simp (disch := (first | fun_prop (disch := simp [hy]) | simp [hy])) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_10_11 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (1, 0) (1, 1) = 0 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_11_00 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (1, 1) (0, 0) =
      (-Real.cos (p 0 1) + p 1 1 * Real.sin (p 0 1) * (p 1 0)⁻¹) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_11_01 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (1, 1) (0, 1) =
      (Real.cos (p 0 1) * p 0 0 * p 1 1 * (p 1 0)⁻¹ + p 0 0 * Real.sin (p 0 1)) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_11_10 (p : Fin 2 → Fin 2 → ℝ) (hy : p 1 0 ≠ 0) :
    partialTable ellipticProductNegEntries p (1, 1) (1, 0) = -p 0 0 * p 1 1 * Real.sin (p 0 1) * (p 1 0)⁻¹ ^ 2 := by
  conv_lhs =>
    simp (disch := (first | fun_prop (disch := simp [hy]) | simp [hy])) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem ellipticProductNeg_partial_11_11 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable ellipticProductNegEntries p (1, 1) (1, 1) = p 0 0 * Real.sin (p 0 1) * (p 1 0)⁻¹ := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, ellipticProductNegEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem det_partialTable_ellipticProductNegEntries (p : Fin 2 → Fin 2 → ℝ) (hy : p 1 0 ≠ 0) :
    (partialTable ellipticProductNegEntries p).det = -(p 0 0 ^ 3 * (p 1 0)⁻¹ ^ 4) := by
  have hcs : Real.cos (p 0 1) ^ 2 + Real.sin (p 0 1) ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 1)
  have hyy : p 1 0 * (p 1 0)⁻¹ = 1 := mul_inv_cancel₀ hy
  rw [det_partialTable_eq_det_of, det_of_fin_four, ellipticProductNeg_partial_00_00 p,
    ellipticProductNeg_partial_00_01 p, ellipticProductNeg_partial_00_10 p hy, ellipticProductNeg_partial_00_11 p,
    ellipticProductNeg_partial_01_00 p, ellipticProductNeg_partial_01_01 p, ellipticProductNeg_partial_01_10 p hy,
    ellipticProductNeg_partial_01_11 p, ellipticProductNeg_partial_10_00 p, ellipticProductNeg_partial_10_01 p,
    ellipticProductNeg_partial_10_10 p hy, ellipticProductNeg_partial_10_11 p, ellipticProductNeg_partial_11_00 p,
    ellipticProductNeg_partial_11_01 p, ellipticProductNeg_partial_11_10 p hy, ellipticProductNeg_partial_11_11 p]
  linear_combination (-Real.cos (p 0 1) ^ 2 * p 0 0 ^ 3 * (p 1 0)⁻¹ ^ 4 - p 0 0 ^ 3 * Real.sin (p 0 1) ^ 2 *
    (p 1 0)⁻¹ ^ 4 - p 0 0 ^ 3 * (p 1 0)⁻¹ ^ 4) * hcs + (0) * hyy

private theorem abs_det_fderiv_ellipticProductNeg (p : Fin 2 → Fin 2 → ℝ) (hp : p ∈ ellipticProductDomain) :
    |(fderiv ℝ ellipticProductNeg p).det| = p 0 0 ^ 3 / p 1 0 ^ 4 := by
  have hy : p 1 0 ≠ 0 := hp.2.1.ne'
  have h00 : 0 < p 0 0 := hp.1
  rw [(ellipticProductNeg_eventuallyEq_entries p ⟨hp.1, hp.2.1⟩).fderiv_eq,
    det_fderiv_eq_det_partialTable _ _ (differentiableAt_ellipticProductNegEntries p hy),
    det_partialTable_ellipticProductNegEntries p hy]
  rw [abs_neg, abs_of_nonneg]
  · ring1
  · positivity

private theorem exists_angle_of_sin_pos (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (hs : 0 < s) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ Real.cos θ = c ∧ Real.sin θ = s := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hc1 : -1 < c := by nlinarith
  have hc2 : c < 1 := by nlinarith
  refine ⟨Real.arccos c, Real.arccos_pos.2 hc2, Real.arccos_lt_pi.2 hc1, Real.cos_arccos hc1.le hc2.le, ?_⟩
  rw [Real.sin_arccos, show (1 : ℝ) - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq hs.le]

private theorem exists_angle_of_sin_ne_zero (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ θ ≠ Real.pi ∧ Real.cos θ = c ∧ Real.sin θ = s := by
  rcases hs.lt_or_gt with hneg | hpos
  · obtain ⟨θ, h0, hπ, hc, hs'⟩ := exists_angle_of_sin_pos c (-s) (by rw [neg_sq]; exact h) (by linarith)
    refine ⟨2 * Real.pi - θ, by linarith, by linarith, fun heq => ?_, ?_, ?_⟩
    · linarith
    · rw [Real.cos_two_pi_sub, hc]
    · rw [Real.sin_two_pi_sub, hs', neg_neg]
  · obtain ⟨θ, h0, hπ, hc, hs'⟩ := exists_angle_of_sin_pos c s h hpos
    exact ⟨θ, h0, by linarith [Real.pi_pos], hπ.ne, hc, hs'⟩

private theorem image_ellipticProductNeg_subset :
    ellipticProductNeg '' ellipticProductDomain ⊆ {m : Fin 2 → Fin 2 → ℝ | m 0 0 * m 1 1 - m 0 1 * m 1 0 < 0} := by
  rintro _ ⟨p, hp, rfl⟩
  have hdet := det_of_ellipticProductNeg p ⟨hp.1, hp.2.1⟩
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.of_apply] at hdet
  simp only [Set.mem_setOf_eq]
  rw [hdet]
  exact neg_lt_zero.2 (div_pos (pow_pos hp.1 2) hp.2.1)

private theorem exists_polar (A B : ℝ) (hB : B ≠ 0) :
    ∃ r φ : ℝ, 0 < r ∧ 0 < φ ∧ φ < 2 * Real.pi ∧ φ ≠ Real.pi ∧ r * Real.cos φ = A ∧ r * Real.sin φ = B := by
  obtain ⟨r, hr, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = A ^ 2 + B ^ 2 :=
    ⟨Real.sqrt (A ^ 2 + B ^ 2), Real.sqrt_pos.2 (by positivity), Real.sq_sqrt (by positivity)⟩
  have hr' : r ≠ 0 := hr.ne'
  obtain ⟨φ, h0, h2, hπ, hc, hs⟩ :=
    exists_angle_of_sin_ne_zero (A / r) (B / r) (by field_simp; nlinarith [hr2]) (div_ne_zero hB hr')
  refine ⟨r, φ, hr, h0, h2, hπ, ?_, ?_⟩
  · rw [hc]; field_simp
  · rw [hs]; field_simp

private theorem image_ellipticProductNeg :
    {m : Fin 2 → Fin 2 → ℝ | m 0 0 * m 1 1 - m 0 1 * m 1 0 < 0} ⊆
      ellipticProductNeg '' ellipticProductDomain ∪ {m : Fin 2 → Fin 2 → ℝ | m 1 0 = 0} := by
  intro m hm
  simp only [Set.mem_setOf_eq] at hm
  by_cases h10 : m 1 0 = 0
  · exact Or.inr h10
  left
  have hD : 0 < m 0 0 ^ 2 + m 1 0 ^ 2 := by positivity
  have hD' : m 0 0 ^ 2 + m 1 0 ^ 2 ≠ 0 := hD.ne'
  obtain ⟨y, hy, hy_def⟩ : ∃ y : ℝ, 0 < y ∧ y * (m 0 0 ^ 2 + m 1 0 ^ 2) = -(m 0 0 * m 1 1 - m 0 1 * m 1 0) :=
    ⟨-(m 0 0 * m 1 1 - m 0 1 * m 1 0) / (m 0 0 ^ 2 + m 1 0 ^ 2), div_pos (neg_pos.2 hm) hD, by field_simp⟩
  obtain ⟨x, hx_def⟩ : ∃ x : ℝ, x * (m 0 0 ^ 2 + m 1 0 ^ 2) = -(m 0 0 * m 0 1 + m 1 0 * m 1 1) :=
    ⟨-(m 0 0 * m 0 1 + m 1 0 * m 1 1) / (m 0 0 ^ 2 + m 1 0 ^ 2), by field_simp⟩
  have h1 : m 0 0 * y + m 1 0 * x + m 1 1 = 0 := by
    have h : (m 0 0 * y + m 1 0 * x + m 1 1) * (m 0 0 ^ 2 + m 1 0 ^ 2) = 0 := by
      linear_combination m 0 0 * hy_def + m 1 0 * hx_def
    exact (mul_eq_zero.1 h).resolve_right hD'
  have h2 : m 0 0 * x - m 1 0 * y + m 0 1 = 0 := by
    have h : (m 0 0 * x - m 1 0 * y + m 0 1) * (m 0 0 ^ 2 + m 1 0 ^ 2) = 0 := by
      linear_combination m 0 0 * hx_def - m 1 0 * hy_def
    exact (mul_eq_zero.1 h).resolve_right hD'
  have hy' : y ≠ 0 := hy.ne'
  obtain ⟨ρ, φ, hρ, hφ0, hφ2, -, hc, hs⟩ :=
    exists_polar (m 0 0 * y) (-(m 1 0 * y)) (neg_ne_zero.2 (mul_ne_zero h10 hy'))
  have e00 : ρ * Real.cos φ / y = m 0 0 := by rw [hc]; field_simp
  have e01 : ρ * Real.cos φ * (-(x / y)) - ρ * Real.sin φ = m 0 1 := by
    rw [hc, hs, show m 0 0 * y * (-(x / y)) = -(m 0 0 * x) by field_simp]
    linear_combination (-1 : ℝ) * h2
  have e10 : -(ρ * Real.sin φ) / y = m 1 0 := by rw [hs]; field_simp
  have e11 : -(ρ * Real.sin φ) * (-(x / y)) - ρ * Real.cos φ = m 1 1 := by
    rw [hs, hc, show -(-(m 1 0 * y)) * (-(x / y)) = -(m 1 0 * x) by field_simp]
    linear_combination (-1 : ℝ) * h1
  refine ⟨![![ρ, φ], ![y, x]], ⟨hρ, hy, hφ0, hφ2⟩, ?_⟩
  rw [ellipticProductNeg_eq_entries ![![ρ, φ], ![y, x]] ⟨hρ, hy⟩]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [ellipticProductNegEntries, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  exacts [e00, e01, e10, e11]

private theorem angle_eq_of_cos_eq_of_sin_eq {φ ψ : ℝ} (hφ : 0 < φ) (hφ2 : φ < 2 * Real.pi) (hψ : 0 < ψ)
    (hψ2 : ψ < 2 * Real.pi) (hc : Real.cos φ = Real.cos ψ) (hs : Real.sin φ = Real.sin ψ) : φ = ψ := by
  rcases le_or_gt 0 (Real.sin φ) with h | h
  · have hφπ : φ ≤ Real.pi := not_lt.1 fun hcon => by
      have h1 : 0 < Real.sin (φ - Real.pi) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at h1
      linarith
    have hψπ : ψ ≤ Real.pi := not_lt.1 fun hcon => by
      have h1 : 0 < Real.sin (ψ - Real.pi) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at h1
      linarith
    exact Real.injOn_cos ⟨hφ.le, hφπ⟩ ⟨hψ.le, hψπ⟩ hc
  · have hφπ : Real.pi < φ := not_le.1 fun hcon => by
      have h1 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ.le hcon
      linarith
    have hψπ : Real.pi < ψ := not_le.1 fun hcon => by
      have h1 : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi hψ.le hcon
      linarith
    have h2 : Real.cos (φ - Real.pi) = Real.cos (ψ - Real.pi) := by rw [Real.cos_sub_pi, Real.cos_sub_pi, hc]
    have h3 : φ - Real.pi = ψ - Real.pi :=
      Real.injOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h2
    linarith

private theorem eq_of_ellipticProductNegEntries_eq (p q : Fin 2 → Fin 2 → ℝ)
    (hpq : ellipticProductNegEntries p = ellipticProductNegEntries q) (hrp : 0 < p 0 0) (hrq : 0 < q 0 0)
    (hyp0 : 0 < p 1 0) (hyq0 : 0 < q 1 0) (hφp : 0 < p 0 1) (hφp2 : p 0 1 < 2 * Real.pi) (hφq : 0 < q 0 1)
    (hφq2 : q 0 1 < 2 * Real.pi) : p = q := by
  have h00 :
      p 0 0 * Real.cos (p 0 1) / p 1 0 =
      q 0 0 * Real.cos (q 0 1) / q 1 0 := by
    simpa [ellipticProductNegEntries] using congrFun (congrFun hpq 0) 0
  have h01 :
      p 0 0 * Real.cos (p 0 1) * (-(p 1 1 / p 1 0)) - p 0 0 * Real.sin (p 0 1) =
      q 0 0 * Real.cos (q 0 1) * (-(q 1 1 / q 1 0)) - q 0 0 * Real.sin (q 0 1) := by
    simpa [ellipticProductNegEntries] using congrFun (congrFun hpq 0) 1
  have h10 :
      -(p 0 0 * Real.sin (p 0 1)) / p 1 0 =
      -(q 0 0 * Real.sin (q 0 1)) / q 1 0 := by
    simpa [ellipticProductNegEntries] using congrFun (congrFun hpq 1) 0
  have h11 :
      -(p 0 0 * Real.sin (p 0 1)) * (-(p 1 1 / p 1 0)) - p 0 0 * Real.cos (p 0 1) =
      -(q 0 0 * Real.sin (q 0 1)) * (-(q 1 1 / q 1 0)) - q 0 0 * Real.cos (q 0 1) := by
    simpa [ellipticProductNegEntries] using congrFun (congrFun hpq 1) 1
  have hcsp : Real.cos (p 0 1) ^ 2 + Real.sin (p 0 1) ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 0 1)
  have hcsq : Real.cos (q 0 1) ^ 2 + Real.sin (q 0 1) ^ 2 = 1 := Real.cos_sq_add_sin_sq (q 0 1)
  have hyp : p 1 0 * (p 1 0)⁻¹ = 1 := mul_inv_cancel₀ hyp0.ne'
  have hyq : q 1 0 * (q 1 0)⁻¹ = 1 := mul_inv_cancel₀ hyq0.ne'
  have hD : p 0 0 ^ 2 * q 1 0 = q 0 0 ^ 2 * p 1 0 := by
    linear_combination (Real.cos (p 0 1) * p 0 0 * p 1 0 * q 1 0 - p 0 0 * p 1 0 * p 1 1 * q 1 0 * Real.sin (p 0 1) *
      (p 1 0)⁻¹) * h00 + (-Real.cos (q 0 1) * p 1 0 * q 0 0 * q 1 0 * (q 1 0)⁻¹) * h11 + (-p 0 0 * p 1 0 * q 1 0 *
      Real.sin (p 0 1) * (p 1 0)⁻¹) * h01 + (-Real.cos (q 0 1) * p 1 0 * q 0 0 * q 1 0 * q 1 1 * (q 1 0)⁻¹ - p 1 0 *
      q 0 0 * q 1 0 * Real.sin (q 0 1)) * h10 + (-p 0 0 ^ 2 * p 1 0 * q 1 0 * (p 1 0)⁻¹) * hcsp + (p 1 0 *
      q 0 0 ^ 2 * q 1 0 * (q 1 0)⁻¹) * hcsq + (-p 0 0 ^ 2 * q 1 0) * hyp + (p 1 0 * q 0 0 ^ 2) * hyq
  have hE : p 0 0 ^ 2 * q 1 0 ^ 2 = q 0 0 ^ 2 * p 1 0 ^ 2 := by
    linear_combination (Real.cos (p 0 1) * p 0 0 * p 1 0 ^ 2 * q 1 0 ^ 2 * (p 1 0)⁻¹ + Real.cos (q 0 1) * p 1 0 ^ 2 *
      q 0 0 * q 1 0 ^ 2 * (q 1 0)⁻¹) * h00 + (-p 0 0 * p 1 0 ^ 2 * q 1 0 ^ 2 * Real.sin (p 0 1) * (p 1 0)⁻¹ -
      p 1 0 ^ 2 * q 0 0 * q 1 0 ^ 2 * Real.sin (q 0 1) * (q 1 0)⁻¹) * h10 + (-p 0 0 ^ 2 * p 1 0 ^ 2 * q 1 0 ^ 2 *
      (p 1 0)⁻¹ ^ 2) * hcsp + (p 1 0 ^ 2 * q 0 0 ^ 2 * q 1 0 ^ 2 * (q 1 0)⁻¹ ^ 2) * hcsq + (-p 0 0 ^ 2 * p 1 0 *
      q 1 0 ^ 2 * (p 1 0)⁻¹ - p 0 0 ^ 2 * q 1 0 ^ 2) * hyp + (p 1 0 ^ 2 * q 0 0 ^ 2 * q 1 0 * (q 1 0)⁻¹ + p 1 0 ^ 2 *
      q 0 0 ^ 2) * hyq
  have hy1 : q 0 0 ^ 2 * p 1 0 * (p 1 0 - q 1 0) = 0 := by
    linear_combination (q 1 0) * hD + (-1) * hE
  have hy : p 1 0 = q 1 0 := by
    rcases mul_eq_zero.1 hy1 with h1 | h1
    · exfalso
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact pow_ne_zero 2 hrq.ne' h2
      · exact hyp0.ne' h2
    · exact sub_eq_zero.1 h1
  have hyi : (p 1 0)⁻¹ = (q 1 0)⁻¹ := by rw [hy]
  have hr1 : (p 0 0 - q 0 0) * (p 0 0 + q 0 0) * p 1 0 = 0 := by
    linear_combination (1) * hD + (p 0 0 ^ 2) * hy
  have hr : p 0 0 = q 0 0 := by
    rcases mul_eq_zero.1 hr1 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact sub_eq_zero.1 h2
      · exfalso
        linarith
    · exfalso
      exact hyp0.ne' h1
  have hC1 : p 0 0 * (Real.cos (p 0 1) - Real.cos (q 0 1)) = 0 := by
    linear_combination (p 1 0) * h00 + (-Real.cos (q 0 1) * p 1 0 * q 0 0) * hyi + (-Real.cos (q 0 1) * p 1 0 *
      (p 1 0)⁻¹) * hr + (-Real.cos (p 0 1) * p 0 0 + Real.cos (q 0 1) * p 0 0) * hyp
  have hC : Real.cos (p 0 1) = Real.cos (q 0 1) := sub_eq_zero.1 ((mul_eq_zero.1 hC1).resolve_left hrp.ne')
  have hS1 : p 0 0 * (Real.sin (p 0 1) - Real.sin (q 0 1)) = 0 := by
    linear_combination (-p 1 0) * h10 + (-p 1 0 * q 0 0 * Real.sin (q 0 1)) * hyi + (-p 1 0 * Real.sin (q 0 1) *
      (p 1 0)⁻¹) * hr + (-p 0 0 * Real.sin (p 0 1) + p 0 0 * Real.sin (q 0 1)) * hyp
  have hS : Real.sin (p 0 1) = Real.sin (q 0 1) := sub_eq_zero.1 ((mul_eq_zero.1 hS1).resolve_left hrp.ne')
  have hφ : p 0 1 = q 0 1 := angle_eq_of_cos_eq_of_sin_eq hφp hφp2 hφq hφq2 hC hS
  have hx1 : p 0 0 * (p 1 1 - q 1 1) = 0 := by
    linear_combination (-Real.cos (p 0 1) * p 1 0) * h01 + (p 1 0 * Real.sin (p 0 1)) * h11 + (-Real.cos (p 0 1) *
      Real.cos (q 0 1) * p 1 0 * q 0 0 * q 1 1 - p 1 0 * q 0 0 * q 1 1 * Real.sin (p 0 1) * Real.sin (q 0 1)) * hyi +
      (-Real.cos (p 0 1) * Real.cos (q 0 1) * p 1 0 * q 1 1 * (p 1 0)⁻¹ - Real.cos (p 0 1) * p 1 0 *
      Real.sin (q 0 1) + Real.cos (q 0 1) * p 1 0 * Real.sin (p 0 1) - p 1 0 * q 1 1 * Real.sin (p 0 1) *
      Real.sin (q 0 1) * (p 1 0)⁻¹) * hr + (-Real.cos (p 0 1) * p 0 0 * p 1 0 * q 1 1 * (p 1 0)⁻¹ + p 0 0 * p 1 0 *
      Real.sin (p 0 1)) * hC + (-Real.cos (p 0 1) * p 0 0 * p 1 0 - p 0 0 * p 1 0 * q 1 1 * Real.sin (p 0 1) *
      (p 1 0)⁻¹) * hS + (-p 0 0 * p 1 0 * p 1 1 * (p 1 0)⁻¹ + p 0 0 * p 1 0 * q 1 1 * (p 1 0)⁻¹) * hcsp + (-p 0 0 *
      p 1 1 + p 0 0 * q 1 1) * hyp
  have hx : p 1 1 = q 1 1 := sub_eq_zero.1 ((mul_eq_zero.1 hx1).resolve_left hrp.ne')
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

private theorem injOn_ellipticProductNeg :
    Set.InjOn ellipticProductNeg ellipticProductDomain := by
  intro p hp q hq hpq
  rw [ellipticProductNeg_eq_entries p ⟨hp.1, hp.2.1⟩, ellipticProductNeg_eq_entries q ⟨hq.1, hq.2.1⟩] at hpq
  exact eq_of_ellipticProductNegEntries_eq p q hpq hp.1 hq.1 hp.2.1 hq.2.1 hp.2.2.1 hp.2.2.2 hq.2.2.1 hq.2.2.2

private theorem map_chart_eq (f : (Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ) (D : Set (Fin 2 → Fin 2 → ℝ))
    (hD : MeasurableSet D) (hdiff : ∀ p ∈ D, DifferentiableAt ℝ f p) (hinj : Set.InjOn f D)
    (δ : (Fin 2 → Fin 2 → ℝ) → ℝ) (hδ : ∀ p ∈ D, |(fderiv ℝ f p).det| = δ p) (R : Set (Fin 2 → Fin 2 → ℝ))
    (hR : f '' D =ᵐ[volume] R) :
    Measure.map f ((volume.restrict D).withDensity fun p => ENNReal.ofReal (δ p)) = volume.restrict R := by
  haveI : (volume : Measure (Fin 2 → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin 2 → Fin 2 → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h1 : ((volume.restrict D).withDensity fun p => ENNReal.ofReal (δ p)) =
      (volume.restrict D).withDensity fun p => ENNReal.ofReal |(fderiv ℝ f p).det| := by
    refine withDensity_congr_ae ((ae_restrict_iff' hD).2 (Filter.Eventually.of_forall fun p hp => ?_))
    show ENNReal.ofReal (δ p) = ENNReal.ofReal |(fderiv ℝ f p).det|
    rw [hδ p hp]
  rw [h1, map_withDensity_abs_det_fderiv_eq_addHaar volume hD.nullMeasurableSet
    (fun p hp => (hdiff p hp).hasFDerivAt.hasFDerivWithinAt) hinj]
  exact Measure.restrict_congr_set hR

private theorem ae_eq_of_subset_of_subset_union (S R : Set (Fin 2 → Fin 2 → ℝ)) (h₁ : S ⊆ R)
    (h₂ : R ⊆ S ∪ {m : Fin 2 → Fin 2 → ℝ | m 1 0 = 0}) : S =ᵐ[volume] R := by
  rw [ae_eq_set]
  refine ⟨measure_mono_null (fun m hm => (hm.2 (h₁ hm.1)).elim) measure_empty, ?_⟩
  exact measure_mono_null (fun m hm => Or.resolve_left (h₂ hm.1) hm.2) volume_lowerLeft_eq_zero

end AutomorphicForm.GL2Real

theorem solution :
    Measure.map
      (fun p : Fin 2 → Fin 2 → ℝ => Matrix.of.symm
      (((if h : 0 < p 0 0 ∧ 0 < p 1 0 then
            ellipticElt (p 0 0) (p 0 1) h.1 *
              (upperHalfPlaneElt (p 1 1) (p 1 0) h.2 *
                upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)))⁻¹
          else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))
      ((volume.restrict
        {p : Fin 2 → Fin 2 → ℝ | 0 < p 0 0 ∧ 0 < p 1 0 ∧ 0 < p 0 1 ∧ p 0 1 < 2 * Real.pi}).withDensity
        (fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4))) =
      volume.restrict
        {m : Fin 2 → Fin 2 → ℝ | m 0 0 * m 1 1 - m 0 1 * m 1 0 < 0} := by
  exact map_chart_eq ellipticProductNeg ellipticProductDomain measurableSet_ellipticProductDomain
    differentiableAt_ellipticProductNeg injOn_ellipticProductNeg (fun p => p 0 0 ^ 3 / p 1 0 ^ 4)
    abs_det_fderiv_ellipticProductNeg _
    (ae_eq_of_subset_of_subset_union _ _ image_ellipticProductNeg_subset image_ellipticProductNeg)

end S_AutomorphicForm_GL2Real_map_ellipticProduct_neg
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_map_ellipticProduct_neg (solution)
