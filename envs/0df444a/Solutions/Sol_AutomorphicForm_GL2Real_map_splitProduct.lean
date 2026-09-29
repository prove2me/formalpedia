-- Prove2me | solution 1 for AutomorphicForm.GL2Real.map_splitProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e2e2c029-ac3f-599e-b771-e182651b3318

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_map_splitProduct
set_option autoImplicit false
open MeasureTheory
p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_map_splitProduct.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_map_splitProduct.AutomorphicForm.GL2Real"

namespace AutomorphicForm
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular"
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

private noncomputable def splitProduct : (Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ :=
  fun p : Fin 2 → Fin 2 → ℝ => Matrix.of.symm
      (((if h : p 0 0 * p 0 1 ≠ 0 then
            upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) h * (rotation (p 1 0))⁻¹
          else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))

private theorem rotation_inv (θ : ℝ) : (rotation θ)⁻¹ = rotation (-θ) := by
  refine inv_eq_of_mul_eq_one_right ?_
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;>
      nlinarith [Real.cos_sq_add_sin_sq θ]

private theorem det_coe_rotation (θ : ℝ) : ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [show ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] from rfl, Matrix.det_fin_two_of]
  linear_combination Real.cos_sq_add_sin_sq θ

private theorem det_coe_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = a₁ * a₂ := by
  rw [show ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] from rfl,
    Matrix.det_fin_two_of]
  ring

private theorem det_of_splitProduct (p : Fin 2 → Fin 2 → ℝ) (hp : p 0 0 * p 0 1 ≠ 0) :
    (Matrix.of (splitProduct p)).det = p 0 0 * p 0 1 := by
  simp only [splitProduct, Equiv.apply_symm_apply, dif_pos hp, Units.val_mul, Matrix.det_mul, rotation_inv,
    det_coe_rotation, det_coe_upperTriangular, mul_one]

private def splitProductDomain : Set (Fin 2 → Fin 2 → ℝ) :=
  {p : Fin 2 → Fin 2 → ℝ | p 0 0 * p 0 1 ≠ 0 ∧ 0 < p 1 0 ∧ p 1 0 < Real.pi}

private theorem measurableSet_splitProductDomain :
    MeasurableSet splitProductDomain := by
  refine IsOpen.measurableSet ?_
  unfold splitProductDomain
  simp only [Set.setOf_and]
  exact (isOpen_ne_fun (by fun_prop) continuous_const).inter
    ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const))

private theorem isOpen_splitGuard : IsOpen {q : Fin 2 → Fin 2 → ℝ | q 0 0 * q 0 1 ≠ 0} :=
  isOpen_ne_fun (by fun_prop) continuous_const

private noncomputable def splitProductEntries (p : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![p 0 0 * Real.cos (p 1 0) + p 0 0 * p 1 1 * Real.sin (p 1 0),
      -(p 0 0 * Real.sin (p 1 0)) + p 0 0 * p 1 1 * Real.cos (p 1 0)],
    ![p 0 1 * Real.sin (p 1 0), p 0 1 * Real.cos (p 1 0)]]

private theorem splitProduct_eq_entries (p : Fin 2 → Fin 2 → ℝ) (hp : p 0 0 * p 0 1 ≠ 0) :
    splitProduct p = splitProductEntries p := by
  simp only [splitProduct, dif_pos hp]
  rw [Equiv.symm_apply_eq, rotation_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, upperTriangular, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, splitProductEntries,
      Real.cos_neg, Real.sin_neg]

private theorem splitProduct_eventuallyEq_entries (p : Fin 2 → Fin 2 → ℝ) (hp : p 0 0 * p 0 1 ≠ 0) :
    splitProduct =ᶠ[nhds p] splitProductEntries :=
  Filter.eventuallyEq_of_mem (isOpen_splitGuard.mem_nhds hp) fun q hq => splitProduct_eq_entries q hq

private theorem differentiableAt_splitProductEntries (p : Fin 2 → Fin 2 → ℝ) :
    DifferentiableAt ℝ splitProductEntries p := by
  refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [splitProductEntries] <;> simp <;> fun_prop

private theorem differentiableAt_splitProduct (p : Fin 2 → Fin 2 → ℝ) (hp : p 0 0 * p 0 1 ≠ 0) :
    DifferentiableAt ℝ splitProduct p :=
  (differentiableAt_splitProductEntries p).congr_of_eventuallyEq (splitProduct_eventuallyEq_entries p hp)

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

private theorem splitProduct_partial_00_00 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (0, 0) (0, 0) = Real.cos (p 1 0) + p 1 1 * Real.sin (p 1 0) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_00_01 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (0, 0) (0, 1) = 0 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_00_10 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (0, 0) (1, 0) =
      (Real.cos (p 1 0) * p 0 0 * p 1 1 - p 0 0 * Real.sin (p 1 0)) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_00_11 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (0, 0) (1, 1) = p 0 0 * Real.sin (p 1 0) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_01_00 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (0, 1) (0, 0) = Real.cos (p 1 0) * p 1 1 - Real.sin (p 1 0) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_01_01 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (0, 1) (0, 1) = 0 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_01_10 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (0, 1) (1, 0) =
      (-Real.cos (p 1 0) * p 0 0 - p 0 0 * p 1 1 * Real.sin (p 1 0)) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_01_11 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (0, 1) (1, 1) = Real.cos (p 1 0) * p 0 0 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_10_00 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (1, 0) (0, 0) = 0 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_10_01 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (1, 0) (0, 1) = Real.sin (p 1 0) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_10_10 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (1, 0) (1, 0) = Real.cos (p 1 0) * p 0 1 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_10_11 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (1, 0) (1, 1) = 0 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_11_00 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (1, 1) (0, 0) = 0 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_11_01 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (1, 1) (0, 1) = Real.cos (p 1 0) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_11_10 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (1, 1) (1, 0) = -p 0 1 * Real.sin (p 1 0) := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem splitProduct_partial_11_11 (p : Fin 2 → Fin 2 → ℝ) :
    partialTable splitProductEntries p (1, 1) (1, 1) = 0 := by
  conv_lhs =>
    simp (disch := (first | fun_prop | simp)) [partialTable, splitProductEntries]
  all_goals first | ring1 | (field_simp; ring1)

private theorem det_partialTable_splitProductEntries (p : Fin 2 → Fin 2 → ℝ) :
    (partialTable splitProductEntries p).det = -(p 0 0 * p 0 1) := by
  have hcs : Real.cos (p 1 0) ^ 2 + Real.sin (p 1 0) ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 1 0)
  rw [det_partialTable_eq_det_of, det_of_fin_four, splitProduct_partial_00_00 p, splitProduct_partial_00_01 p,
    splitProduct_partial_00_10 p, splitProduct_partial_00_11 p, splitProduct_partial_01_00 p,
    splitProduct_partial_01_01 p, splitProduct_partial_01_10 p, splitProduct_partial_01_11 p,
    splitProduct_partial_10_00 p, splitProduct_partial_10_01 p, splitProduct_partial_10_10 p,
    splitProduct_partial_10_11 p, splitProduct_partial_11_00 p, splitProduct_partial_11_01 p,
    splitProduct_partial_11_10 p, splitProduct_partial_11_11 p]
  linear_combination (-Real.cos (p 1 0) ^ 2 * p 0 0 * p 0 1 - p 0 0 * p 0 1 * Real.sin (p 1 0) ^ 2 - p 0 0 *
    p 0 1) * hcs

private theorem abs_det_fderiv_splitProduct (p : Fin 2 → Fin 2 → ℝ) (hp : p 0 0 * p 0 1 ≠ 0) :
    |(fderiv ℝ splitProduct p).det| = |p 0 0 * p 0 1| := by
  rw [(splitProduct_eventuallyEq_entries p hp).fderiv_eq,
    det_fderiv_eq_det_partialTable _ _ (differentiableAt_splitProductEntries p),
    det_partialTable_splitProductEntries p]
  exact abs_neg _

private theorem exists_angle_of_sin_pos (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (hs : 0 < s) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ Real.cos θ = c ∧ Real.sin θ = s := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hc1 : -1 < c := by nlinarith
  have hc2 : c < 1 := by nlinarith
  refine ⟨Real.arccos c, Real.arccos_pos.2 hc2, Real.arccos_lt_pi.2 hc1, Real.cos_arccos hc1.le hc2.le, ?_⟩
  rw [Real.sin_arccos, show (1 : ℝ) - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq hs.le]

private theorem exists_line_of_ne_zero (a b : ℝ) (ha : a ≠ 0) :
    ∃ α θ : ℝ, α ≠ 0 ∧ 0 < θ ∧ θ < Real.pi ∧ α * Real.sin θ = a ∧ α * Real.cos θ = b := by
  obtain ⟨n, hn, hn2⟩ : ∃ n : ℝ, 0 < n ∧ n ^ 2 = a ^ 2 + b ^ 2 :=
    ⟨Real.sqrt (a ^ 2 + b ^ 2), Real.sqrt_pos.2 (by positivity), Real.sq_sqrt (by positivity)⟩
  have hn' : n ≠ 0 := hn.ne'
  rcases ha.lt_or_gt with hneg | hpos
  · obtain ⟨θ, h0, hπ, hc, hs⟩ := exists_angle_of_sin_pos (-(b / n)) (-(a / n))
      (by field_simp; nlinarith [hn2]) (by have := div_neg_of_neg_of_pos hneg hn; linarith)
    refine ⟨-n, θ, neg_ne_zero.2 hn', h0, hπ, ?_, ?_⟩
    · rw [hs]; field_simp
    · rw [hc]; field_simp
  · obtain ⟨θ, h0, hπ, hc, hs⟩ := exists_angle_of_sin_pos (b / n) (a / n)
      (by field_simp; nlinarith [hn2]) (div_pos hpos hn)
    refine ⟨n, θ, hn', h0, hπ, ?_, ?_⟩
    · rw [hs]; field_simp
    · rw [hc]; field_simp

private theorem image_splitProduct :
    splitProduct '' splitProductDomain = {m : Fin 2 → Fin 2 → ℝ | m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0 ∧ m 1 0 ≠ 0} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hdet := det_of_splitProduct p hp.1
    rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.of_apply] at hdet
    simp only [Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [hdet]; exact hp.1
    · rw [splitProduct_eq_entries p hp.1]
      simp only [splitProductEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact mul_ne_zero (right_ne_zero_of_mul hp.1) (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2).ne'
  · rintro m ⟨hdet, h10⟩
    obtain ⟨α, θ, hα, hθ0, hθπ, hs, hc⟩ := exists_line_of_ne_zero (m 1 0) (m 1 1) h10
    obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = m 0 0 * Real.cos θ - m 0 1 * Real.sin θ := ⟨_, rfl⟩
    have hprod : α * A = m 0 0 * m 1 1 - m 0 1 * m 1 0 := by
      linear_combination m 0 0 * hc - m 0 1 * hs + α * hA_def
    have hA : A ≠ 0 := by
      refine right_ne_zero_of_mul (a := α) ?_
      rw [hprod]; exact hdet
    obtain ⟨u, hu⟩ : ∃ u : ℝ, A * u = m 0 0 * Real.sin θ + m 0 1 * Real.cos θ :=
      ⟨(m 0 0 * Real.sin θ + m 0 1 * Real.cos θ) / A, by field_simp⟩
    have e00 : A * Real.cos θ + A * u * Real.sin θ = m 0 0 := by
      linear_combination Real.sin θ * hu + Real.cos θ * hA_def + m 0 0 * Real.cos_sq_add_sin_sq θ
    have e01 : -(A * Real.sin θ) + A * u * Real.cos θ = m 0 1 := by
      linear_combination Real.cos θ * hu + (-Real.sin θ) * hA_def + m 0 1 * Real.cos_sq_add_sin_sq θ
    refine ⟨![![A, α], ![θ, u]], ⟨mul_ne_zero hA hα, hθ0, hθπ⟩, ?_⟩
    rw [splitProduct_eq_entries ![![A, α], ![θ, u]] (mul_ne_zero hA hα)]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp only [splitProductEntries, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one]
    exacts [e00, e01, hs, hc]

private theorem eq_of_splitProductEntries_eq (p q : Fin 2 → Fin 2 → ℝ)
    (hpq : splitProductEntries p = splitProductEntries q) (ha0 : p 0 0 ≠ 0) (hb0 : p 0 1 ≠ 0) (hp0 : 0 < p 1 0)
    (hpπ : p 1 0 < Real.pi) (hq0 : 0 < q 1 0) (hqπ : q 1 0 < Real.pi) : p = q := by
  have h00 :
      p 0 0 * Real.cos (p 1 0) + p 0 0 * p 1 1 * Real.sin (p 1 0) =
      q 0 0 * Real.cos (q 1 0) + q 0 0 * q 1 1 * Real.sin (q 1 0) := by
    simpa [splitProductEntries] using congrFun (congrFun hpq 0) 0
  have h01 :
      -(p 0 0 * Real.sin (p 1 0)) + p 0 0 * p 1 1 * Real.cos (p 1 0) =
      -(q 0 0 * Real.sin (q 1 0)) + q 0 0 * q 1 1 * Real.cos (q 1 0) := by
    simpa [splitProductEntries] using congrFun (congrFun hpq 0) 1
  have h10 :
      p 0 1 * Real.sin (p 1 0) =
      q 0 1 * Real.sin (q 1 0) := by
    simpa [splitProductEntries] using congrFun (congrFun hpq 1) 0
  have h11 :
      p 0 1 * Real.cos (p 1 0) =
      q 0 1 * Real.cos (q 1 0) := by
    simpa [splitProductEntries] using congrFun (congrFun hpq 1) 1
  have hcsp : Real.cos (p 1 0) ^ 2 + Real.sin (p 1 0) ^ 2 = 1 := Real.cos_sq_add_sin_sq (p 1 0)
  have hcsq : Real.cos (q 1 0) ^ 2 + Real.sin (q 1 0) ^ 2 = 1 := Real.cos_sq_add_sin_sq (q 1 0)
  have hsp : 0 < Real.sin (p 1 0) := Real.sin_pos_of_pos_of_lt_pi hp0 hpπ
  have hsq : 0 < Real.sin (q 1 0) := Real.sin_pos_of_pos_of_lt_pi hq0 hqπ
  have hbb : (p 0 1 - q 0 1) * (p 0 1 + q 0 1) = 0 := by
    linear_combination (p 0 1 * Real.sin (p 1 0) + q 0 1 * Real.sin (q 1 0)) * h10 + (Real.cos (p 1 0) * p 0 1 +
      Real.cos (q 1 0) * q 0 1) * h11 + (-p 0 1 ^ 2) * hcsp + (q 0 1 ^ 2) * hcsq
  have hb : p 0 1 = q 0 1 := by
    rcases mul_eq_zero.1 hbb with h1 | h1
    · exact sub_eq_zero.1 h1
    · exfalso
      have h2 : p 0 1 * (Real.sin (p 1 0) + Real.sin (q 1 0)) = 0 := by
        linear_combination (1) * h10 + (Real.sin (q 1 0)) * h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact hb0 h3
      · linarith
  have hc1 : p 0 1 * (Real.cos (p 1 0) - Real.cos (q 1 0)) = 0 := by
    linear_combination (1) * h11 + (-Real.cos (q 1 0)) * hb
  have hc : Real.cos (p 1 0) = Real.cos (q 1 0) := sub_eq_zero.1 ((mul_eq_zero.1 hc1).resolve_left hb0)
  have ht : p 1 0 = q 1 0 := Real.injOn_cos ⟨hp0.le, hpπ.le⟩ ⟨hq0.le, hqπ.le⟩ hc
  have hs : Real.sin (p 1 0) = Real.sin (q 1 0) := by rw [ht]
  have ha : p 0 0 = q 0 0 := by
    linear_combination (Real.cos (p 1 0)) * h00 + (-Real.sin (p 1 0)) * h01 + (-Real.cos (p 1 0) * q 0 0 + q 0 0 *
      q 1 1 * Real.sin (p 1 0)) * hc + (-Real.cos (p 1 0) * q 0 0 * q 1 1 - q 0 0 * Real.sin (p 1 0)) * hs +
      (-p 0 0 + q 0 0) * hcsp
  have hd1 : p 0 0 * (p 1 1 - q 1 1) = 0 := by
    linear_combination (Real.sin (p 1 0)) * h00 + (Real.cos (p 1 0)) * h01 + (-Real.cos (p 1 0) * q 0 0 * q 1 1 -
      q 0 0 * Real.sin (p 1 0)) * hc + (Real.cos (p 1 0) * q 0 0 - q 0 0 * q 1 1 * Real.sin (p 1 0)) * hs +
      (-Real.cos (p 1 0) ^ 2 * q 1 1 - q 1 1 * Real.sin (p 1 0) ^ 2) * ha + (-p 0 0 * p 1 1 + p 0 0 * q 1 1) * hcsp
  have hd : p 1 1 = q 1 1 := sub_eq_zero.1 ((mul_eq_zero.1 hd1).resolve_left ha0)
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

private theorem injOn_splitProduct :
    Set.InjOn splitProduct splitProductDomain := by
  intro p hp q hq hpq
  rw [splitProduct_eq_entries p hp.1, splitProduct_eq_entries q hq.1] at hpq
  exact eq_of_splitProductEntries_eq p q hpq (left_ne_zero_of_mul hp.1) (right_ne_zero_of_mul hp.1) hp.2.1 hp.2.2
    hq.2.1 hq.2.2

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
      (((if h : p 0 0 * p 0 1 ≠ 0 then
            upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) h * (rotation (p 1 0))⁻¹
          else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))
      ((volume.restrict
        {p : Fin 2 → Fin 2 → ℝ | p 0 0 * p 0 1 ≠ 0 ∧ 0 < p 1 0 ∧ p 1 0 < Real.pi}).withDensity
        (fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal |p 0 0 * p 0 1|)) =
      volume.restrict
        {m : Fin 2 → Fin 2 → ℝ | m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0 ∧ m 1 0 ≠ 0} := by
  exact map_chart_eq splitProduct splitProductDomain measurableSet_splitProductDomain
    (fun p hp => differentiableAt_splitProduct p hp.1) injOn_splitProduct (fun p => |p 0 0 * p 0 1|)
    (fun p hp => abs_det_fderiv_splitProduct p hp.1) _
    (ae_eq_of_subset_of_subset_union _ _ image_splitProduct.subset fun m hm =>
      Or.inl (image_splitProduct.symm.subset hm))

end S_AutomorphicForm_GL2Real_map_splitProduct
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_map_splitProduct (solution)
