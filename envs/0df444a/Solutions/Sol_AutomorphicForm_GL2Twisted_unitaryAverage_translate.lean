-- Prove2me | solution 1 for AutomorphicForm.GL2Twisted.unitaryAverage_translate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ae5d9e12-34b6-5828-b19b-93b14d74281a

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Twisted_unitaryAverage_translate

set_option autoImplicit false

open AutomorphicForm.GL2Twisted

open MeasureTheory

noncomputable section

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

end

open UnitaryChart in

theorem solution (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F)
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

end S_AutomorphicForm_GL2Twisted_unitaryAverage_translate
end P2MW
export P2MW.S_AutomorphicForm_GL2Twisted_unitaryAverage_translate (solution)
