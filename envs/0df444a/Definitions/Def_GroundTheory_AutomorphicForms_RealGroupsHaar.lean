-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
-- name    : GroundTheory_AutomorphicForms_RealGroupsHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:25.483804+00:00
-- url     : https://prove2.me/theorems/77834dc4-ed62-482f-933b-753832d44bfc
-- title:
--   Real Groups Haar
-- statement:
--   Definitions and structural lemmas for Real Groups Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsHaar.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Matrix Measure
open scoped Matrix.Norms.L2Operator ENNReal Kronecker
section Det
variable {𝕜 : Type*} [Field 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
def vecLinearEquiv : Matrix n n 𝕜 ≃ₗ[𝕜] (n × n → 𝕜) where
  toFun := vec
  invFun v := of fun i j => v (j, i)
  map_add' := vec_add
  map_smul' := vec_smul
  left_inv _ := rfl
  right_inv _ := funext fun _ => rfl
theorem det_mulLeft_matrix (A : Matrix n n 𝕜) :
    LinearMap.det (LinearMap.mulLeft 𝕜 A) = A.det ^ Fintype.card n := by
  have h : (vecLinearEquiv : Matrix n n 𝕜 ≃ₗ[𝕜] (n × n → 𝕜)).toLinearMap ∘ₗ
      LinearMap.mulLeft 𝕜 A ∘ₗ (vecLinearEquiv (n := n)).symm.toLinearMap = toLin' (1 ⊗ₖ A) := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.mulLeft_apply, toLin'_apply]
    show vec (A * vecLinearEquiv.symm v) = _
    rw [vec_mul_eq_mulVec]
    rfl
  rw [← LinearMap.det_conj (LinearMap.mulLeft 𝕜 A) vecLinearEquiv, h, LinearMap.det_toLin',
    det_kronecker, det_one, one_pow, one_mul]
theorem det_mulRight_matrix (A : Matrix n n 𝕜) :
    LinearMap.det (LinearMap.mulRight 𝕜 A) = A.det ^ Fintype.card n := by
  have h : (vecLinearEquiv : Matrix n n 𝕜 ≃ₗ[𝕜] (n × n → 𝕜)).toLinearMap ∘ₗ
      LinearMap.mulRight 𝕜 A ∘ₗ (vecLinearEquiv (n := n)).symm.toLinearMap =
        toLin' (A ⊗ₖ (1 : Matrix n n 𝕜))ᵀ := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.mulRight_apply, toLin'_apply]
    show vec (vecLinearEquiv.symm v * A) = _
    rw [vec_mul_eq_vecMul, mulVec_transpose]
    rfl
  rw [← LinearMap.det_conj (LinearMap.mulRight 𝕜 A) vecLinearEquiv, h, LinearMap.det_toLin',
    det_transpose, det_kronecker, det_one, one_pow, mul_one]
end Det
section General
theorem map_withDensity_eq_of_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ₀ : Measure E)
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) (L : E →ₗ[ℝ] E) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (hmap : Measure.map L μ₀ = c • μ₀) (hρL : ∀ x, ρ (L x) = c * ρ x) :
    Measure.map L (μ₀.withDensity ρ) = μ₀.withDensity ρ := by
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  ext s hs
  rw [Measure.map_apply hLm hs, withDensity_apply _ (hLm hs), withDensity_apply _ hs]
  have key : ∫⁻ y, s.indicator ρ y ∂(Measure.map L μ₀) = ∫⁻ x, s.indicator ρ (L x) ∂μ₀ :=
    lintegral_map (hρ.indicator hs) hLm
  rw [hmap, lintegral_smul_measure, lintegral_indicator hs] at key
  have h2 : (fun x => s.indicator ρ (L x)) = fun x => c * (L ⁻¹' s).indicator ρ x := by
    funext x
    by_cases hx : L x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ L ⁻¹' s from hx), hρL]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ L ⁻¹' s from hx),
        mul_zero]
  rw [h2, lintegral_const_mul _ (hρ.indicator (hLm hs)), lintegral_indicator (hLm hs)] at key
  exact ((ENNReal.mul_right_inj hc0 hcT).1 key).symm
theorem image_val_preimage_mul_left {M : Type*} [Monoid M] (g : Mˣ) (s : Set Mˣ) :
    Units.val '' ((fun h => g * h) ⁻¹' s) = (fun x : M => (g : M) * x) ⁻¹' (Units.val '' s) := by
  ext x
  constructor
  · rintro ⟨h, hs, rfl⟩; exact ⟨g * h, hs, rfl⟩
  · rintro ⟨h', hs, hx⟩
    refine ⟨g⁻¹ * h', by simpa using hs, ?_⟩
    rw [Units.val_mul, hx, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
theorem image_val_preimage_mul_right {M : Type*} [Monoid M] (g : Mˣ) (s : Set Mˣ) :
    Units.val '' ((fun h => h * g) ⁻¹' s) = (fun x : M => x * (g : M)) ⁻¹' (Units.val '' s) := by
  ext x
  constructor
  · rintro ⟨h, hs, rfl⟩; exact ⟨h * g, hs, rfl⟩
  · rintro ⟨h', hs, hx⟩
    refine ⟨h' * g⁻¹, by simpa using hs, ?_⟩
    rw [Units.val_mul, hx, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
end General
section Real
variable {n : Type*} [Fintype n] [DecidableEq n]
noncomputable scoped instance matrixMeasurableSpaceReal : MeasurableSpace (Matrix n n ℝ) := borel _
scoped instance matrixBorelSpaceReal : BorelSpace (Matrix n n ℝ) := ⟨rfl⟩
instance borelSpace_GLReal : BorelSpace (GL n ℝ) :=
  ⟨by
    show MeasurableSpace.comap Units.val (borel (Matrix n n ℝ)) = borel (GL n ℝ)
    rw [Units.isOpenEmbedding_val.isEmbedding.eq_induced, borel_comap]⟩
noncomputable def haarDensityGLReal (x : Matrix n n ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖x.det‖ ^ 1)⁻¹ ^ Fintype.card n)
theorem measurable_haarDensityGLReal : Measurable (haarDensityGLReal (n := n)) :=
  ENNReal.measurable_ofReal.comp
    ((((continuous_id.matrix_det).norm.pow _).measurable.inv).pow_const _)
theorem haarDensityGLReal_mul (A x : Matrix n n ℝ) :
    haarDensityGLReal (A * x) = ENNReal.ofReal ((‖A.det‖ ^ 1)⁻¹ ^ Fintype.card n) *
      haarDensityGLReal x := by
  simp only [haarDensityGLReal, det_mul, norm_mul, mul_pow, mul_inv]
  rw [ENNReal.ofReal_mul (by positivity)]
theorem haarDensityGLReal_mul' (A x : Matrix n n ℝ) :
    haarDensityGLReal (x * A) = ENNReal.ofReal ((‖A.det‖ ^ 1)⁻¹ ^ Fintype.card n) *
      haarDensityGLReal x := by
  rw [← haarDensityGLReal_mul]
  simp only [haarDensityGLReal, det_mul, mul_comm]
theorem map_mulLeft_haarReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] (g : GL n ℝ) :
    Measure.map (LinearMap.mulLeft ℝ (g : Matrix n n ℝ)) μ₀ =
      ENNReal.ofReal ((‖(g : Matrix n n ℝ).det‖ ^ 1)⁻¹ ^ Fintype.card n) • μ₀ := by
  have hd : (g : Matrix n n ℝ).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [map_linearMap_addHaar_eq_smul_addHaar μ₀
    (by rw [det_mulLeft_matrix]; exact pow_ne_zero _ hd), det_mulLeft_matrix, pow_one,
    Real.norm_eq_abs, abs_inv, abs_pow, inv_pow]
theorem map_mulRight_haarReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] (g : GL n ℝ) :
    Measure.map (LinearMap.mulRight ℝ (g : Matrix n n ℝ)) μ₀ =
      ENNReal.ofReal ((‖(g : Matrix n n ℝ).det‖ ^ 1)⁻¹ ^ Fintype.card n) • μ₀ := by
  have hd : (g : Matrix n n ℝ).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [map_linearMap_addHaar_eq_smul_addHaar μ₀
    (by rw [det_mulRight_matrix]; exact pow_ne_zero _ hd), det_mulRight_matrix, pow_one,
    Real.norm_eq_abs, abs_inv, abs_pow, inv_pow]
noncomputable def haarGLReal (μ₀ : Measure (Matrix n n ℝ)) : Measure (GL n ℝ) :=
  Measure.comap Units.val (μ₀.withDensity haarDensityGLReal)
theorem measurableEmbedding_val_GLReal :
    MeasurableEmbedding (Units.val : GL n ℝ → Matrix n n ℝ) :=
  Units.isOpenEmbedding_val.measurableEmbedding
theorem haarGLReal_apply (μ₀ : Measure (Matrix n n ℝ)) (s : Set (GL n ℝ)) :
    haarGLReal μ₀ s = μ₀.withDensity haarDensityGLReal (Units.val '' s) :=
  measurableEmbedding_val_GLReal.comap_apply _ s
theorem haarScaleReal_ne_zero (g : GL n ℝ) :
    ENNReal.ofReal ((‖(g : Matrix n n ℝ).det‖ ^ 1)⁻¹ ^ Fintype.card n) ≠ 0 := by
  have hd : (g : Matrix n n ℝ).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  exact (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (pow_pos (norm_pos_iff.2 hd) _)) _)).ne'
instance isMulLeftInvariant_haarGLReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] :
    (haarGLReal μ₀).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hm : Measurable (fun h : GL n ℝ => g * h) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs, haarGLReal_apply, haarGLReal_apply, image_val_preimage_mul_left]
  have hmeas : MeasurableSet (Units.val '' s) :=
    measurableEmbedding_val_GLReal.measurableSet_image.2 hs
  have := map_withDensity_eq_of_scale μ₀ measurable_haarDensityGLReal (LinearMap.mulLeft ℝ (g : Matrix n n ℝ))
    (haarScaleReal_ne_zero g) ENNReal.ofReal_ne_top (map_mulLeft_haarReal μ₀ g)
    (fun x => haarDensityGLReal_mul _ x)
  have h2 := congrArg (fun m : Measure (Matrix n n ℝ) => m (Units.val '' s)) this
  rw [Measure.map_apply (LinearMap.mulLeft ℝ (g : Matrix n n ℝ)).continuous_of_finiteDimensional.measurable hmeas] at h2
  exact h2
instance isMulRightInvariant_haarGLReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] :
    (haarGLReal μ₀).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hm : Measurable (fun h : GL n ℝ => h * g) :=
    (continuous_id.mul continuous_const).measurable
  rw [Measure.map_apply hm hs, haarGLReal_apply, haarGLReal_apply, image_val_preimage_mul_right]
  have hmeas : MeasurableSet (Units.val '' s) :=
    measurableEmbedding_val_GLReal.measurableSet_image.2 hs
  have := map_withDensity_eq_of_scale μ₀ measurable_haarDensityGLReal (LinearMap.mulRight ℝ (g : Matrix n n ℝ))
    (haarScaleReal_ne_zero g) ENNReal.ofReal_ne_top (map_mulRight_haarReal μ₀ g)
    (fun x => haarDensityGLReal_mul' _ x)
  have h2 := congrArg (fun m : Measure (Matrix n n ℝ) => m (Units.val '' s)) this
  rw [Measure.map_apply (LinearMap.mulRight ℝ (g : Matrix n n ℝ)).continuous_of_finiteDimensional.measurable hmeas] at h2
  exact h2
theorem haarDensityGLReal_val_ne_zero (h : GL n ℝ) : haarDensityGLReal (h : Matrix n n ℝ) ≠ 0 := by
  have := haarScaleReal_ne_zero h
  simpa [haarDensityGLReal] using this
instance isHaarMeasure_haarGLReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] :
    (haarGLReal μ₀).IsHaarMeasure where
  lt_top_of_isCompact := fun K hK => by
    rw [haarGLReal_apply]
    have hK' : IsCompact (Units.val '' K) := hK.image Units.continuous_val
    have hmeas : MeasurableSet (Units.val '' K) := hK'.isClosed.measurableSet
    have hcont : Continuous (fun h : GL n ℝ =>
        (‖(h : Matrix n n ℝ).det‖ ^ 1)⁻¹ ^ Fintype.card n) :=
      (((Units.continuous_val.matrix_det).norm.pow _).inv₀ (fun h => pow_ne_zero _
        (norm_ne_zero_iff.2 ((isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero))).pow _
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    rw [withDensity_apply _ hmeas]
    calc ∫⁻ x in Units.val '' K, haarDensityGLReal x ∂μ₀
        ≤ ∫⁻ _ in Units.val '' K, ENNReal.ofReal C ∂μ₀ := by
          refine setLIntegral_mono' hmeas fun x hx => ?_
          obtain ⟨h, hK, rfl⟩ := hx
          refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
          simpa [Real.norm_eq_abs] using hC h hK
      _ = ENNReal.ofReal C * μ₀ (Units.val '' K) := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK'.measure_lt_top
  map_mul_left_eq_self := (isMulLeftInvariant_haarGLReal μ₀).map_mul_left_eq_self
  open_pos := fun U hU hne => by
    rw [haarGLReal_apply, ne_eq,
      withDensity_apply_eq_zero' measurable_haarDensityGLReal.aemeasurable]
    have e : {x | haarDensityGLReal x ≠ 0} ∩ Units.val '' U = Units.val '' U := by
      refine Set.inter_eq_right.2 ?_
      rintro _ ⟨h, _, rfl⟩
      exact haarDensityGLReal_val_ne_zero h
    rw [e]
    exact (Units.isOpenEmbedding_val.isOpenMap U hU).measure_ne_zero μ₀ (hne.image _)
end Real
section Complex
variable {n : Type*} [Fintype n] [DecidableEq n]
noncomputable scoped instance matrixMeasurableSpaceComplex : MeasurableSpace (Matrix n n ℂ) := borel _
scoped instance matrixBorelSpaceComplex : BorelSpace (Matrix n n ℂ) := ⟨rfl⟩
instance borelSpace_GLComplex : BorelSpace (GL n ℂ) :=
  ⟨by
    show MeasurableSpace.comap Units.val (borel (Matrix n n ℂ)) = borel (GL n ℂ)
    rw [Units.isOpenEmbedding_val.isEmbedding.eq_induced, borel_comap]⟩
noncomputable def haarDensityGLComplex (x : Matrix n n ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖x.det‖ ^ 2)⁻¹ ^ Fintype.card n)
theorem measurable_haarDensityGLComplex : Measurable (haarDensityGLComplex (n := n)) :=
  ENNReal.measurable_ofReal.comp
    ((((continuous_id.matrix_det).norm.pow _).measurable.inv).pow_const _)
theorem haarDensityGLComplex_mul (A x : Matrix n n ℂ) :
    haarDensityGLComplex (A * x) = ENNReal.ofReal ((‖A.det‖ ^ 2)⁻¹ ^ Fintype.card n) *
      haarDensityGLComplex x := by
  simp only [haarDensityGLComplex, det_mul, norm_mul, mul_pow, mul_inv]
  rw [ENNReal.ofReal_mul (by positivity)]
theorem haarDensityGLComplex_mul' (A x : Matrix n n ℂ) :
    haarDensityGLComplex (x * A) = ENNReal.ofReal ((‖A.det‖ ^ 2)⁻¹ ^ Fintype.card n) *
      haarDensityGLComplex x := by
  rw [← haarDensityGLComplex_mul]
  simp only [haarDensityGLComplex, det_mul, mul_comm]
theorem det_restrictScalars_mulLeft (A : Matrix n n ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ A).restrictScalars ℝ) = (‖A.det‖ ^ 2) ^ Fintype.card n := by
  rw [LinearMap.det_restrictScalars, det_mulLeft_matrix, map_pow, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]
theorem det_restrictScalars_mulRight (A : Matrix n n ℂ) :
    LinearMap.det ((LinearMap.mulRight ℂ A).restrictScalars ℝ) = (‖A.det‖ ^ 2) ^ Fintype.card n := by
  rw [LinearMap.det_restrictScalars, det_mulRight_matrix, map_pow, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]
theorem map_mulLeft_haarComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] (g : GL n ℂ) :
    Measure.map ((LinearMap.mulLeft ℂ (g : Matrix n n ℂ)).restrictScalars ℝ) μ₀ =
      ENNReal.ofReal ((‖(g : Matrix n n ℂ).det‖ ^ 2)⁻¹ ^ Fintype.card n) • μ₀ := by
  have hd : (g : Matrix n n ℂ).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [map_linearMap_addHaar_eq_smul_addHaar μ₀
    (by rw [det_restrictScalars_mulLeft]; exact pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 hd))),
    det_restrictScalars_mulLeft, ← inv_pow, abs_pow, abs_inv, abs_pow, abs_norm]
theorem map_mulRight_haarComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] (g : GL n ℂ) :
    Measure.map ((LinearMap.mulRight ℂ (g : Matrix n n ℂ)).restrictScalars ℝ) μ₀ =
      ENNReal.ofReal ((‖(g : Matrix n n ℂ).det‖ ^ 2)⁻¹ ^ Fintype.card n) • μ₀ := by
  have hd : (g : Matrix n n ℂ).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [map_linearMap_addHaar_eq_smul_addHaar μ₀
    (by rw [det_restrictScalars_mulRight]; exact pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 hd))),
    det_restrictScalars_mulRight, ← inv_pow, abs_pow, abs_inv, abs_pow, abs_norm]
noncomputable def haarGLComplex (μ₀ : Measure (Matrix n n ℂ)) : Measure (GL n ℂ) :=
  Measure.comap Units.val (μ₀.withDensity haarDensityGLComplex)
theorem measurableEmbedding_val_GLComplex :
    MeasurableEmbedding (Units.val : GL n ℂ → Matrix n n ℂ) :=
  Units.isOpenEmbedding_val.measurableEmbedding
theorem haarGLComplex_apply (μ₀ : Measure (Matrix n n ℂ)) (s : Set (GL n ℂ)) :
    haarGLComplex μ₀ s = μ₀.withDensity haarDensityGLComplex (Units.val '' s) :=
  measurableEmbedding_val_GLComplex.comap_apply _ s
theorem haarScaleComplex_ne_zero (g : GL n ℂ) :
    ENNReal.ofReal ((‖(g : Matrix n n ℂ).det‖ ^ 2)⁻¹ ^ Fintype.card n) ≠ 0 := by
  have hd : (g : Matrix n n ℂ).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  exact (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (pow_pos (norm_pos_iff.2 hd) _)) _)).ne'
instance isMulLeftInvariant_haarGLComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] :
    (haarGLComplex μ₀).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hm : Measurable (fun h : GL n ℂ => g * h) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs, haarGLComplex_apply, haarGLComplex_apply, image_val_preimage_mul_left]
  have hmeas : MeasurableSet (Units.val '' s) :=
    measurableEmbedding_val_GLComplex.measurableSet_image.2 hs
  have := map_withDensity_eq_of_scale μ₀ measurable_haarDensityGLComplex ((LinearMap.mulLeft ℂ (g : Matrix n n ℂ)).restrictScalars ℝ)
    (haarScaleComplex_ne_zero g) ENNReal.ofReal_ne_top (map_mulLeft_haarComplex μ₀ g)
    (fun x => haarDensityGLComplex_mul _ x)
  have h2 := congrArg (fun m : Measure (Matrix n n ℂ) => m (Units.val '' s)) this
  rw [Measure.map_apply ((LinearMap.mulLeft ℂ (g : Matrix n n ℂ)).restrictScalars ℝ).continuous_of_finiteDimensional.measurable hmeas] at h2
  exact h2
instance isMulRightInvariant_haarGLComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] :
    (haarGLComplex μ₀).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hm : Measurable (fun h : GL n ℂ => h * g) :=
    (continuous_id.mul continuous_const).measurable
  rw [Measure.map_apply hm hs, haarGLComplex_apply, haarGLComplex_apply, image_val_preimage_mul_right]
  have hmeas : MeasurableSet (Units.val '' s) :=
    measurableEmbedding_val_GLComplex.measurableSet_image.2 hs
  have := map_withDensity_eq_of_scale μ₀ measurable_haarDensityGLComplex ((LinearMap.mulRight ℂ (g : Matrix n n ℂ)).restrictScalars ℝ)
    (haarScaleComplex_ne_zero g) ENNReal.ofReal_ne_top (map_mulRight_haarComplex μ₀ g)
    (fun x => haarDensityGLComplex_mul' _ x)
  have h2 := congrArg (fun m : Measure (Matrix n n ℂ) => m (Units.val '' s)) this
  rw [Measure.map_apply ((LinearMap.mulRight ℂ (g : Matrix n n ℂ)).restrictScalars ℝ).continuous_of_finiteDimensional.measurable hmeas] at h2
  exact h2
theorem haarDensityGLComplex_val_ne_zero (h : GL n ℂ) : haarDensityGLComplex (h : Matrix n n ℂ) ≠ 0 := by
  have := haarScaleComplex_ne_zero h
  simpa [haarDensityGLComplex] using this
instance isHaarMeasure_haarGLComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] :
    (haarGLComplex μ₀).IsHaarMeasure where
  lt_top_of_isCompact := fun K hK => by
    rw [haarGLComplex_apply]
    have hK' : IsCompact (Units.val '' K) := hK.image Units.continuous_val
    have hmeas : MeasurableSet (Units.val '' K) := hK'.isClosed.measurableSet
    have hcont : Continuous (fun h : GL n ℂ =>
        (‖(h : Matrix n n ℂ).det‖ ^ 2)⁻¹ ^ Fintype.card n) :=
      (((Units.continuous_val.matrix_det).norm.pow _).inv₀ (fun h => pow_ne_zero _
        (norm_ne_zero_iff.2 ((isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero))).pow _
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    rw [withDensity_apply _ hmeas]
    calc ∫⁻ x in Units.val '' K, haarDensityGLComplex x ∂μ₀
        ≤ ∫⁻ _ in Units.val '' K, ENNReal.ofReal C ∂μ₀ := by
          refine setLIntegral_mono' hmeas fun x hx => ?_
          obtain ⟨h, hK, rfl⟩ := hx
          refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
          simpa [Real.norm_eq_abs] using hC h hK
      _ = ENNReal.ofReal C * μ₀ (Units.val '' K) := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK'.measure_lt_top
  map_mul_left_eq_self := (isMulLeftInvariant_haarGLComplex μ₀).map_mul_left_eq_self
  open_pos := fun U hU hne => by
    rw [haarGLComplex_apply, ne_eq,
      withDensity_apply_eq_zero' measurable_haarDensityGLComplex.aemeasurable]
    have e : {x | haarDensityGLComplex x ≠ 0} ∩ Units.val '' U = Units.val '' U := by
      refine Set.inter_eq_right.2 ?_
      rintro _ ⟨h, _, rfl⟩
      exact haarDensityGLComplex_val_ne_zero h
    rw [e]
    exact (Units.isOpenEmbedding_val.isOpenMap U hU).measure_ne_zero μ₀ (hne.image _)
end Complex
end GroundTheory.Automorphic


