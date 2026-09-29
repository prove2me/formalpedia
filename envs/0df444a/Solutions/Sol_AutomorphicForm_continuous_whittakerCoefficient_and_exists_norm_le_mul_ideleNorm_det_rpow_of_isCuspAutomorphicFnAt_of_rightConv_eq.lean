-- Prove2me | solution 1 for AutomorphicForm.continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/703ab633-29fb-5f00-a7b8-b0c0b3739d06

import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicVolume NumberField.TateGlobal
p2m_open "AutomorphicForm~continuous_unipotentGL2 AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory Topology"
open scoped NNReal ENNReal

noncomputable section

namespace KcWhittakerGrowth

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem continuous_unipotentGL2 : Continuous (unipotentGL2 : AdeleRing (𝓞 K) K → AdelicGL2 (𝓞 K) K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      first | exact continuous_const | exact continuous_id
  · have h : ∀ x : AdeleRing (𝓞 K) K, ((unipotentGL2 x)⁻¹ : AdelicGL2 (𝓞 K) K) = unipotentGL2 (-x) := fun x =>
      inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [unipotentGL2_coe, Matrix.of_apply, Matrix.cons_val'] <;>
      first | exact continuous_const | exact continuous_neg

theorem det_unipotentGL2 (x : AdeleRing (𝓞 K) K) : Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of])

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z ^ 2 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, centralScalar_val, Matrix.det_diagonal, Units.val_pow_eq_pow_val]
  simp

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hval : (Units.val ∘ (centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K)) =
      fun z : (AdeleRing (𝓞 K) K)ˣ => Matrix.diagonal fun _ : Fin 2 => (z : AdeleRing (𝓞 K) K) :=
    funext fun z => centralScalar_val z
  have hinv : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((centralScalar (𝓞 K) K z)⁻¹ : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) =
      fun z => Matrix.diagonal fun _ : Fin 2 => ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) :=
    funext fun z => by rw [← map_inv]; exact centralScalar_val z⁻¹
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · rw [hval]
    exact continuous_matrix fun i j => by
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; exact Units.continuous_val
      · simp only [Matrix.diagonal_apply_ne _ h]; exact continuous_const
  · rw [hinv]
    exact continuous_matrix fun i j => by
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; exact Units.continuous_coe_inv
      · simp only [Matrix.diagonal_apply_ne _ h]; exact continuous_const

theorem globalPoints_scalar (u : Kˣ) :
    globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom u) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [centralScalar_val]
  show algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (u : K)) i j) = _
  rw [Matrix.scalar_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem ideleNorm_det_globalPoints (γ : GL (Fin 2) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ)) = 1 := by
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap K (Matrix.GeneralLinearGroup.det γ)
  unfold ideleNorm
  rw [show globalPoints (𝓞 K) K γ = Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) γ from rfl,
    Matrix.GeneralLinearGroup.map_det]
  rw [show (Units.map ((algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)))
      (Matrix.GeneralLinearGroup.det γ) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) from rfl, h]
  rfl

theorem ideleNorm_pow (x : (AdeleRing (𝓞 K) K)ˣ) (n : ℕ) : ideleNorm K (x ^ n) = ideleNorm K x ^ n := by
  simp only [ideleNorm, map_pow, NNReal.coe_pow]

theorem ideleNorm_det_mem_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    {s : AdelicGL2 (𝓞 K) K} (hs : s ∈ centreCutSiegelSet K c u d₁ d₂) :
    d₁ ^ (∑ w : InfinitePlace K, w.mult) ≤ ideleNorm K (Matrix.GeneralLinearGroup.det s) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det s) ≤ d₂ ^ (∑ w : InfinitePlace K, w.mult) := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K s hs.1, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum]
  have hw := hs.2.2.2
  refine ⟨Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _) fun w _ => ?_,
    Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w s).le _) fun w _ => ?_⟩
  · exact pow_le_pow_left₀ hd₁.le (hw w).1 _
  · exact pow_le_pow_left₀ (archDetNorm_pos w s).le (hw w).2 _

theorem exists_pinch_finset (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ T, m ≤ ideleNorm K (Matrix.GeneralLinearGroup.det x) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det x) ≤ m⁻¹ := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, le_rfl, fun x hx => (Finset.notMem_empty x hx).elim⟩
  | insert a T ha ih =>
    obtain ⟨m, hm0, hm1, hm⟩ := ih
    set N : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det a) with hN
    have hNpos : 0 < N := ideleNorm_pos _
    refine ⟨min m (min N N⁻¹), lt_min hm0 (lt_min hNpos (inv_pos.2 hNpos)), (min_le_left _ _).trans hm1, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · refine ⟨(min_le_right _ _).trans (min_le_left _ _), ?_⟩
      rw [← hN]
      have h1 : min m (min N N⁻¹) ≤ N⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
      have h2 : 0 < min m (min N N⁻¹) := lt_min hm0 (lt_min hNpos (inv_pos.2 hNpos))
      calc N = (N⁻¹)⁻¹ := (inv_inv N).symm
        _ ≤ (min m (min N N⁻¹))⁻¹ := inv_anti₀ h2 h1
    · obtain ⟨h1, h2⟩ := hm x hx
      refine ⟨(min_le_left _ _).trans h1, h2.trans ?_⟩
      exact inv_anti₀ (lt_min hm0 (lt_min hNpos (inv_pos.2 hNpos))) (min_le_left _ _)

theorem exists_pinch_window {c u d₁ d₂ : ℝ} (T : Finset (AdelicGL2 (𝓞 K) K)) (hd₁ : 0 < d₁) (hd : d₁ < d₂) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ s ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂),
      L ≤ ideleNorm K (Matrix.GeneralLinearGroup.det s) ∧ ideleNorm K (Matrix.GeneralLinearGroup.det s) ≤ U := by
  obtain ⟨m, hm0, _, hm⟩ := exists_pinch_finset K T
  have hd₂ : 0 < d₂ := hd₁.trans hd
  refine ⟨d₁ ^ (∑ w : InfinitePlace K, w.mult) * m, d₂ ^ (∑ w : InfinitePlace K, w.mult) * m⁻¹,
    mul_pos (pow_pos hd₁ _) hm0, mul_pos (pow_pos hd₂ _) (inv_pos.2 hm0), fun s hs => ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hs
  obtain ⟨x, hx, s₁, hs₁, rfl⟩ := hs
  obtain ⟨h1, h2⟩ := ideleNorm_det_mem_of_mem_centreCutSiegelSet K hd₁ hd hs₁
  obtain ⟨h3, h4⟩ := hm x hx
  rw [map_mul, ideleNorm_mul]
  exact ⟨mul_le_mul h1 h3 hm0.le (ideleNorm_pos _).le,
    mul_le_mul h2 h4 (ideleNorm_pos _).le (pow_nonneg hd₂.le _)⟩

theorem exists_norm_le_mul_ideleNorm_det_rpow
    (D : Set (AdelicGL2 (𝓞 K) K)) (hcov : CoversModCentre K D)
    (L U : ℝ) (hL : 0 < L) (_hU : 0 < U)
    (hLU : ∀ s ∈ D, L ≤ ideleNorm K (Matrix.GeneralLinearGroup.det s) ∧ ideleNorm K (Matrix.GeneralLinearGroup.det s) ≤ U)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (C : ℝ) (hC : ∀ s ∈ D, ‖φ s‖ ≤ C)
    (hleft : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      φ (centralScalar (𝓞 K) K z * g) = ((χ z : ℂˣ) : ℂ) * φ g)
    (σ : ℝ) (hσ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((χ z : ℂˣ) : ℂ)‖ = ideleNorm K z ^ σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g : AdelicGL2 (𝓞 K) K,
      ‖φ g‖ ≤ M * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (σ / 2) := by

  have hC0 : 0 ≤ C := by
    obtain ⟨γ, z, h1⟩ := hcov 1
    exact (norm_nonneg _).trans (hC _ h1)
  set e : ℝ := -(σ / 2) with he
  refine ⟨C * max (L ^ e) (U ^ e), mul_nonneg hC0 (le_max_of_le_left (Real.rpow_nonneg hL.le _)), fun g => ?_⟩
  obtain ⟨γ, z, hs⟩ := hcov g
  set s : AdelicGL2 (𝓞 K) K := globalPoints (𝓞 K) K γ * g * centralScalar (𝓞 K) K z with hsdef
  set N : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det g) with hN
  set q : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det s) with hq
  have hNpos : 0 < N := ideleNorm_pos _
  have hzpos : 0 < ideleNorm K z := ideleNorm_pos _

  have hφs : φ s = ((χ z : ℂˣ) : ℂ) * φ g := by
    rw [hsdef, mul_assoc, hleft, mul_centralScalar_comm, hcentral]

  have hqN : q = N * ideleNorm K z ^ 2 := by
    rw [hq, hsdef, map_mul, map_mul, ideleNorm_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul,
      det_centralScalar, ideleNorm_pow]
  have hz2 : ideleNorm K z ^ (2 : ℕ) = q / N := by
    rw [hqN]; field_simp

  have h1 : ‖φ g‖ = ‖φ s‖ * (ideleNorm K z ^ σ)⁻¹ := by
    rw [hφs, norm_mul, hσ]
    have : ideleNorm K z ^ σ ≠ 0 := (Real.rpow_pos_of_pos hzpos σ).ne'
    field_simp
  have h2 : (ideleNorm K z ^ σ)⁻¹ = (q / N) ^ e := by
    rw [← hz2, he, ← Real.rpow_natCast, ← Real.rpow_mul hzpos.le, ← Real.rpow_neg hzpos.le]
    congr 1
    push_cast
    ring
  have hqmem := hLU s hs
  have hqpos : 0 < q := hL.trans_le hqmem.1
  have h3 : (q / N) ^ e = q ^ e * N ^ (σ / 2) := by
    rw [Real.div_rpow hqpos.le hNpos.le, he, Real.rpow_neg hNpos.le, div_inv_eq_mul]
  have h4 : q ^ e ≤ max (L ^ e) (U ^ e) := by
    rcases le_total 0 e with he0 | he0
    · exact le_max_of_le_right (Real.rpow_le_rpow hqpos.le hqmem.2 he0)
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos hL hqmem.1 he0)
  rw [h1, h2, h3]
  calc ‖φ s‖ * (q ^ e * N ^ (σ / 2)) ≤ C * (max (L ^ e) (U ^ e) * N ^ (σ / 2)) :=
        mul_le_mul (hC s hs) (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hNpos.le _)) (by positivity) hC0
    _ = C * max (L ^ e) (U ^ e) * N ^ (σ / 2) := by ring

def liftChar {Z : Subgroup (AdeleRing (𝓞 K) K)ˣ} (hZ : Z = ⊤) (χ : Z →* ℂˣ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ where
  toFun z := χ ⟨z, hZ ▸ Subgroup.mem_top z⟩
  map_one' := by
    rw [show (⟨1, hZ ▸ Subgroup.mem_top 1⟩ : Z) = 1 from rfl, map_one]
  map_mul' a b := by
    rw [← map_mul]; rfl

theorem liftChar_apply {Z : Subgroup (AdeleRing (𝓞 K) K)ˣ} (hZ : Z = ⊤) (χ : Z →* ℂˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    liftChar K hZ χ z = χ ⟨z, hZ ▸ Subgroup.mem_top z⟩ := rfl

theorem isIdeleClassChar_and_continuous
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hφ0 : φ ≠ 0)
    (hleft : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      φ (centralScalar (𝓞 K) K z * g) = ((χ z : ℂˣ) : ℂ) * φ g) :
    AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ ∧ Continuous χ := by
  obtain ⟨g₁, hg₁⟩ := Function.ne_iff.1 hφ0
  have hg₁' : φ g₁ ≠ 0 := hg₁
  refine ⟨fun u => ?_, ?_⟩
  · have h := hcentral (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom u) g₁
    rw [← globalPoints_scalar, hleft] at h
    have h1 : ((χ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom u) : ℂˣ) : ℂ) = 1 :=
      (mul_eq_right₀ hg₁').1 h.symm
    exact Units.val_eq_one.1 h1
  ·
    have hval : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((χ z : ℂˣ) : ℂ) = φ (centralScalar (𝓞 K) K z * g₁) / φ g₁ := by
      intro z; rw [hcentral, mul_div_cancel_right₀ _ hg₁']
    have hc1 : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ) := by
      simp_rw [hval]
      exact (hcont.comp ((continuous_centralScalar K).mul continuous_const)).div_const _
    refine Units.continuous_iff.2 ⟨hc1, ?_⟩
    have : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((χ z⁻¹ : ℂˣ) : ℂ) := by
      funext z; rw [map_inv]
    rw [this]
    exact hc1.comp continuous_inv

theorem continuous_whittaker_integral [SecondCountableTopology (AdelicGL2 (𝓞 K) K)]
    (ν : Measure (AdeleRing (𝓞 K) K)) [IsFiniteMeasure ν]
    (B : Set (AdeleRing (𝓞 K) K)) (hB : ∃ C, IsCompact C ∧ B ⊆ C) (hνB : ∀ᵐ x ∂ν, x ∈ B)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψc : Continuous ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1) (a : AdeleRing (𝓞 K) K) :
    Continuous fun g : AdelicGL2 (𝓞 K) K => ∫ x, φ (unipotentGL2 x * g) * ψ (-(a * x)) ∂ν := by
  obtain ⟨C, hCc, hBC⟩ := hB
  have hF : ∀ g : AdelicGL2 (𝓞 K) K, Continuous fun x : AdeleRing (𝓞 K) K => φ (unipotentGL2 x * g) * ψ (-(a * x)) :=
    fun g => (hcont.comp ((continuous_unipotentGL2 K).mul continuous_const)).mul
      (hψc.comp ((continuous_const.mul continuous_id).neg))
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨V, hVc, hVn⟩ := exists_compact_mem_nhds g₀

  have hcompact : IsCompact ((fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K => unipotentGL2 p.1 * p.2) '' (C ×ˢ V)) :=
    (hCc.prod hVc).image (((continuous_unipotentGL2 K).comp continuous_fst).mul continuous_snd)
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun g => (hF g).aestronglyMeasurable
  · filter_upwards [hVn] with g hg
    filter_upwards [hνB] with x hx
    rw [norm_mul, hψ1, mul_one]
    exact hM _ ⟨(x, g), ⟨hBC hx, hg⟩, rfl⟩
  · exact Filter.Eventually.of_forall fun x =>
      ((hcont.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt

theorem norm_whittaker_integral_le (ν : Measure (AdeleRing (𝓞 K) K)) [IsProbabilityMeasure ν]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (M r : ℝ)
    (hφ : ∀ g : AdelicGL2 (𝓞 K) K, ‖φ g‖ ≤ M * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ r)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ1 : ∀ x, ‖ψ x‖ = 1) (a : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    ‖∫ x, φ (unipotentGL2 x * g) * ψ (-(a * x)) ∂ν‖ ≤ M * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ r := by
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x : AdeleRing (𝓞 K) K => φ (unipotentGL2 x * g) * ψ (-(a * x)))
    (C := M * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ r)
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul, hψ1, mul_one]
      have := hφ (unipotentGL2 x * g)
      rwa [map_mul, det_unipotentGL2, one_mul] at this)
  rwa [probReal_univ, mul_one] at h

abbrev wpins (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

theorem main [SecondCountableTopology (AdelicGL2 (𝓞 K) K)]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (wpins K c u d₁ d₂ T).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K (wpins K c u d₁ d₂ T) χ φ)
    (hcont : Continuous φ)
    (hsmooth : ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K f ∧ rightConv K φ f = φ)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψc : Continuous ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1) (α : K) :
    Continuous (whittakerCoefficient K (wpins K c u d₁ d₂ T) ψ φ α) ∧
    ∃ M r : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (wpins K c u d₁ d₂ T) ψ φ α g‖ ≤
        M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ r := by

  haveI : IsProbabilityMeasure (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K) (adelicBox K)) :=
    isProbabilityMeasure_cond_adelicBox K
  have hνB : ∀ᵐ x ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K) (adelicBox K)), x ∈ adelicBox K :=
    ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox K)
  have hWc : whittakerCoefficient K (wpins K c u d₁ d₂ T) ψ φ α =
      fun g => ∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K) (adelicBox K)) := rfl
  refine ⟨?_, ?_⟩
  · rw [hWc]
    exact continuous_whittaker_integral K _ (adelicBox K) (exists_isCompact_adelicBox_subset K) hνB φ hcont ψ hψc hψ1 _
  ·
    by_cases hφ0 : φ = 0
    · refine ⟨0, 0, fun g => ?_⟩
      subst hφ0
      rw [hWc]
      simp

    obtain ⟨f, hf, hconv⟩ := hsmooth
    have hbdd : IsBoundedOnSiegelWindows K φ := by
      have h := AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
        K c u d₁ d₂ T hd hcov χ φ hφ hcont f hf
      rwa [hconv] at h
    obtain ⟨CD, hCD⟩ := hbdd c u d₁ d₂ T hc hd₁

    have hLs : IsLsXiFunction (𝓞 K) K (wpins K c u d₁ d₂ T).Z χ φ :=
      ((AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (wpins K c u d₁ d₂ T).μ (wpins K c u d₁ d₂ T).Z χ
        (wpins K c u d₁ d₂ T).D φ).1 hφ.1).1
    have hZ : (wpins K c u d₁ d₂ T).Z = ⊤ := rfl
    have hcentral : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        φ (centralScalar (𝓞 K) K z * g) = ((liftChar K hZ χ z : ℂˣ) : ℂ) * φ g := fun z g =>
      hLs.central_transform ⟨z, hZ ▸ Subgroup.mem_top z⟩ g
    obtain ⟨hclass, hχc⟩ := isIdeleClassChar_and_continuous K φ hcont hφ0 hLs.left_invariant (liftChar K hZ χ) hcentral
    obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K (liftChar K hZ χ) hclass hχc

    obtain ⟨L, U, hL, hU, hLU⟩ := exists_pinch_window K (c := c) (u := u) T hd₁ hd
    obtain ⟨M, _, hM⟩ := exists_norm_le_mul_ideleNorm_det_rpow K _ hcov L U hL hU hLU φ CD hCD hLs.left_invariant
      (liftChar K hZ χ) hcentral σ hσ
    refine ⟨M, σ / 2, fun g => ?_⟩
    rw [hWc]
    exact norm_whittaker_integral_le K _ φ M (σ / 2) hM ψ hψ1 _ g

end KcWhittakerGrowth

open KcWhittakerGrowth

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem solution
    (K : Type) [Field K] [NumberField K] [SecondCountableTopology (AdelicGL2 (𝓞 K) K)]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (hsmooth : ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K f ∧ rightConv K φ f = φ)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψc : Continuous ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1) (α : K) :
    Continuous (whittakerCoefficient K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ψ φ α) ∧
    ∃ M r : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ψ φ α g‖ ≤
        M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ r :=
  KcWhittakerGrowth.main K c u d₁ d₂ T hc hd₁ hd hcov χ φ hφ hcont hsmooth ψ hψc hψ1 α

end
end S_AutomorphicForm_continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq
end P2MW
export P2MW.S_AutomorphicForm_continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq (solution)
