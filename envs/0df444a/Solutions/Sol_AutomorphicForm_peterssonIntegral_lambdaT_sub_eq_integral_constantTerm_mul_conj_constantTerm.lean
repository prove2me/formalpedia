-- Prove2me | solution 1 for AutomorphicForm.peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/98bc62d3-a55e-5e1a-b7e8-9e0582a843fe

import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory

namespace AutomorphicForm
p2m_export "AutomorphicForm" "highSet mem_highSet_iff lambdaT unipotentGL2 constantTermIntegrand constantTerm constantTerm_const rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent AdelicGL2 globalPoints peterssonIntegral WindowedSiegel.centreCutSiegelSet continuous_unipotentGL2 borelSubgroup exists_isFundamentalDomain_globalPoints_range ideleNorm_det_globalPoints isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul"
p2m_open "AutomorphicForm"

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

private theorem lambdaT_mul_conj_lambdaT_sub_lambdaT_mul_conj_lambdaT (μ : Measure Q) (u : Q → G) (H : G → ℝ)
    {T T' : ℝ} (hTT' : T ≤ T') (φ ψ : G → ℂ) (g : G) :
    lambdaT μ u H T' φ g * (starRingEnd ℂ) (lambdaT μ u H T' ψ g) -
        lambdaT μ u H T φ g * (starRingEnd ℂ) (lambdaT μ u H T ψ g) =
      (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (H g) *
        (φ g * (starRingEnd ℂ) (constantTerm μ u ψ g) +
          constantTerm μ u φ g * (starRingEnd ℂ) (ψ g) -
          constantTerm μ u φ g * (starRingEnd ℂ) (constantTerm μ u ψ g)) := by
  classical
  simp only [lambdaT, Set.indicator_apply, mem_highSet_iff, Set.mem_Ioc]
  by_cases hT : T < H g
  · by_cases hT' : T' < H g
    · simp [hT, hT', not_le.2 hT', map_sub]
    · simp [hT, hT', not_lt.1 hT', map_sub]
      ring
  · have hT'' : ¬ T' < H g := fun h => hT (lt_of_le_of_lt hTT' h)
    simp [hT, hT'']

end AutomorphicForm

open MeasureTheory

namespace AutomorphicForm
p2m_export "AutomorphicForm" "highSet mem_highSet_iff lambdaT unipotentGL2 constantTermIntegrand constantTerm constantTerm_const rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent AdelicGL2 globalPoints peterssonIntegral WindowedSiegel.centreCutSiegelSet continuous_unipotentGL2 borelSubgroup exists_isFundamentalDomain_globalPoints_range ideleNorm_det_globalPoints isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul"
p2m_open "AutomorphicForm"

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

private theorem lambdaT_eq_lambdaT_add_shell_mul_constantTerm (μ : Measure Q) (u : Q → G) (H : G → ℝ)
    {T₁ T : ℝ} (hT : T₁ ≤ T) (φ : G → ℂ) :
    lambdaT μ u H T φ = lambdaT μ u H T₁ φ +
      fun g => (Set.Ioc T₁ T).indicator (fun _ => (1 : ℂ)) (H g) * constantTerm μ u φ g := by
  classical
  funext g
  simp only [lambdaT, Pi.add_apply, Set.indicator_apply, mem_highSet_iff, Set.mem_Ioc]
  by_cases h₁ : T₁ < H g
  · by_cases h₂ : T < H g
    · rw [if_pos h₂, if_pos h₁, if_neg fun h => not_le.2 h₂ h.2]
      ring
    · rw [if_neg h₂, if_pos h₁, if_pos ⟨h₁, not_lt.1 h₂⟩]
      ring
  · have h₂ : ¬ T < H g := fun h => h₁ (lt_of_le_of_lt hT h)
    rw [if_neg h₂, if_neg h₁, if_neg fun h => h₁ h.1]
    ring

private theorem measurable_lambdaT_of_continuous [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure Q) (u : Q → G) {H : G → ℝ} {T : ℝ}
    (hH : MeasurableSet (highSet H T)) {φ : G → ℂ} (hφ : Continuous φ)
    (hN : Continuous (constantTerm μ u φ)) : Measurable (lambdaT μ u H T φ) :=
  hφ.measurable.sub (hN.measurable.indicator hH)

end AutomorphicForm

p2m_open "NumberField NumberField.AdelicLevel AutomorphicForm.WindowedSiegel P2MW.S_AutomorphicForm_peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm.AutomorphicForm.WindowedSiegel NumberField.AdelicHeight"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "highSet mem_highSet_iff lambdaT unipotentGL2 constantTermIntegrand constantTerm constantTerm_const rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent AdelicGL2 globalPoints peterssonIntegral WindowedSiegel.centreCutSiegelSet continuous_unipotentGL2 borelSubgroup exists_isFundamentalDomain_globalPoints_range ideleNorm_det_globalPoints isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul"
p2m_open "AutomorphicForm"

section Generic

variable {A B : Type*} [CommRing A] [CommRing B]

private theorem glMap_unipotentGL2 (f : A →+* B) (x : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2]

end Generic

section LocalInvariance

variable {K : Type*} [NormedField K]

private theorem det_coe_unipotentGL2_mul (y : K) (h : GL (Fin 2) K) :
    ((unipotentGL2 y * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      (h : Matrix (Fin 2) (Fin 2) K).det := by
  rw [Units.val_mul, Matrix.det_mul]
  simp [unipotentGL2, Matrix.det_fin_two_of]

private theorem localHeight_unipotentGL2_mul (y : K) (h : GL (Fin 2) K) :
    localHeight (unipotentGL2 y * h) = localHeight h := by
  have hrow : rowNormSq ((unipotentGL2 y * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      rowNormSq (h : Matrix (Fin 2) (Fin 2) K) := by
    simp [rowNormSq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2]
  unfold localHeight
  rw [det_coe_unipotentGL2_mul, hrow]

private theorem finLocalHeight_unipotentGL2_mul (y : K) (h : GL (Fin 2) K) :
    finLocalHeight (unipotentGL2 y * h) = finLocalHeight h := by
  have hrow : rowMaxNorm ((unipotentGL2 y * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      rowMaxNorm (h : Matrix (Fin 2) (Fin 2) K) := by
    simp [rowMaxNorm, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2]
  unfold finLocalHeight
  rw [det_coe_unipotentGL2_mul, hrow]

end LocalInvariance

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem archHeight_glArch_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F (unipotentGL2 x * g)) = archHeight F (glArch (𝓞 F) F g) := by
  unfold archHeight
  refine Finset.prod_congr rfl fun w _ => ?_
  have h1 : glArch (𝓞 F) F (unipotentGL2 x) = unipotentGL2 _ := glMap_unipotentGL2 _ x
  have h2 : ∀ y, archComponent F w (unipotentGL2 y) = unipotentGL2 _ :=
    fun y => glMap_unipotentGL2 _ y
  rw [map_mul, h1, map_mul, h2, localHeight_unipotentGL2_mul]

private theorem finHeight_glFin_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    finHeight F (glFin (𝓞 F) F (unipotentGL2 x * g)) = finHeight F (glFin (𝓞 F) F g) := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  have h1 : glFin (𝓞 F) F (unipotentGL2 x) = unipotentGL2 _ := glMap_unipotentGL2 _ x
  have h2 : ∀ y, finComponent (𝓞 F) F v (unipotentGL2 y) = unipotentGL2 _ :=
    fun y => glMap_unipotentGL2 _ y
  rw [map_mul, h1, map_mul, h2, finLocalHeight_unipotentGL2_mul]

private theorem adelicHeight_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (unipotentGL2 x * g) = adelicHeight F g := by
  unfold adelicHeight
  rw [archHeight_glArch_unipotentGL2_mul, finHeight_glFin_unipotentGL2_mul]

end Adelic

end AutomorphicForm

open MeasureTheory NumberField NumberField.AdelicBox Filter Topology
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "highSet mem_highSet_iff lambdaT unipotentGL2 constantTermIntegrand constantTerm constantTerm_const rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent AdelicGL2 globalPoints peterssonIntegral WindowedSiegel.centreCutSiegelSet continuous_unipotentGL2 borelSubgroup exists_isFundamentalDomain_globalPoints_range ideleNorm_det_globalPoints isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem continuous_unipotentGL2_fst_mul_snd {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) :
    Continuous fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F => φ (unipotentGL2 p.1 * p.2) :=
  hφ.comp (((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).comp continuous_fst).mul
    continuous_snd)

private theorem continuous_unipotentGL2_mul_const {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (g : AdelicGL2 (𝓞 F) F) : Continuous fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g) :=
  hφ.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul continuous_const)

private theorem integrable_constantTermIntegrand_adelicBox {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (constantTermIntegrand (fun x : AdeleRing (𝓞 F) F => unipotentGL2 x) φ g)
      ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F]) := by
  haveI : IsProbabilityMeasure ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F]) :=
    isProbabilityMeasure_cond_adelicBox F
  obtain ⟨K, hK, hboxK⟩ := exists_isCompact_adelicBox_subset F
  have hcont := continuous_unipotentGL2_mul_const F hφ g
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hbox : ∀ᵐ q ∂(AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F], q ∈ adelicBox F :=
    ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)
  exact (integrable_const C).mono' hcont.aestronglyMeasurable
    (hbox.mono fun q hq => hC q (hboxK hq))

private theorem exists_mem_nhds_forall_dist_lt_of_continuous_prod {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (Ψ : X → Y → ℂ) (hΨ : Continuous fun p : X × Y => Ψ p.1 p.2) (y₀ : Y)
    {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ 𝓝 y₀, ∀ y ∈ V, ∀ x ∈ K, dist (Ψ x y) (Ψ x y₀) < ε := by
  have h₀ : Continuous fun p : X × Y => Ψ p.1 y₀ := hΨ.comp (continuous_fst.prodMk continuous_const)
  have hWopen : IsOpen {p : X × Y | dist (Ψ p.1 p.2) (Ψ p.1 y₀) < ε} :=
    isOpen_lt (hΨ.dist h₀) continuous_const
  have hsub : K ×ˢ ({y₀} : Set Y) ⊆ {p : X × Y | dist (Ψ p.1 p.2) (Ψ p.1 y₀) < ε} := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    have hy' : y = y₀ := Set.mem_singleton_iff.1 hy
    rw [hy']
    show dist (Ψ x y₀) (Ψ x y₀) < ε
    rw [dist_self]
    exact hε
  have h := generalized_tube_lemma hK isCompact_singleton hWopen hsub
  obtain ⟨U, V, -, hVopen, hKU, hy₀V, hUV⟩ := h
  exact ⟨V, hVopen.mem_nhds (hy₀V (Set.mem_singleton y₀)),
    fun y hy x hx => hUV (Set.mk_mem_prod (hKU hx) hy)⟩

private theorem exists_mem_nhds_forall_dist_lt {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (g₀ : AdelicGL2 (𝓞 F) F) {ε : ℝ} (hε : 0 < ε) {K : Set (AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    ∃ V ∈ 𝓝 g₀, ∀ g ∈ V, ∀ q ∈ K,
      dist (φ (unipotentGL2 q * g)) (φ (unipotentGL2 q * g₀)) < ε :=
  exists_mem_nhds_forall_dist_lt_of_continuous_prod
    (fun q : AdeleRing (𝓞 F) F => fun g : AdelicGL2 (𝓞 F) F => φ (unipotentGL2 q * g))
    (continuous_unipotentGL2_fst_mul_snd F hφ) g₀ hK hε

private theorem continuous_constantTerm_adelicBox {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) :
    Continuous (constantTerm ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F])
      (fun x : AdeleRing (𝓞 F) F => unipotentGL2 x) φ) := by
  haveI : IsProbabilityMeasure ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F]) :=
    isProbabilityMeasure_cond_adelicBox F
  obtain ⟨K, hK, hboxK⟩ := exists_isCompact_adelicBox_subset F
  have hbox : ∀ᵐ q ∂(AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F], q ∈ adelicBox F :=
    ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨V, hV, hVε⟩ := exists_mem_nhds_forall_dist_lt F hφ g₀ (half_pos hε) hK
  filter_upwards [hV] with g hg
  have hdiff : ∀ᵐ q ∂(AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F],
      ‖constantTermIntegrand (fun x : AdeleRing (𝓞 F) F => unipotentGL2 x) φ g q -
          constantTermIntegrand (fun x : AdeleRing (𝓞 F) F => unipotentGL2 x) φ g₀ q‖ ≤ ε / 2 := by
    refine hbox.mono fun q hq => ?_
    have h := hVε g hg q (hboxK hq)
    rw [dist_eq_norm] at h
    exact h.le
  rw [dist_eq_norm]
  simp only [constantTerm]
  rw [← integral_sub (integrable_constantTermIntegrand_adelicBox F hφ g)
    (integrable_constantTermIntegrand_adelicBox F hφ g₀)]
  calc ‖∫ q, (constantTermIntegrand (fun x : AdeleRing (𝓞 F) F => unipotentGL2 x) φ g q -
          constantTermIntegrand (fun x : AdeleRing (𝓞 F) F => unipotentGL2 x) φ g₀ q)
          ∂(AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F]‖
      ≤ ε / 2 * ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F]).real Set.univ :=
        norm_integral_le_of_norm_le_const hdiff
    _ = ε / 2 := by simp
    _ < ε := half_lt_self hε

end AutomorphicForm

open NumberField NumberField.AdelicLevel NumberField.AdelicHeight NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.AdelicHaar MeasureTheory

namespace AutomorphicForm
p2m_export "AutomorphicForm" "highSet mem_highSet_iff lambdaT unipotentGL2 constantTermIntegrand constantTerm constantTerm_const rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent AdelicGL2 globalPoints peterssonIntegral WindowedSiegel.centreCutSiegelSet continuous_unipotentGL2 borelSubgroup exists_isFundamentalDomain_globalPoints_range ideleNorm_det_globalPoints isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul"
namespace WindowedSiegel
p2m_export "AutomorphicForm.WindowedSiegel" "rowNormSq localHeight archHeight localHeight_pos centreCutSiegelSet mem_centreCutSiegelSet_iff isCompact_centreCutSiegelSet_inter_heightCap exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet"
p2m_open "AutomorphicForm.WindowedSiegel AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem localHeight_le_of_mem_centreCutSiegelSet_of_archHeight_le {c u d₁ d₂ : ℝ} (hc : 0 < c)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂) {M : ℝ}
    (hM : archHeight F (glArch (𝓞 F) F g) ≤ M) (w : InfinitePlace F) :
    localHeight (archComponent F w (glArch (𝓞 F) F g))
      ≤ max 1 (M / (min 1 c) ^ (∑ v : InfinitePlace F, v.mult)) := by
  classical
  set m : ℝ := min 1 c with hm_def
  have hm0 : 0 < m := lt_min one_pos hc
  have hm1 : m ≤ 1 := min_le_left _ _
  set S : ℕ := ∑ v : InfinitePlace F, v.mult with hS_def
  set f : InfinitePlace F → ℝ :=
    fun v => localHeight (archComponent F v (glArch (𝓞 F) F g)) ^ v.mult with hf_def
  have hfloor : ∀ v : InfinitePlace F, m ≤ localHeight (archComponent F v (glArch (𝓞 F) F g)) :=
    fun v => (min_le_right _ _).trans ((mem_centreCutSiegelSet_iff.1 hg).2.1 v)
  have hsplit : f w * ∏ v ∈ Finset.univ.erase w, f v = archHeight F (glArch (𝓞 F) F g) := by
    unfold archHeight
    exact Finset.mul_prod_erase Finset.univ f (Finset.mem_univ w)
  have hrest : m ^ S ≤ ∏ v ∈ Finset.univ.erase w, f v := by
    calc m ^ S ≤ m ^ (∑ v ∈ Finset.univ.erase w, v.mult) :=
          pow_le_pow_of_le_one hm0.le hm1
            (Finset.sum_le_sum_of_subset (Finset.erase_subset w Finset.univ))
      _ = ∏ v ∈ Finset.univ.erase w, m ^ v.mult := (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ v ∈ Finset.univ.erase w, f v :=
          Finset.prod_le_prod (fun v _ => pow_nonneg hm0.le _)
            (fun v _ => pow_le_pow_left₀ hm0.le (hfloor v) _)
  have hfw : f w ≤ M / m ^ S := by
    rw [le_div_iff₀ (pow_pos hm0 S)]
    calc f w * m ^ S ≤ f w * ∏ v ∈ Finset.univ.erase w, f v :=
          mul_le_mul_of_nonneg_left hrest (pow_nonneg (localHeight_pos _).le _)
      _ = archHeight F (glArch (𝓞 F) F g) := hsplit
      _ ≤ M := hM
  by_cases h1 : localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ 1
  · exact h1.trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    exact (le_self_pow₀ (not_le.1 h1).le InfinitePlace.mult_ne_zero).trans hfw

private theorem exists_isCompact_inter_adelicHeight_le_subset {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁)
    {Tc : Set (AdelicGL2 (𝓞 F) F)} (hTc : IsCompact Tc) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet F c u d₁ d₂) (M : ℝ) :
    ∃ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C ∧ Φ₀ ∩ {g | adelicHeight F g ≤ M} ⊆ C := by
  obtain ⟨κ, _, hκ, hdist⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F Tc hTc
  set Cap : ℝ := max 1 (M / κ / (min 1 c) ^ (∑ v : InfinitePlace F, v.mult)) with hCap_def
  have hC₁ : IsCompact (centreCutSiegelSet F c u d₁ d₂ ∩
      {g | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ Cap}) :=
    isCompact_centreCutSiegelSet_inter_heightCap F hc hd₁
  refine ⟨(fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * p.2) ''
      ((centreCutSiegelSet F c u d₁ d₂ ∩
        {g | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ Cap})
        ×ˢ Tc), (hC₁.prod hTc).image continuous_mul, ?_⟩
  rintro x ⟨hxΦ, hxM⟩
  obtain ⟨y, hy, g, hg, rfl⟩ := Set.mem_iUnion₂.1 (hΦ₀S hxΦ)
  have hxM' : adelicHeight F (g * y) ≤ M := hxM
  have hgM : adelicHeight F g ≤ M / κ := by
    rw [le_div_iff₀ hκ, mul_comm]
    exact (hdist g y hy).1.trans hxM'
  have harch : archHeight F (glArch (𝓞 F) F g) ≤ M / κ := by
    rw [← adelicHeight_eq_archHeight_of_mem (mem_centreCutSiegelSet_iff.1 hg).1]
    exact hgM
  exact ⟨(g, y), ⟨⟨hg, fun w =>
    localHeight_le_of_mem_centreCutSiegelSet_of_archHeight_le F hc hg harch w⟩, hy⟩, rfl⟩

private theorem exists_pos_subset_iUnion_image_mul_centreCutSiegelSet_of_ideleNorm_det_mem_Icc
    {c u d₁ d₂ α β : ℝ} (hα : 0 < α) {Tc : Set (AdelicGL2 (𝓞 F) F)} (hTc : IsCompact Tc)
    {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet F c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) :
    ∃ d₁' : ℝ, 0 < d₁' ∧ Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet F c u d₁' d₂ := by
  classical
  obtain ⟨Y₀, hY₀⟩ := hTc.exists_bound_of_continuousOn (continuous_ideleNorm_det F).continuousOn
  set Y : ℝ := max Y₀ 1 with hY_def
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hY : ∀ y ∈ Tc, ideleNorm F (Matrix.GeneralLinearGroup.det y) ≤ Y := fun y hy =>
    (Real.le_norm_self _).trans ((hY₀ y hy).trans (le_max_left _ _))
  set S : ℕ := ∑ v : InfinitePlace F, v.mult with hS_def
  set D : ℝ := max 1 d₂ with hD_def
  have hD1 : (1 : ℝ) ≤ D := le_max_left _ _
  have hDS : 0 < D ^ S := pow_pos (lt_of_lt_of_le one_pos hD1) S
  set δ : ℝ := min 1 (α / Y / D ^ S) with hδ_def
  have hδ : 0 < δ := lt_min one_pos (div_pos (div_pos hα hYpos) hDS)
  refine ⟨max d₁ δ, lt_of_lt_of_le hδ (le_max_right _ _), fun g hg => ?_⟩
  obtain ⟨y, hy, s, hs, rfl⟩ := Set.mem_iUnion₂.1 (hΦ₀S hg)
  obtain ⟨hsfin, hsfloor, hswin, hsdet⟩ := mem_centreCutSiegelSet_iff.1 hs
  have hgα : α ≤ ideleNorm F (Matrix.GeneralLinearGroup.det (s * y)) := (hΦ₀s hg).1
  have hsα : α / Y ≤ ideleNorm F (Matrix.GeneralLinearGroup.det s) := by
    rw [div_le_iff₀ hYpos]
    calc α ≤ ideleNorm F (Matrix.GeneralLinearGroup.det (s * y)) := hgα
      _ = ideleNorm F (Matrix.GeneralLinearGroup.det s) *
            ideleNorm F (Matrix.GeneralLinearGroup.det y) := by rw [map_mul, ideleNorm_mul]
      _ ≤ ideleNorm F (Matrix.GeneralLinearGroup.det s) * Y :=
            mul_le_mul_of_nonneg_left (hY y hy) (ideleNorm_pos _).le
  rw [ideleNorm_det_eq_prod_archDetNorm_pow_mult F s hsfin] at hsα
  have hdet0 : ∀ v : InfinitePlace F, 0 ≤ archDetNorm v s := fun v => norm_nonneg _
  refine Set.mem_iUnion₂.2 ⟨y, hy, s, mem_centreCutSiegelSet_iff.2
    ⟨hsfin, hsfloor, hswin, fun w => ⟨max_le (hsdet w).1 ?_, (hsdet w).2⟩⟩, rfl⟩
  set f : InfinitePlace F → ℝ := fun v => archDetNorm v s ^ v.mult with hf_def
  have hsplit : f w * ∏ v ∈ Finset.univ.erase w, f v = ∏ v, f v :=
    Finset.mul_prod_erase Finset.univ f (Finset.mem_univ w)
  have hrest : ∏ v ∈ Finset.univ.erase w, f v ≤ D ^ S := by
    calc ∏ v ∈ Finset.univ.erase w, f v ≤ ∏ v ∈ Finset.univ.erase w, D ^ v.mult :=
          Finset.prod_le_prod (fun v _ => pow_nonneg (hdet0 v) _)
            (fun v _ => pow_le_pow_left₀ (hdet0 v) ((hsdet v).2.trans (le_max_right _ _)) _)
      _ = D ^ (∑ v ∈ Finset.univ.erase w, v.mult) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ D ^ S :=
          pow_le_pow_right₀ hD1 (Finset.sum_le_sum_of_subset (Finset.erase_subset w Finset.univ))
  have hfw : α / Y / D ^ S ≤ f w := by
    rw [div_le_iff₀ hDS]
    calc α / Y ≤ ∏ v, f v := hsα
      _ = f w * ∏ v ∈ Finset.univ.erase w, f v := hsplit.symm
      _ ≤ f w * D ^ S := mul_le_mul_of_nonneg_left hrest (pow_nonneg (hdet0 w) _)
  by_cases h1 : 1 ≤ archDetNorm w s
  · exact (min_le_left _ _).trans h1
  · have hle : f w ≤ archDetNorm w s :=
      pow_le_of_le_one (hdet0 w) (not_le.1 h1).le InfinitePlace.mult_ne_zero
    exact (min_le_right _ _).trans (hfw.trans hle)

private theorem _root_.MeasureTheory.NullMeasurableSet.of_restrict_of_subset {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S A : Set X} (hS : MeasurableSet S) (hAS : A ⊆ S)
    (hA : NullMeasurableSet A (μ.restrict S)) : NullMeasurableSet A μ := by
  obtain ⟨t, htA, ht, htae⟩ := hA.exists_measurable_subset_ae_eq
  refine ht.nullMeasurableSet.congr (ae_eq_set.2 ⟨?_, ?_⟩)
  · rw [Set.diff_eq_empty.2 htA, measure_empty]
  · have h := (ae_eq_set.1 htae).2
    rwa [Measure.restrict_apply' hS, Set.inter_eq_left.2 (Set.diff_subset.trans hAS)] at h

p2m_alias "P2MW.S_AutomorphicForm_peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm.MeasureTheory.NullMeasurableSet.of_restrict_of_subset" "MeasureTheory.NullMeasurableSet.of_restrict_of_subset"
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private theorem integrableOn_adelicGLHaar_of_forall_norm_le_of_forall_eq_zero_of_lt_adelicHeight
    {c u d₁ d₂ α β : ℝ} (hc : 0 < c) (hα : 0 < α) {Tc : Set (AdelicGL2 (𝓞 F) F)}
    (hTc : IsCompact Tc) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet F c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀m : NullMeasurableSet Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F))
    {E : Type*} [NormedAddCommGroup E] {t : AdelicGL2 (𝓞 F) F → ℂ} {k : AdelicGL2 (𝓞 F) F → E}
    (ht : Continuous t)
    (hk : AEStronglyMeasurable k (adelicGLHaar (Fin 2) (𝓞 F) F)) (hkt : ∀ g, ‖k g‖ ≤ ‖t g‖)
    {M : ℝ} (hkM : ∀ g, M < adelicHeight F g → k g = 0) :
    IntegrableOn k Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨d₁', hd₁', hΦ₀S'⟩ :=
    exists_pos_subset_iUnion_image_mul_centreCutSiegelSet_of_ideleNorm_det_mem_Icc F hα hTc hΦ₀S hΦ₀s
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_inter_adelicHeight_le_subset F hc hd₁' hTc hΦ₀S' M
  obtain ⟨Bt, hBt⟩ := hC.exists_bound_of_continuousOn ht.continuousOn
  have hkC : IntegrableOn k C (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    Measure.integrableOn_of_bounded hC.measure_lt_top.ne hk
      ((ae_restrict_mem₀ hC.isClosed.measurableSet.nullMeasurableSet).mono fun g hg =>
        (hkt g).trans (hBt g hg))
  refine hkC.of_ae_diff_eq_zero hΦ₀m (Filter.Eventually.of_forall fun g hg => ?_)
  exact hkM g (not_le.1 fun hle => hg.2 (hsub ⟨hg.1, hle⟩))

end AutomorphicForm.WindowedSiegel

open MeasureTheory NumberField NumberField.AdelicHeight NumberField.AdelicHaar NumberField.TateGlobal
open scoped Pointwise

namespace AutomorphicForm
p2m_export "AutomorphicForm" "highSet mem_highSet_iff lambdaT unipotentGL2 constantTermIntegrand constantTerm constantTerm_const rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent AdelicGL2 globalPoints peterssonIntegral WindowedSiegel.centreCutSiegelSet continuous_unipotentGL2 borelSubgroup exists_isFundamentalDomain_globalPoints_range ideleNorm_det_globalPoints isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul"
p2m_open "AutomorphicForm"

section Generic

variable {G : Type*} [Group G] [MeasurableSpace G]

private theorem isFundamentalDomain_inter_highSet_of_forall_le
    {Γ B : Subgroup G} (hBΓ : B ≤ Γ) {μ : Measure G} {S Φ : Set G} {H : G → ℝ} {R₁ T : ℝ}
    (hΦ : IsFundamentalDomain Γ Φ (μ.restrict S))
    (hS : MeasurableSet S) (hH : MeasurableSet (highSet H T))
    (hinv : ∀ b ∈ B, ∀ g : G, H (b * g) = H g)
    (hbound : ∀ x ∈ Φ, ∀ γ ∈ Γ, γ ∉ B → H (γ * x) ≤ R₁)
    (hT : R₁ ≤ T) :
    IsFundamentalDomain B (Φ ∩ highSet H T) (μ.restrict (S ∩ highSet H T)) := by
  have hle : μ.restrict (S ∩ highSet H T) ≤ μ.restrict S :=
    Measure.restrict_mono Set.inter_subset_left le_rfl
  have hac : μ.restrict (S ∩ highSet H T) ≪ μ.restrict S := Measure.absolutelyContinuous_of_le hle
  refine ⟨?_, ?_, ?_⟩
  · exact (hΦ.nullMeasurableSet.inter hH.nullMeasurableSet).mono_ac hac
  · have h1 : ∀ᵐ g ∂μ.restrict (S ∩ highSet H T), ∃ γ : Γ, γ • g ∈ Φ :=
      hΦ.ae_covers.filter_mono hac.ae_le
    have h2 : ∀ᵐ g ∂μ.restrict (S ∩ highSet H T), g ∈ S ∩ highSet H T :=
      ae_restrict_mem (hS.inter hH)
    filter_upwards [h1, h2] with g hg hgS
    obtain ⟨γ, hγ⟩ := hg
    have hgT : T < H g := mem_highSet_iff.1 hgS.2
    have hx : (γ : G) * g ∈ Φ := by simpa [Subgroup.smul_def] using hγ
    by_cases hγB : (γ : G) ∈ B
    · refine ⟨⟨γ, hγB⟩, hx, ?_⟩
      rw [mem_highSet_iff, Subgroup.smul_def, Subgroup.coe_mk, smul_eq_mul, hinv _ hγB]
      exact hgT
    · exfalso
      have hinvB : (γ : G)⁻¹ ∉ B := fun h => hγB (B.inv_mem_iff.1 h)
      have hb := hbound _ hx _ (Γ.inv_mem γ.2) hinvB
      rw [inv_mul_cancel_left] at hb
      exact not_lt.2 (hb.trans hT) hgT
  · intro b₁ b₂ hne
    have hne' : Subgroup.inclusion hBΓ b₁ ≠ Subgroup.inclusion hBΓ b₂ :=
      fun h => hne (Subgroup.inclusion_injective hBΓ h)
    have hd : AEDisjoint (μ.restrict S) ((Subgroup.inclusion hBΓ b₁ : Γ) • Φ)
        ((Subgroup.inclusion hBΓ b₂ : Γ) • Φ) := hΦ.aedisjoint hne'
    have hsub : ∀ b : B, (b • (Φ ∩ highSet H T) : Set G) ⊆ (Subgroup.inclusion hBΓ b : Γ) • Φ := by
      intro b z hz
      obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.1 hz
      refine Set.mem_smul_set.2 ⟨x, hx.1, ?_⟩
      simp [Subgroup.smul_def, Subgroup.coe_inclusion]
    exact hac (hd.mono (hsub b₁) (hsub b₂))

private theorem smulInvariantMeasure_restrict_of_forall_mem_iff [MeasurableMul G]
    (B : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant] {X : Set G}
    (hX : ∀ b ∈ B, ∀ g : G, g ∈ X ↔ b * g ∈ X) :
    SMulInvariantMeasure B G (μ.restrict X) where
  measure_preimage_smul b s hs := by
    have hpre : (fun x => (b : G) * x) ⁻¹' s ∩ X = (fun x => (b : G) * x) ⁻¹' (s ∩ X) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact and_congr_right fun _ => hX b b.2 g
    show μ.restrict X ((fun x => (b : G) * x) ⁻¹' s) = μ.restrict X s
    rw [Measure.restrict_apply (measurable_const_mul (b : G) hs), Measure.restrict_apply hs, hpre]
    exact measure_preimage_mul μ (b : G) (s ∩ X)

private theorem setIntegral_eq_of_isFundamentalDomain_restrict [MeasurableMul G] (B : Subgroup G)
    [Countable B] (μ : Measure G) [μ.IsMulLeftInvariant] {X D S' : Set G} (hXm : MeasurableSet X)
    (hX : ∀ b ∈ B, ∀ g : G, g ∈ X ↔ b * g ∈ X) (hDX : D ⊆ X)
    (hD : IsFundamentalDomain B D (μ.restrict X)) (hS' : IsFundamentalDomain B S' μ)
    {h : G → ℂ} (hh : ∀ b ∈ B, ∀ g : G, h (b * g) = h g) (hsupp : ∀ g, g ∉ X → h g = 0) :
    ∫ g in D, h g ∂μ = ∫ g in S', h g ∂μ := by
  haveI : SMulInvariantMeasure B G (μ.restrict X) :=
    smulInvariantMeasure_restrict_of_forall_mem_iff B μ hX
  haveI : MeasurableConstSMul B G := ⟨fun b => measurable_const_mul (b : G)⟩
  have hS'X : IsFundamentalDomain B S' (μ.restrict X) :=
    hS'.mono (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hinvf : ∀ (b : B) (g : G), h (b • g) = h g := by
    intro b g
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hh b b.2 g
  have key := hD.setIntegral_eq hS'X hinvf
  have hind : X.indicator h = h := by
    funext g
    by_cases hg : g ∈ X <;> simp [hg, hsupp]
  rw [Measure.restrict_restrict₀ hD.nullMeasurableSet,
    Measure.restrict_restrict₀ hS'X.nullMeasurableSet, Set.inter_eq_left.2 hDX] at key
  rw [key, ← setIntegral_indicator hXm, hind]

private theorem setLIntegral_eq_of_isFundamentalDomain_restrict [MeasurableMul G] (B : Subgroup G)
    [Countable B] (μ : Measure G) [μ.IsMulLeftInvariant] {X D S' : Set G} (hXm : MeasurableSet X)
    (hX : ∀ b ∈ B, ∀ g : G, g ∈ X ↔ b * g ∈ X) (hDX : D ⊆ X)
    (hD : IsFundamentalDomain B D (μ.restrict X)) (hS' : IsFundamentalDomain B S' μ)
    (f : G → ENNReal) (hf : ∀ b ∈ B, ∀ g : G, f (b * g) = f g) (hsupp : ∀ g, g ∉ X → f g = 0) :
    ∫⁻ g in D, f g ∂μ = ∫⁻ g in S', f g ∂μ := by
  haveI : SMulInvariantMeasure B G (μ.restrict X) :=
    smulInvariantMeasure_restrict_of_forall_mem_iff B μ hX
  haveI : MeasurableConstSMul B G := ⟨fun b => measurable_const_mul (b : G)⟩
  have hS'X : IsFundamentalDomain B S' (μ.restrict X) :=
    hS'.mono (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hinvf : ∀ (b : B) (g : G), f (b • g) = f g := by
    intro b g
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hf b b.2 g
  have key := hD.setLIntegral_eq hS'X f hinvf
  have hind : X.indicator f = f := by
    funext g
    by_cases hg : g ∈ X <;> simp [hg, hsupp]
  rw [Measure.restrict_restrict₀ hD.nullMeasurableSet,
    Measure.restrict_restrict₀ hS'X.nullMeasurableSet, Set.inter_eq_left.2 hDX] at key
  rw [key, Set.inter_comm, ← Measure.restrict_restrict hXm, ← lintegral_indicator hXm, hind]

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem isFundamentalDomain_borel_inter_highSet_adelicHeight
    [MeasurableSpace (AdelicGL2 (𝓞 F) F)] {μ : Measure (AdelicGL2 (𝓞 F) F)}
    {S Φ₀ : Set (AdelicGL2 (𝓞 F) F)} {R₁ T : ℝ}
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀ (μ.restrict S))
    (hS : MeasurableSet S) (hH : MeasurableSet (highSet (adelicHeight F) T))
    (hinv : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      adelicHeight F (globalPoints (𝓞 F) F γ * g) = adelicHeight F g)
    (hred : ∀ x ∈ Φ₀, ∀ γ : Matrix.GeneralLinearGroup (Fin 2) F,
      (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → adelicHeight F (globalPoints (𝓞 F) F γ * x) ≤ R₁)
    (hT : R₁ ≤ T) :
    IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F))
      (Φ₀ ∩ highSet (adelicHeight F) T) (μ.restrict (S ∩ highSet (adelicHeight F) T)) := by
  refine isFundamentalDomain_inter_highSet_of_forall_le ?_ hΦ₀ hS hH ?_ ?_ hT
  · intro b hb
    obtain ⟨γ, -, rfl⟩ := Subgroup.mem_map.1 hb
    exact MonoidHom.mem_range.2 ⟨γ, rfl⟩
  · intro b hb g
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hb
    exact hinv γ hγ g
  · intro x hx b hb hbB
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 hb
    refine hred x hx γ fun h => hbB ?_
    exact Subgroup.mem_map_of_mem _ (show γ ∈ borelSubgroup F from h)

end Adelic

section BorelUnfolding

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private theorem countable_borel_map_globalPoints :
    Countable ((borelSubgroup F).map (globalPoints (𝓞 F) F)) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable fun _ _ h => Units.ext h
  exact ((globalPoints (𝓞 F) F).subgroupMap_surjective (borelSubgroup F)).countable

private theorem borel_map_globalPoints_le_range :
    (borelSubgroup F).map (globalPoints (𝓞 F) F) ≤ (globalPoints (𝓞 F) F).range := by
  intro b hb
  obtain ⟨γ, -, rfl⟩ := Subgroup.mem_map.1 hb
  exact MonoidHom.mem_range.2 ⟨γ, rfl⟩

private theorem exists_isFundamentalDomain_borel_map_globalPoints :
    ∃ S : Set (AdelicGL2 (𝓞 F) F),
      IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S
        (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  classical
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SMulInvariantMeasure (AdelicGL2 (𝓞 F) F) (AdelicGL2 (𝓞 F) F)
      (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    ⟨fun c s _ => measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) c s⟩
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable fun _ _ h => Units.ext h
  haveI : Countable (globalPoints (𝓞 F) F).range := (globalPoints (𝓞 F) F).rangeRestrict_surjective.countable
  obtain ⟨𝓕, h𝓕⟩ := exists_isFundamentalDomain_globalPoints_range F
  set Γ₁ : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range
  set Γ₂ : Subgroup (AdelicGL2 (𝓞 F) F) := (borelSubgroup F).map (globalPoints (𝓞 F) F)
  set N : Subgroup Γ₁ := Γ₂.subgroupOf Γ₁
  haveI : Countable (Γ₁ ⧸ N) := (QuotientGroup.mk_surjective (s := N)).countable
  have hR : ∀ γ : Γ₁, ∃! i : Γ₁ ⧸ N, (((Quotient.out i : Γ₁)⁻¹ * γ : Γ₁) : AdelicGL2 (𝓞 F) F) ∈ Γ₂ := by
    intro γ
    refine ⟨QuotientGroup.mk γ, ?_, fun i hi => ?_⟩
    · exact Subgroup.mem_subgroupOf.1
        (QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk γ : Γ₁ ⧸ N)))
    · calc i = QuotientGroup.mk (Quotient.out i) := (QuotientGroup.out_eq' i).symm
        _ = QuotientGroup.mk γ := QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hi)
  exact ⟨_, IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
    (adelicGLHaar (Fin 2) (𝓞 F) F) Γ₁ Γ₂ (borel_map_globalPoints_le_range F) 𝓕 h𝓕
    (fun i : Γ₁ ⧸ N => Quotient.out i) hR⟩

private theorem mem_setOf_ideleNorm_det_mem_Icc_globalPoints_mul_iff (α β : ℝ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    g ∈ {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β} ↔
      globalPoints (𝓞 F) F γ * g ∈
        {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β} := by
  simp only [Set.mem_setOf_eq, map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

private theorem mem_slab_inter_highSet_borel_mul_iff (α β T : ℝ) {b : AdelicGL2 (𝓞 F) F}
    (hb : b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F)) (g : AdelicGL2 (𝓞 F) F) :
    g ∈ {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β} ∩
        highSet (adelicHeight F) T ↔
      b * g ∈ {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β} ∩
        highSet (adelicHeight F) T := by
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hb
  rw [Set.mem_inter_iff, Set.mem_inter_iff, mem_highSet_iff, mem_highSet_iff,
    adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ
      (show (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 from hγ) g]
  exact and_congr_left fun _ => mem_setOf_ideleNorm_det_mem_Icc_globalPoints_mul_iff F α β γ g

private theorem slab_shell_mul_borel_mul (α β T T' : ℝ) {t : AdelicGL2 (𝓞 F) F → ℂ}
    (ht : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, t (globalPoints (𝓞 F) F γ * g) = t g) :
    ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F,
      {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) (b * g) *
          (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F (b * g)) * t (b * g) =
        {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g := by
  intro b hb g
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hb
  have hXg : {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
        (fun _ => (1 : ℂ)) (globalPoints (𝓞 F) F γ * g) =
      {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
        (fun _ => (1 : ℂ)) g := by
    by_cases hgX : g ∈ {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}
    · rw [Set.indicator_of_mem hgX,
        Set.indicator_of_mem ((mem_setOf_ideleNorm_det_mem_Icc_globalPoints_mul_iff F α β γ g).1 hgX)]
    · rw [Set.indicator_of_notMem hgX, Set.indicator_of_notMem
        (fun h => hgX ((mem_setOf_ideleNorm_det_mem_Icc_globalPoints_mul_iff F α β γ g).2 h))]
  rw [hXg, adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ
    (show (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 from hγ) g, ht γ hγ g]

private theorem slab_shell_mul_eq_zero_of_notMem (α β T T' : ℝ) (t : AdelicGL2 (𝓞 F) F → ℂ)
    {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∉ {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β} ∩
      highSet (adelicHeight F) T) :
    {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
          (fun _ => (1 : ℂ)) g *
        (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g = 0 := by
  by_cases hgX : g ∈ {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}
  · have hgT : adelicHeight F g ∉ Set.Ioc T T' :=
      fun h => hg ⟨hgX, mem_highSet_iff.2 h.1⟩
    rw [Set.indicator_of_notMem hgT, mul_zero, zero_mul]
  · rw [Set.indicator_of_notMem hgX, zero_mul, zero_mul]

private theorem setIntegral_slab_shell_eq_setIntegral_of_isFundamentalDomain {α β : ℝ}
    {Φ₀ S' : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hslab : MeasurableSet {g : AdelicGL2 (𝓞 F) F |
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    {H₁ T T' : ℝ} (hH : MeasurableSet (highSet (adelicHeight F) T))
    (hred : ∀ x ∈ Φ₀, ∀ γ : Matrix.GeneralLinearGroup (Fin 2) F,
      (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → adelicHeight F (globalPoints (𝓞 F) F γ * x) ≤ H₁)
    (hT : H₁ ≤ T)
    (hS' : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S'
      (adelicGLHaar (Fin 2) (𝓞 F) F))
    {t : AdelicGL2 (𝓞 F) F → ℂ}
    (ht : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, t (globalPoints (𝓞 F) F γ * g) = t g) :
    ∫ g in Φ₀,
        {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ g in S',
        {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  classical
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := countable_borel_map_globalPoints F
  have hD := isFundamentalDomain_borel_inter_highSet_adelicHeight F hΦ₀ hslab hH
    (fun γ hγ g => adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ
      (show (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 from hγ) g) hred hT
  set k : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
        (fun _ => (1 : ℂ)) g *
      (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g with hk
  have hkhigh : (highSet (adelicHeight F) T).indicator k = k := by
    funext g
    by_cases hg : g ∈ highSet (adelicHeight F) T
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg]
      exact (slab_shell_mul_eq_zero_of_notMem F α β T T' t fun h => hg h.2).symm
  have hleft : (∫ g in Φ₀, k g ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
      ∫ g in Φ₀ ∩ highSet (adelicHeight F) T, k g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    conv_lhs => rw [← hkhigh]
    exact setIntegral_indicator hH
  exact hleft.trans (setIntegral_eq_of_isFundamentalDomain_restrict
    ((borelSubgroup F).map (globalPoints (𝓞 F) F)) (adelicGLHaar (Fin 2) (𝓞 F) F) (hslab.inter hH)
    (fun b hb g => mem_slab_inter_highSet_borel_mul_iff F α β T hb g)
    (Set.inter_subset_inter_left _ hΦ₀s) hD hS' (slab_shell_mul_borel_mul F α β T T' ht)
    (fun g hg => slab_shell_mul_eq_zero_of_notMem F α β T T' t hg))

private theorem lintegral_enorm_slab_shell_lt_top_of_integrableOn {α β : ℝ}
    {Φ₀ S' : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hslab : MeasurableSet {g : AdelicGL2 (𝓞 F) F |
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    {H₁ T T' : ℝ} (hH : MeasurableSet (highSet (adelicHeight F) T))
    (hred : ∀ x ∈ Φ₀, ∀ γ : Matrix.GeneralLinearGroup (Fin 2) F,
      (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → adelicHeight F (globalPoints (𝓞 F) F γ * x) ≤ H₁)
    (hT : H₁ ≤ T)
    (hS' : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S'
      (adelicGLHaar (Fin 2) (𝓞 F) F))
    {t : AdelicGL2 (𝓞 F) F → ℂ}
    (ht : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, t (globalPoints (𝓞 F) F γ * g) = t g)
    (hint : IntegrableOn (fun g : AdelicGL2 (𝓞 F) F =>
      {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
          (fun _ => (1 : ℂ)) g *
        (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    ∫⁻ g in S',
        ‖{x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g‖ₑ
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  classical
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := countable_borel_map_globalPoints F
  have hD := isFundamentalDomain_borel_inter_highSet_adelicHeight F hΦ₀ hslab hH
    (fun γ hγ g => adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ
      (show (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 from hγ) g) hred hT
  set k : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
        (fun _ => (1 : ℂ)) g *
      (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g with hk
  have hf : ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F,
      ‖k (b * g)‖ₑ = ‖k g‖ₑ :=
    fun b hb g => congrArg (‖·‖ₑ) (slab_shell_mul_borel_mul F α β T T' ht b hb g)
  have hzero : ∀ g : AdelicGL2 (𝓞 F) F,
      g ∉ {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β} ∩
        highSet (adelicHeight F) T → ‖k g‖ₑ = 0 :=
    fun g hg => by rw [show k g = 0 from slab_shell_mul_eq_zero_of_notMem F α β T T' t hg, enorm_zero]
  have key := setLIntegral_eq_of_isFundamentalDomain_restrict
    ((borelSubgroup F).map (globalPoints (𝓞 F) F)) (adelicGLHaar (Fin 2) (𝓞 F) F) (hslab.inter hH)
    (fun b hb g => mem_slab_inter_highSet_borel_mul_iff F α β T hb g)
    (Set.inter_subset_inter_left _ hΦ₀s) hD hS' (fun g => ‖k g‖ₑ) hf hzero
  rw [← key]
  exact lt_of_le_of_lt (lintegral_mono_set Set.inter_subset_left) hint.2

private theorem measurable_slab_shell_mul {α β T T' : ℝ}
    (hslab : MeasurableSet {g : AdelicGL2 (𝓞 F) F |
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    {t : AdelicGL2 (𝓞 F) F → ℂ} (ht : Continuous t) :
    Measurable fun g : AdelicGL2 (𝓞 F) F =>
      {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
          (fun _ => (1 : ℂ)) g *
        (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g := by
  have h₁ : Measurable ({x : AdelicGL2 (𝓞 F) F |
      ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator fun _ => (1 : ℂ)) :=
    measurable_const.indicator hslab
  have h₂ : Measurable fun g : AdelicGL2 (𝓞 F) F =>
      (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) :=
    (measurable_const.indicator measurableSet_Ioc).comp (continuous_adelicHeight F).measurable
  exact (h₁.mul h₂).mul ht.measurable

private theorem norm_slab_shell_mul_le {α β T T' : ℝ} (t : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    ‖{x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
          (fun _ => (1 : ℂ)) g *
        (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g‖ ≤ ‖t g‖ := by
  have h₁ : ‖{x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
      (fun _ => (1 : ℂ)) g‖ ≤ 1 :=
    (norm_indicator_le_norm_self (fun _ : AdelicGL2 (𝓞 F) F => (1 : ℂ)) g).trans (by simp)
  have h₂ : ‖(Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g)‖ ≤ 1 :=
    (norm_indicator_le_norm_self (fun _ : ℝ => (1 : ℂ)) (adelicHeight F g)).trans (by simp)
  have h₃ : ‖{x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
        (fun _ => (1 : ℂ)) g‖ * ‖(Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g)‖ ≤ 1 := by
    simpa using mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one
  rw [norm_mul, norm_mul]
  calc _ ≤ 1 * ‖t g‖ := mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)
    _ = ‖t g‖ := one_mul _

private theorem slab_shell_mul_eq_zero_of_lt {α β T T' : ℝ} (t : AdelicGL2 (𝓞 F) F → ℂ) {g : AdelicGL2 (𝓞 F) F}
    (hg : T' < adelicHeight F g) :
    {x : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β}.indicator
          (fun _ => (1 : ℂ)) g *
        (Set.Ioc T T').indicator (fun _ => (1 : ℂ)) (adelicHeight F g) * t g = 0 := by
  have h : adelicHeight F g ∉ Set.Ioc T T' := fun h => not_lt.2 h.2 hg
  rw [Set.indicator_of_notMem h, mul_zero, zero_mul]

private theorem peterssonIntegral_zero (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F 0 S x y =
      ∫ g in S, x g * (starRingEnd ℂ) (y g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  simp [peterssonIntegral]

private theorem _root_.Real.le_exp_of_log_max_one_le {a R : ℝ} (h : Real.log (max a 1) ≤ R) : a ≤ Real.exp R :=
  (le_max_left a 1).trans
    ((Real.exp_log (lt_of_lt_of_le one_pos (le_max_right a 1))).symm.le.trans (Real.exp_le_exp.2 h))

p2m_alias "P2MW.S_AutomorphicForm_peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm.Real.le_exp_of_log_max_one_le" "Real.le_exp_of_log_max_one_le"
end BorelUnfolding

end AutomorphicForm

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open scoped ENNReal

namespace AutomorphicForm
p2m_export "AutomorphicForm" "highSet mem_highSet_iff lambdaT unipotentGL2 constantTermIntegrand constantTerm constantTerm_const rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent AdelicGL2 globalPoints peterssonIntegral WindowedSiegel.centreCutSiegelSet continuous_unipotentGL2 borelSubgroup exists_isFundamentalDomain_globalPoints_range ideleNorm_det_globalPoints isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul"
p2m_open "AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type) [Field K] [NumberField K]

private noncomputable def boxSheetMap (u : AdeleRing (𝓞 K) K) : rationalTorusUnipotent K :=
  Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)

private theorem coe_boxSheetMap (u : AdeleRing (𝓞 K) K) :
    ((boxSheetMap K u : rationalTorusUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 u :=
  (Subgroup.coe_inclusion le_sup_right (toAdelicUnipotent K u)).trans
    (MonoidHom.coe_rangeRestrict _ _)

private theorem measurable_boxSheetMap : Measurable (boxSheetMap K) :=
  continuous_unipotentGL2.measurable.subtype_mk

private theorem rationalTorusUnipotentHaar_restrict_boxSheet :
    (rationalTorusUnipotentHaar K).restrict (boxSheetMap K '' adelicBox K)
      = Measure.map (boxSheetMap K)
          (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) := by
  obtain ⟨-, -, -, -, hsheet⟩ := isFundamentalDomain_boxSheet_rationalTorusUnipotent K
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF (measurable_boxSheetMap K), ProbabilityTheory.cond, ← Measure.restrict_smul]
  exact hsheet F hF

private theorem setIntegral_boxSheet_mul_eq_constantTerm (k : AdelicGL2 (𝓞 K) K → ℂ) (hk : Measurable k)
    (g : AdelicGL2 (𝓞 K) K) :
    ∫ x in boxSheetMap K '' adelicBox K, k ((x : AdelicGL2 (𝓞 K) K) * g) ∂(rationalTorusUnipotentHaar K)
      = constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2 k g := by
  have hkm : Measurable fun x : rationalTorusUnipotent K => k ((x : AdelicGL2 (𝓞 K) K) * g) :=
    hk.comp (measurable_subtype_coe.mul_const g)
  rw [rationalTorusUnipotentHaar_restrict_boxSheet K,
    integral_map (measurable_boxSheetMap K).aemeasurable hkm.aestronglyMeasurable]
  simp only [coe_boxSheetMap]
  rfl

private theorem setIntegral_eq_integral_constantTerm_out_of_isFundamentalDomain_borel
    (k : AdelicGL2 (𝓞 K) K → ℂ) (hk : Measurable k)
    (hkB : ∀ b ∈ (borelSubgroup K).map (globalPoints (𝓞 K) K), ∀ g : AdelicGL2 (𝓞 K) K, k (b * g) = k g)
    (S : Set (AdelicGL2 (𝓞 K) K))
    (hS : IsFundamentalDomain ((borelSubgroup K).map (globalPoints (𝓞 K) K)) S
      (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hfin : ∫⁻ g in S, ‖k g‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ∞) :
    Integrable
        (fun q : RationalTorusUnipotentQuotient K =>
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2 k q.out)
        (rationalTorusUnipotentQuotientMeasure K) ∧
      ∫ g in S, k g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        = ∫ q : RationalTorusUnipotentQuotient K,
            constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2 k q.out
              ∂(rationalTorusUnipotentQuotientMeasure K) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨hBle, hBc, -, hsheet, -⟩ := isFundamentalDomain_boxSheet_rationalTorusUnipotent K
  obtain ⟨hHaar, hright⟩ := isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K
  haveI : (rationalTorusUnipotentHaar K).IsHaarMeasure := hHaar
  haveI : (rationalTorusUnipotentHaar K).IsMulRightInvariant := hright
  haveI : Countable ((borelSubgroup K).map (globalPoints (𝓞 K) K)) := hBc
  obtain ⟨-, hint, heq⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
      (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K) (isClosed_rationalTorusUnipotent K)
      (rationalTorusUnipotentHaar K) ((borelSubgroup K).map (globalPoints (𝓞 K) K)) hBle k hk hkB S hS
      _ hsheet hfin
  have hfun :
      (fun q : RationalTorusUnipotentQuotient K =>
          ∫ x in ((fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) ''
              adelicBox K : Set (rationalTorusUnipotent K)),
            k ((x : AdelicGL2 (𝓞 K) K) * q.out) ∂(rationalTorusUnipotentHaar K))
        = fun q : RationalTorusUnipotentQuotient K =>
            constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2 k
              q.out :=
    funext fun q => setIntegral_boxSheet_mul_eq_constantTerm K k hk q.out
  exact ⟨hfun ▸ hint, hfun ▸ heq⟩

end AutomorphicForm

open MeasureTheory ComplexConjugate NumberField

namespace AutomorphicForm
p2m_export "AutomorphicForm" "highSet mem_highSet_iff lambdaT unipotentGL2 constantTermIntegrand constantTerm constantTerm_const rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent AdelicGL2 globalPoints peterssonIntegral WindowedSiegel.centreCutSiegelSet continuous_unipotentGL2 borelSubgroup exists_isFundamentalDomain_globalPoints_range ideleNorm_det_globalPoints isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul"
p2m_open "AutomorphicForm"

section ConstantTermFactors

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

private theorem constantTerm_mul_left_of_forall_mul_eq (μ : Measure Q) (u : Q → G) (c f : G → ℂ)
    (hc : ∀ (q : Q) (g : G), c (u q * g) = c g) (g : G) :
    constantTerm μ u (fun x => c x * f x) g = c g * constantTerm μ u f g := by
  simp only [constantTerm, constantTermIntegrand, hc, integral_const_mul]

private theorem constantTerm_mul_conj_of_forall_mul_eq (μ : Measure Q) (u : Q → G) (c f : G → ℂ)
    (hc : ∀ (q : Q) (g : G), c (u q * g) = c g) (g : G) :
    constantTerm μ u (fun x => c x * conj (f x)) g = c g * conj (constantTerm μ u f g) := by
  simp only [constantTerm, constantTermIntegrand, hc, integral_const_mul, integral_conj]

private theorem constantTerm_of_forall_mul_eq (μ : Measure Q) [IsProbabilityMeasure μ] (u : Q → G) (c : G → ℂ)
    (hc : ∀ (q : Q) (g : G), c (u q * g) = c g) (g : G) : constantTerm μ u c g = c g := by
  have h : constantTerm μ u c g = constantTerm μ u (fun _ => c g) g := by
    simp only [constantTerm, constantTermIntegrand, hc]
  rw [h, constantTerm_const]

end ConstantTermFactors

section Determinants

variable {R : Type*} [CommRing R]

private theorem generalLinearGroup_det_unipotentGL2 (x : R) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  show Matrix.det !![(1 : R), x; 0, 1] = 1
  rw [Matrix.det_fin_two_of]
  simp

private theorem generalLinearGroup_det_unipotentGL2_mul (x : R) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, generalLinearGroup_det_unipotentGL2, one_mul]

end Determinants

section HeightShellTerms

attribute [local instance] NumberField.AdelicHaar.adeleBorel

variable (F : Type) [Field F] [NumberField F]

private theorem slab_indicator_unipotentGL2_mul (α β : ℝ) (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
        (fun _ => (1 : ℂ)) (unipotentGL2 x * g)
      = {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
          (fun _ => (1 : ℂ)) g := by
  simp only [Set.indicator_apply, Set.mem_setOf_eq, generalLinearGroup_det_unipotentGL2_mul]

variable (ν : Measure (AdeleRing (𝓞 F) F)) (E E' : AdelicGL2 (𝓞 F) F → ℂ) (α β R R' : ℝ)

private theorem constantTerm_slab_shell_mul_conj_constantTerm_eq
    (hH : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      NumberField.AdelicHeight.adelicHeight F (unipotentGL2 x * g)
        = NumberField.AdelicHeight.adelicHeight F g)
    (hE'N : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      constantTerm ν (fun t => unipotentGL2 t) E' (unipotentGL2 x * g)
        = constantTerm ν (fun t => unipotentGL2 t) E' g) :
    constantTerm ν (fun t => unipotentGL2 t)
        (fun g => {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (E g * (starRingEnd ℂ) (constantTerm ν (fun t => unipotentGL2 t) E' g)))
      = fun g => {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (constantTerm ν (fun t => unipotentGL2 t) E g *
            (starRingEnd ℂ) (constantTerm ν (fun t => unipotentGL2 t) E' g)) := by
  funext g
  have hk : (fun g : AdelicGL2 (𝓞 F) F => {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (E g * (starRingEnd ℂ) (constantTerm ν (fun t => unipotentGL2 t) E' g)))
      = fun g => ({g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (starRingEnd ℂ) (constantTerm ν (fun t => unipotentGL2 t) E' g)) * E g :=
    funext fun g => by ring
  rw [hk, constantTerm_mul_left_of_forall_mul_eq]
  · ring
  · intro x g
    simp only [slab_indicator_unipotentGL2_mul, hH, hE'N]

private theorem constantTerm_slab_shell_constantTerm_mul_conj_eq
    (hH : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      NumberField.AdelicHeight.adelicHeight F (unipotentGL2 x * g)
        = NumberField.AdelicHeight.adelicHeight F g)
    (hEN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      constantTerm ν (fun t => unipotentGL2 t) E (unipotentGL2 x * g)
        = constantTerm ν (fun t => unipotentGL2 t) E g) :
    constantTerm ν (fun t => unipotentGL2 t)
        (fun g => {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (constantTerm ν (fun t => unipotentGL2 t) E g * (starRingEnd ℂ) (E' g)))
      = fun g => {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (constantTerm ν (fun t => unipotentGL2 t) E g *
            (starRingEnd ℂ) (constantTerm ν (fun t => unipotentGL2 t) E' g)) := by
  funext g
  have hk : (fun g : AdelicGL2 (𝓞 F) F => {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (constantTerm ν (fun t => unipotentGL2 t) E g * (starRingEnd ℂ) (E' g)))
      = fun g => ({g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          constantTerm ν (fun t => unipotentGL2 t) E g) * conj (E' g) :=
    funext fun g => by ring
  rw [hk, constantTerm_mul_conj_of_forall_mul_eq]
  · ring
  · intro x g
    simp only [slab_indicator_unipotentGL2_mul, hH, hEN]

private theorem constantTerm_slab_shell_constantTerm_mul_conj_constantTerm_eq [IsProbabilityMeasure ν]
    (hH : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      NumberField.AdelicHeight.adelicHeight F (unipotentGL2 x * g)
        = NumberField.AdelicHeight.adelicHeight F g)
    (hEN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      constantTerm ν (fun t => unipotentGL2 t) E (unipotentGL2 x * g)
        = constantTerm ν (fun t => unipotentGL2 t) E g)
    (hE'N : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      constantTerm ν (fun t => unipotentGL2 t) E' (unipotentGL2 x * g)
        = constantTerm ν (fun t => unipotentGL2 t) E' g) :
    constantTerm ν (fun t => unipotentGL2 t)
        (fun g => {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (constantTerm ν (fun t => unipotentGL2 t) E g *
            (starRingEnd ℂ) (constantTerm ν (fun t => unipotentGL2 t) E' g)))
      = fun g => {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (constantTerm ν (fun t => unipotentGL2 t) E g *
            (starRingEnd ℂ) (constantTerm ν (fun t => unipotentGL2 t) E' g)) :=
  funext fun g => constantTerm_of_forall_mul_eq ν (fun t => unipotentGL2 t) _
    (fun x g => by simp only [slab_indicator_unipotentGL2_mul, hH, hEN, hE'N]) g

end HeightShellTerms

end AutomorphicForm

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.TateGlobal
open NumberField.AdelicHeight
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "highSet mem_highSet_iff lambdaT unipotentGL2 constantTermIntegrand constantTerm constantTerm_const rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent AdelicGL2 globalPoints peterssonIntegral WindowedSiegel.centreCutSiegelSet continuous_unipotentGL2 borelSubgroup exists_isFundamentalDomain_globalPoints_range ideleNorm_det_globalPoints isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul"
p2m_open "AutomorphicForm"

section Increment

variable (F : Type) [Field F] [NumberField F]

open scoped ComplexConjugate in

private theorem memLp_two_lambdaT_adelicBox_of_le {c u d₁ d₂ α β : ℝ} (hc : 0 < c) (hα : 0 < α)
    {Tc : Set (AdelicGL2 (𝓞 F) F)} (hTc : IsCompact Tc) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet F c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀m : NullMeasurableSet Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F))
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) {R₁ R : ℝ} (hR : R₁ ≤ R)
    (hL2 : IntegrableOn (fun g => ‖lambdaT ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F])
        (fun t => unipotentGL2 t) (adelicHeight F) (Real.exp R₁) φ g‖ ^ 2) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    MemLp (lambdaT ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F]) (fun t => unipotentGL2 t)
        (adelicHeight F) (Real.exp R) φ) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
  classical
  set ν : Measure (AdeleRing (𝓞 F) F) := (AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F] with hν
  have hN : Continuous (constantTerm ν (fun t => unipotentGL2 t) φ) := continuous_constantTerm_adelicBox F hφ
  have hhigh : ∀ T : ℝ, MeasurableSet (highSet (adelicHeight F) T) := fun T =>
    (isOpen_lt continuous_const (continuous_adelicHeight F)).measurableSet
  have h₁ : MemLp (lambdaT ν (fun t => unipotentGL2 t) (adelicHeight F) (Real.exp R₁) φ) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm
      (measurable_lambdaT_of_continuous ν (fun t => unipotentGL2 t) (hhigh _) hφ hN).aestronglyMeasurable).2
      hL2
  set p : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    (Set.Ioc (Real.exp R₁) (Real.exp R)).indicator (fun _ => (1 : ℂ)) (adelicHeight F g) *
      constantTerm ν (fun t => unipotentGL2 t) φ g with hp
  have hpm : Measurable p :=
    ((measurable_const.indicator measurableSet_Ioc).comp (continuous_adelicHeight F).measurable).mul
      hN.measurable
  have hp_le : ∀ g, ‖p g‖ ≤ ‖constantTerm ν (fun t => unipotentGL2 t) φ g‖ := by
    intro g
    simp only [hp, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      ((norm_indicator_le_norm_self (fun _ : ℝ => (1 : ℂ)) (adelicHeight F g)).trans (by simp))
  have hsq : IntegrableOn (fun g => ‖p g‖ ^ 2) Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    refine WindowedSiegel.integrableOn_adelicGLHaar_of_forall_norm_le_of_forall_eq_zero_of_lt_adelicHeight F
      hc hα hTc hΦ₀S hΦ₀s hΦ₀m
      (t := fun g => ((‖constantTerm ν (fun t => unipotentGL2 t) φ g‖ ^ 2 : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp (hN.norm.pow 2)) (hpm.norm.pow_const 2).aestronglyMeasurable
      (fun g => ?_) (M := Real.exp R) (fun g hg => ?_)
    · simp only [Complex.norm_real, norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hp_le g) 2
    · have hnot : adelicHeight F g ∉ Set.Ioc (Real.exp R₁) (Real.exp R) := fun h => not_lt.2 h.2 hg
      simp [hp, Set.indicator_of_notMem hnot]
  have hpL2 : MemLp p 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm hpm.aestronglyMeasurable).2 hsq
  rw [lambdaT_eq_lambdaT_add_shell_mul_constantTerm ν (fun t => unipotentGL2 t) (adelicHeight F)
    (Real.exp_le_exp.2 hR) φ]
  exact h₁.add hpL2

private theorem integrableOn_lambdaT_mul_conj_lambdaT_adelicBox {c u d₁ d₂ α β : ℝ} (hc : 0 < c) (hα : 0 < α)
    {Tc : Set (AdelicGL2 (𝓞 F) F)} (hTc : IsCompact Tc) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet F c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀m : NullMeasurableSet Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F))
    {E E' : AdelicGL2 (𝓞 F) F → ℂ} (hE : Continuous E) (hE' : Continuous E') {R₁ R : ℝ} (hR : R₁ ≤ R)
    (hL2 : IntegrableOn (fun g => ‖lambdaT ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F])
        (fun t => unipotentGL2 t) (adelicHeight F) (Real.exp R₁) E g‖ ^ 2) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hL2' : IntegrableOn (fun g => ‖lambdaT ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F])
        (fun t => unipotentGL2 t) (adelicHeight F) (Real.exp R₁) E' g‖ ^ 2) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    IntegrableOn (fun g =>
        lambdaT ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F]) (fun t => unipotentGL2 t)
            (adelicHeight F) (Real.exp R) E g *
          (starRingEnd ℂ) (lambdaT ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F])
            (fun t => unipotentGL2 t) (adelicHeight F) (Real.exp R) E' g))
      Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have hA := memLp_two_lambdaT_adelicBox_of_le F hc hα hTc hΦ₀S hΦ₀s hΦ₀m hE hR hL2
  have hB := memLp_two_lambdaT_adelicBox_of_le F hc hα hTc hΦ₀S hΦ₀s hΦ₀m hE' hR hL2'
  have hBm : Measurable (lambdaT ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F])
      (fun t => unipotentGL2 t) (adelicHeight F) (Real.exp R) E') :=
    measurable_lambdaT_of_continuous _ _ (isOpen_lt continuous_const (continuous_adelicHeight F)).measurableSet
      hE' (continuous_constantTerm_adelicBox F hE')
  have hBc : MemLp (fun g => (starRingEnd ℂ) (lambdaT ((AdelicHaar.adelicAddHaar (𝓞 F) F)[|adelicBox F])
      (fun t => unipotentGL2 t) (adelicHeight F) (Real.exp R) E' g)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
    hB.of_le (Complex.continuous_conj.measurable.comp hBm).aestronglyMeasurable
      (ae_of_all _ fun g => by simp)
  exact memLp_one_iff_integrable.1 (hBc.mul' hA)

end Increment

end AutomorphicForm

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm.AutomorphicForm IsDedekindDomain"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 F) F)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet F c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ R₁ : ℝ, ∀ (E E' : AdelicGL2 (𝓞 F) F → ℂ), Continuous E → Continuous E' →
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        E (globalPoints (𝓞 F) F γ * g) = E g) →
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        E' (globalPoints (𝓞 F) F γ * g) = E' g) →
      let ν : @Measure (AdeleRing (𝓞 F) F) (adeleBorel (𝓞 F) F) :=
        @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)
      let Λ : ℝ → (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℂ := fun R φ =>
        @AutomorphicForm.lambdaT _ (adeleBorel (𝓞 F) F) _ _ ν (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) φ
      IntegrableOn (fun g => ‖Λ R₁ E g‖ ^ 2) Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) →
      IntegrableOn (fun g => ‖Λ R₁ E' g‖ ^ 2) Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) →
      ∀ (R R' : ℝ), R₁ ≤ R → R ≤ R' →
      peterssonIntegral F 0 Φ₀ (Λ R' E) (Λ R' E') - peterssonIntegral F 0 Φ₀ (Λ R E) (Λ R E') =
        ∫ q : RationalTorusUnipotentQuotient F,
          {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}.indicator
            (fun _ => (1 : ℂ)) q.out *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F q.out) *
          (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 F) F) _ _ ν
              (fun t => AutomorphicForm.unipotentGL2 t) E q.out *
            (starRingEnd ℂ) (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 F) F) _ _ ν
              (fun t => AutomorphicForm.unipotentGL2 t) E' q.out))
          ∂(rationalTorusUnipotentQuotientMeasure F) := by
  classical
  obtain ⟨H₁, hred⟩ :=
    WindowedSiegel.exists_forall_adelicHeight_globalPoints_mul_le_of_subset_iUnion_mul_centreCutSiegelSet
      F c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S
  refine ⟨Real.log (max H₁ 1), ?_⟩
  intro E E' hEc hE'c hE hE' ν Λ hL2 hL2' R R' hR₁R hRR'

  have hslab : MeasurableSet {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :=
    NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F α β
  have hΦ₀m : NullMeasurableSet Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hΦ₀.nullMeasurableSet.of_restrict_of_subset hslab hΦ₀s
  have hT : H₁ ≤ Real.exp R := Real.le_exp_of_log_max_one_le hR₁R
  have hTT' : Real.exp R ≤ Real.exp R' := Real.exp_le_exp.2 hRR'
  have hH : MeasurableSet (highSet (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)) :=
    (isOpen_lt continuous_const (NumberField.AdelicHeight.continuous_adelicHeight F)).measurableSet
  obtain ⟨S', hS'⟩ := exists_isFundamentalDomain_borel_map_globalPoints F

  have hI : IntegrableOn (fun g => Λ R E g * (starRingEnd ℂ) (Λ R E' g)) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    integrableOn_lambdaT_mul_conj_lambdaT_adelicBox F hc hα hTc hΦ₀S hΦ₀s hΦ₀m hEc hE'c hR₁R hL2 hL2'
  have hI' : IntegrableOn (fun g => Λ R' E g * (starRingEnd ℂ) (Λ R' E' g)) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    integrableOn_lambdaT_mul_conj_lambdaT_adelicBox F hc hα hTc hΦ₀S hΦ₀s hΦ₀m hEc hE'c (hR₁R.trans hRR')
      hL2 hL2'

  set t₁ : AdelicGL2 (𝓞 F) F → ℂ := fun g => E g * (starRingEnd ℂ)
    (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun x => unipotentGL2 x) E' g)
    with ht₁
  set t₂ : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun x => unipotentGL2 x) E g *
      (starRingEnd ℂ) (E' g) with ht₂
  set t₃ : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun x => unipotentGL2 x) E g *
      (starRingEnd ℂ) (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun x => unipotentGL2 x) E' g) with ht₃
  set K : (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℂ := fun t g =>
    {x : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈
        Set.Icc α β}.indicator (fun _ => (1 : ℂ)) g *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
        (NumberField.AdelicHeight.adelicHeight F g) * t g with hK
  have hENc : Continuous (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun x => unipotentGL2 x) E) := continuous_constantTerm_adelicBox F hEc
  have hE'Nc : Continuous (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun x => unipotentGL2 x) E') := continuous_constantTerm_adelicBox F hE'c
  have ht₁c : Continuous t₁ := hEc.mul (Complex.continuous_conj.comp hE'Nc)
  have ht₂c : Continuous t₂ := hENc.mul (Complex.continuous_conj.comp hE'c)
  have ht₃c : Continuous t₃ := hENc.mul (Complex.continuous_conj.comp hE'Nc)

  have hEN_B := fun (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ borelSubgroup F)
      (g : AdelicGL2 (𝓞 F) F) =>
    constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F (fun γ _ h => hE γ h) hγ g
  have hE'N_B := fun (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ borelSubgroup F)
      (g : AdelicGL2 (𝓞 F) F) =>
    constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F (fun γ _ h => hE' γ h) hγ g
  have hinv₁ : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      t₁ (globalPoints (𝓞 F) F γ * g) = t₁ g := by
    intro γ hγ g
    simp only [ht₁]
    rw [hE γ g, hE'N_B γ hγ g]
  have hinv₂ : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      t₂ (globalPoints (𝓞 F) F γ * g) = t₂ g := by
    intro γ hγ g
    simp only [ht₂]
    rw [hE' γ g, hEN_B γ hγ g]
  have hinv₃ : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      t₃ (globalPoints (𝓞 F) F γ * g) = t₃ g := by
    intro γ hγ g
    simp only [ht₃]
    rw [hEN_B γ hγ g, hE'N_B γ hγ g]

  have hk : ∀ t : AdelicGL2 (𝓞 F) F → ℂ, Continuous t →
      IntegrableOn (K t) Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) := fun t ht =>
    WindowedSiegel.integrableOn_adelicGLHaar_of_forall_norm_le_of_forall_eq_zero_of_lt_adelicHeight F
      hc hα hTc hΦ₀S hΦ₀s hΦ₀m ht
      (measurable_slab_shell_mul F (T := Real.exp R) (T' := Real.exp R') hslab ht).aestronglyMeasurable
      (fun g => norm_slab_shell_mul_le F (α := α) (β := β) (T := Real.exp R) (T' := Real.exp R') t g)
      (M := Real.exp R')
      (fun g hg => slab_shell_mul_eq_zero_of_lt F (α := α) (β := β) (T := Real.exp R) (T' := Real.exp R') t hg)

  have hpt : ∀ g : AdelicGL2 (𝓞 F) F,
      Λ R' E g * (starRingEnd ℂ) (Λ R' E' g) - Λ R E g * (starRingEnd ℂ) (Λ R E' g) =
        (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) * (t₁ g + t₂ g - t₃ g) := fun g =>
    lambdaT_mul_conj_lambdaT_sub_lambdaT_mul_conj_lambdaT
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (fun x => unipotentGL2 x)
      (NumberField.AdelicHeight.adelicHeight F) hTT' E E' g
  have hcongr : ∫ g in Φ₀, (Λ R' E g * (starRingEnd ℂ) (Λ R' E' g) - Λ R E g * (starRingEnd ℂ) (Λ R E' g))
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ g in Φ₀, (K t₁ g + K t₂ g - K t₃ g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    refine setIntegral_congr_fun₀ hΦ₀m fun g hg => ?_
    simp only [hpt g, hK, Set.indicator_of_mem (hΦ₀s hg)]
    ring

  have hunf : ∀ t : AdelicGL2 (𝓞 F) F → ℂ,
      (∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, t (globalPoints (𝓞 F) F γ * g) = t g) →
      ∫ g in Φ₀, K t g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        ∫ g in S', K t g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := fun t ht =>
    setIntegral_slab_shell_eq_setIntegral_of_isFundamentalDomain F (T' := Real.exp R') hΦ₀ hΦ₀s hslab hH
      hred hT hS' ht

  have hβ : ∀ t : AdelicGL2 (𝓞 F) F → ℂ, Continuous t →
      (∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, t (globalPoints (𝓞 F) F γ * g) = t g) →
      ∫ g in S', K t g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        ∫ q : RationalTorusUnipotentQuotient F,
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 (K t) q.out
            ∂(rationalTorusUnipotentQuotientMeasure F) := fun t ht htB =>
    (setIntegral_eq_integral_constantTerm_out_of_isFundamentalDomain_borel F (K t)
      (measurable_slab_shell_mul F (T := Real.exp R) (T' := Real.exp R') hslab ht)
      (slab_shell_mul_borel_mul F α β (Real.exp R) (Real.exp R') htB) S' hS'
      (lintegral_enorm_slab_shell_lt_top_of_integrableOn F (T' := Real.exp R') hΦ₀ hΦ₀s hslab hH hred hT hS'
        htB (hk t ht))).2

  have hX : ∀ t : AdelicGL2 (𝓞 F) F → ℂ,
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 (K t) = K t₃ →
      ∫ q : RationalTorusUnipotentQuotient F,
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 (K t) q.out
            ∂(rationalTorusUnipotentQuotientMeasure F) =
        ∫ q : RationalTorusUnipotentQuotient F, K t₃ q.out ∂(rationalTorusUnipotentQuotientMeasure F) :=
    fun t h => by rw [h]
  have hHu : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      NumberField.AdelicHeight.adelicHeight F (unipotentGL2 x * g) =
        NumberField.AdelicHeight.adelicHeight F g := adelicHeight_unipotentGL2_mul F
  have hENu := constantTerm_adelicBox_unipotentGL2_mul F (fun k h => hE (unipotentGL2 k) h)
  have hE'Nu := constantTerm_adelicBox_unipotentGL2_mul F (fun k h => hE' (unipotentGL2 k) h)
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) :=
    NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox F
  have hX₁ := hX t₁ (constantTerm_slab_shell_mul_conj_constantTerm_eq (F := F)
    (ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (E := E) (E' := E') (α := α) (β := β)
    (R := R) (R' := R') hHu hE'Nu)
  have hX₂ := hX t₂ (constantTerm_slab_shell_constantTerm_mul_conj_eq (F := F)
    (ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (E := E) (E' := E') (α := α) (β := β)
    (R := R) (R' := R') hHu hENu)
  have hX₃ := hX t₃ (constantTerm_slab_shell_constantTerm_mul_conj_constantTerm_eq (F := F)
    (ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) (E := E) (E' := E') (α := α) (β := β)
    (R := R) (R' := R') hHu hENu hE'Nu)

  have hk12 : IntegrableOn (fun g : AdelicGL2 (𝓞 F) F => K t₁ g + K t₂ g) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (hk t₁ ht₁c).add (hk t₂ ht₂c)
  rw [peterssonIntegral_zero F Φ₀ (Λ R' E) (Λ R' E'), peterssonIntegral_zero F Φ₀ (Λ R E) (Λ R E'),
    ← integral_sub hI' hI, hcongr, integral_sub hk12 (hk t₃ ht₃c),
    integral_add (hk t₁ ht₁c) (hk t₂ ht₂c), hunf t₁ hinv₁, hunf t₂ hinv₂, hunf t₃ hinv₃,
    hβ t₁ ht₁c hinv₁, hβ t₂ ht₂c hinv₂, hβ t₃ ht₃c hinv₃, hX₁, hX₂, hX₃]
  exact (add_sub_cancel_right _ _).trans rfl

end S_AutomorphicForm_peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm
end P2MW
export P2MW.S_AutomorphicForm_peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm (solution)
