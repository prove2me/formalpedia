-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one_of_forall_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/77e2cd41-4187-56c5-acea-b93af9018af4

import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal
import Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one_of_forall_isReal
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one_of_forall_isReal.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup ArchTypeFamily archCutSubmodule rowIsometrySubgroup₀ HasArchCharacterAt₀ adelicArchGLInclAt glFin_adelicArchGLIncl whittakerCoefficient CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent archWeightCharAt whittakerCoefficient_sum_smul_of_continuous CuspidalConstituent.coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal archRealGLAt ArchDir archDerivAt eq_of_glArch_eq_of_glFin_eq archRealGLAt_mul_comm_of_glArch_eq_one archDerivAt_comp_mul_right archCasimirAt_comp_mul_right exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy"
namespace TranslateTR34
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K]

theorem mul_comm_of_glArch_eq_one_of_glFin_eq_one {a b : AdelicGL2 (𝓞 K) K} (ha : glArch (𝓞 K) K a = 1)
    (hb : glFin (𝓞 K) K b = 1) : a * b = b * a :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, map_mul, ha, one_mul, mul_one])
    (by rw [map_mul, map_mul, hb, mul_one, one_mul])

theorem glFin_diagOne_of_snd_eq_one (ε : (AdeleRing (𝓞 K) K)ˣ) (hε : ((ε : AdeleRing (𝓞 K) K)).2 = 1) :
    glFin (𝓞 K) K (diagOne ε) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply, diagOne_coe_apply, Units.val_one]
  fin_cases i <;> fin_cases j <;> (try simp [Matrix.diagonal, hε]) <;> rfl

theorem adelicArchGLInclAt_mul_comm_of_glArch_eq_one (w : InfinitePlace K) (r : GL (Fin 2) w.Completion)
    {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) :
    adelicArchGLInclAt K w r * k = k * adelicArchGLInclAt K w r := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hk, mul_one, one_mul]
  · rw [map_mul, map_mul, adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl, mul_one, one_mul]

theorem whittakerCoefficient_comp_mul_right (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (k h : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ (fun x => φ (x * k)) α h = whittakerCoefficient K pins ψ φ α (h * k) := by
  simp only [whittakerCoefficient, mul_assoc]

theorem foldr_archDerivAt_comp_mul_right {w : InfinitePlace K} (hw : w.IsReal) (l : List ArchDir)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) :
    l.foldr (archDerivAt hw) (fun x => φ (x * k)) = fun x => l.foldr (archDerivAt hw) φ (x * k) := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [List.foldr_cons, List.foldr_cons, ih, archDerivAt_comp_mul_right hw d _ hk]

theorem lop_comp_mul_right {w : InfinitePlace K} (hw : w.IsReal) (cc : ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) :
    (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - cc • (archDerivAt hw .E z + archDerivAt hw .Fm z))
        (fun x => φ (x * k)) =
      fun x => (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - cc • (archDerivAt hw .E z + archDerivAt hw .Fm z)) φ (x * k) := by
  simp only [archDerivAt_comp_mul_right hw _ φ hk]
  funext x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]

theorem iterate_lop_comp_mul_right {w : InfinitePlace K} (hw : w.IsReal) (cc : ℂ) (n : ℕ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) :
    (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - cc • (archDerivAt hw .E z + archDerivAt hw .Fm z))^[n]
        (fun x => φ (x * k)) =
      fun x => ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - cc • (archDerivAt hw .E z + archDerivAt hw .Fm z))^[n] φ) (x * k) := by
  have h : Function.Semiconj (fun ψ : AdelicGL2 (𝓞 K) K → ℂ => fun x => ψ (x * k))
      (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - cc • (archDerivAt hw .E z + archDerivAt hw .Fm z))
      (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - cc • (archDerivAt hw .E z + archDerivAt hw .Fm z)) := by
    intro ψ
    exact (lop_comp_mul_right hw cc ψ hk).symm
  exact ((h.iterate_right n) φ).symm

theorem hasArchCharacterAt₀_comp_mul_right (w : InfinitePlace K) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : HasArchCharacterAt₀ K w χ φ)
    {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) :
    HasArchCharacterAt₀ K w χ (fun x => φ (x * k)) := by
  intro r g
  show φ (g * adelicArchGLInclAt K w (r : GL (Fin 2) w.Completion) * k) = (χ r : ℂ) * φ (g * k)
  rw [mul_assoc, adelicArchGLInclAt_mul_comm_of_glArch_eq_one w _ hk, ← mul_assoc]
  exact hφ r (g * k)

theorem pure_translate
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (hyn : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv n) y)
    (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a * g)‖ ≤ C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by
  classical
  choose nw hnw using hyn
  obtain ⟨hyc, hyG, hyZ, hreg, ⟨C₀, hC₀⟩, lam, hcas, harch⟩ :=
    AutomorphicForm.CuspidalConstituent.coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV hreal N hN tys y hy w₀ hξ nw hnw
  have h1 : ∀ v v' : InfinitePlace K, v.IsComplex → v'.IsComplex → v = v' :=
    fun v _ hv _ => absurd hv (InfinitePlace.not_isComplex_iff_isReal.mpr (hreal v))
  have hdet : ∀ h : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (h * g)) ^ (w₀ / 2) =
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det h) ^ (w₀ / 2) := fun h => by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul,
      Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos _).le (NumberField.TateGlobal.ideleNorm_pos _).le, mul_comm]
  obtain ⟨δ, hδ, C, hC⟩ :=
    AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
      K h1 (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ξ w₀ hξ (fun h => y (h * g))
      (continuous_rightTranslate K hyc g)
      (fun γ h => by show y (globalPoints (𝓞 K) K γ * h * g) = y (h * g); rw [mul_assoc, hyG])
      (fun z h => by
        show y (centralScalar (𝓞 K) K z * h * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y (h * g)
        rw [mul_assoc, hyZ])
      nw lam
      (fun v hv => hasArchCharacterAt₀_comp_mul_right v _ (hnw v hv) hg)
      (fun v hv l => by
        rw [foldr_archDerivAt_comp_mul_right hv l y hg]
        exact ⟨(hreg v hv l).1.comp_mul_right hg, continuous_rightTranslate K (hreg v hv l).2 g⟩)
      ⟨C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2), fun h => by
        rw [whittakerCoefficient_comp_mul_right]
        exact (hC₀ (h * g)).trans_eq (by rw [hdet h]; ring)⟩
      (fun v hv => by rw [archCasimirAt_comp_mul_right hv y hg, hcas v hv]; rfl)
      (fun v hv => by
        rcases harch v hv with hA | ⟨ε, k₀, M, hε, hk₀, hlam, hn, hvan, Mgr, hMgr⟩ | ⟨hlam0, hinv⟩
        · exact Or.inl hA
        · refine Or.inr (Or.inl ⟨ε, k₀, M, hε, hk₀, hlam, hn, ?_,
            Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2), fun h => ?_⟩)
          · rw [iterate_lop_comp_mul_right hv _ (M + 1) y hg, hvan]; rfl
          · rw [iterate_lop_comp_mul_right hv _ M y hg, whittakerCoefficient_comp_mul_right]
            exact (hMgr (h * g)).trans_eq (by rw [hdet h]; ring)
        · refine Or.inr (Or.inr ⟨hlam0, fun h r hr => ?_⟩)
          show y (h * archRealGLAt hv r * g) = y (h * g)
          rw [mul_assoc, archRealGLAt_mul_comm_of_glArch_eq_one hv r hg, ← mul_assoc]
          exact hinv (h * g) r hr)
      (fun v hv => absurd hv (InfinitePlace.not_isComplex_iff_isReal.mpr (hreal v)))
  refine ⟨δ, hδ, C, fun a ha => ?_⟩
  have h := hC a ha
  rwa [whittakerCoefficient_comp_mul_right] at h

theorem cut_translate
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a * g)‖ ≤ C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by
  classical
  obtain ⟨m, ys, hys, hpure, hsum⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV y hy
  have hJ : ∀ j : Fin m, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys j) 1
              (diagOne a * g)‖ ≤ C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := fun j =>
    pure_translate K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV hreal (ys j) (hys j) w₀ hξ (hpure j) g hg
  choose δs hδs Cs hCs using hJ
  let δ : ℝ := if h : (Finset.univ : Finset (Fin m)).Nonempty then Finset.univ.inf' h δs else 1
  have hδpos : 0 < δ := by
    simp only [δ]
    split_ifs with h
    · exact (Finset.lt_inf'_iff h).2 fun i _ => hδs i
    · exact one_pos
  have hδle : ∀ i : Fin m, δ ≤ δs i := by
    intro i
    have h : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i, Finset.mem_univ i⟩
    simp only [δ, dif_pos h]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  refine ⟨δ, hδpos, ∑ j, max (Cs j) 0, ?_⟩
  intro a ha2

  have hcont : ∀ j : Fin m, Continuous (ys j) := by
    intro j
    have hjV : ys j ∈ cuspKFiniteSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ := hV.1.le (hys j).1.1
    refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hjV
    · rintro φ ⟨-, hφc, -⟩; exact hφc
    · exact continuous_zero
    · intro u w _ _ hu hw; exact hu.add hw
    · intro r u _ hu; exact hu.const_smul r

  have hlin : whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a * g) = ∑ j, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys j) 1 (diagOne a * g) := by
    have h := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (NumberField.StandardAddChar.stdAddChar K) (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
      m ys hcont (fun _ => 1) 1 (diagOne a * g)
    have hy' : y = fun x => ∑ j, (1 : ℂ) * ys j x := by
      rw [hsum]; funext x; simp [Finset.sum_apply]
    rw [hy', h]; simp
  rw [hlin]
  have hu : ∀ w : InfinitePlace K, 0 < ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := fun w => by
    have h : ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 :=
      congrArg (fun x : AdeleRing (𝓞 K) K => x.1 w) a.mul_inv
    exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
  have hmpos : ∀ w : InfinitePlace K, 0 < min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := fun w => lt_min one_pos (hu w)
  have hmle : ∀ w : InfinitePlace K, min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ≤ 1 := fun w => min_le_left _ _
  have hfac_nonneg : ∀ (w : InfinitePlace K) (e : ℝ), 0 ≤ ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
      (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ e := fun w e =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (hmpos w).le _)
  set P : ℝ := ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) with hP
  have hPnonneg : 0 ≤ P := Finset.prod_nonneg fun w _ => hfac_nonneg w _
  have hPle : ∀ j : Fin m, ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δs j) ≤ P := by
    intro j
    refine Finset.prod_le_prod (fun w _ => hfac_nonneg w _) fun w _ => ?_
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
    exact Real.rpow_le_rpow_of_exponent_ge (hmpos w) (hmle w) (hδle j)
  have hterm : ∀ j : Fin m, ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys j) 1 (diagOne a * g)‖ ≤
      max (Cs j) 0 * P := by
    intro j
    refine (hCs j a ha2).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left (Cs j) 0) (Finset.prod_nonneg fun w _ => hfac_nonneg w _)).trans ?_
    exact mul_le_mul_of_nonneg_left (hPle j) (le_max_right _ _)
  calc ‖∑ j, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys j) 1 (diagOne a * g)‖
      ≤ ∑ j, ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys j) 1 (diagOne a * g)‖ := norm_sum_le _ _
    _ ≤ ∑ j, max (Cs j) 0 * P := Finset.sum_le_sum fun j _ => hterm j
    _ = (∑ j, max (Cs j) 0) * P := by rw [Finset.sum_mul]

end AutomorphicForm.TranslateTR34

end

open AutomorphicForm.TranslateTR34

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a * k * g)‖ ≤ C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by
  classical
  obtain ⟨m, ys, M, hys, hK⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV x hx w₀ hξ
  have hJ : ∀ i : Fin m, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys i) 1
              (diagOne a * g)‖ ≤ C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := fun i =>
    cut_translate K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV hreal (ys i) (hys i) w₀ hξ g hg
  choose δs hδs Cs hCs using hJ
  let δ : ℝ := if h : (Finset.univ : Finset (Fin m)).Nonempty then Finset.univ.inf' h δs else 1
  have hδpos : 0 < δ := by
    simp only [δ]
    split_ifs with h
    · exact (Finset.lt_inf'_iff h).2 fun i _ => hδs i
    · exact one_pos
  have hδle : ∀ i : Fin m, δ ≤ δs i := by
    intro i
    have h : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i, Finset.mem_univ i⟩
    simp only [δ, dif_pos h]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  refine ⟨δ, hδpos, ∑ i, |M| * max (Cs i) 0, ?_⟩
  intro k hk1 hk2 a ha2
  obtain ⟨cs, ε, hε2, hεw, hεN, hcs, hW⟩ := hK k hk1 hk2
  have haε2 : (((a * ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 = 1 := by
    rw [Units.val_mul]
    change ((a : AdeleRing (𝓞 K) K)).2 * ((ε : AdeleRing (𝓞 K) K)).2 = 1
    rw [ha2, hε2, one_mul]
  have hcomp : ∀ w : InfinitePlace K, ‖(((a * ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w‖ =
      ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := fun w => by
    have h : (((a * ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w =
        ((a : AdeleRing (𝓞 K) K)).1 w * ((ε : AdeleRing (𝓞 K) K)).1 w := rfl
    rw [h, norm_mul, hεw w, mul_one]
  have hu : ∀ w : InfinitePlace K, 0 < ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := fun w => by
    have h : ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 :=
      congrArg (fun x : AdeleRing (𝓞 K) K => x.1 w) a.mul_inv
    exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
  have hmpos : ∀ w : InfinitePlace K, 0 < min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := fun w => lt_min one_pos (hu w)
  have hmle : ∀ w : InfinitePlace K, min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ≤ 1 := fun w => min_le_left _ _
  have hfac_nonneg : ∀ (w : InfinitePlace K) (e : ℝ), 0 ≤ ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
      (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ e := fun w e =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (hmpos w).le _)
  set P : ℝ := ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) with hP
  have hPnonneg : 0 ≤ P := Finset.prod_nonneg fun w _ => hfac_nonneg w _
  have hPε : ∀ i : Fin m, ∏ w : InfinitePlace K, (‖(((a * ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖(((a * ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w‖) ^ δs i) ≤ P := by
    intro i
    simp_rw [hcomp]
    refine Finset.prod_le_prod (fun w _ => hfac_nonneg w _) fun w _ => ?_
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
    exact Real.rpow_le_rpow_of_exponent_ge (hmpos w) (hmle w) (hδle i)
  have hkg : diagOne a * k * g = diagOne a * g * k := by
    rw [mul_assoc, mul_assoc, mul_comm_of_glArch_eq_one_of_glFin_eq_one hg hk1]
  have hεg : diagOne a * g * diagOne ε = diagOne (a * ε) * g := by
    rw [map_mul, mul_assoc, mul_assoc,
      mul_comm_of_glArch_eq_one_of_glFin_eq_one hg (glFin_diagOne_of_snd_eq_one ε hε2)]
  rw [hkg, hW (diagOne a * g), hεg]
  have hterm : ∀ i : Fin m,
      ‖cs i * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys i) 1
              (diagOne (a * ε) * g)‖ ≤
        |M| * max (Cs i) 0 * P := by
    intro i
    rw [norm_mul]
    have h1 : ‖cs i‖ ≤ |M| := (hcs i).trans (le_abs_self M)
    have h2 := hCs i (a * ε) haε2
    have h3 : Cs i * ∏ w : InfinitePlace K, (‖(((a * ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖(((a * ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w‖) ^ δs i) ≤
        max (Cs i) 0 * P :=
      (mul_le_mul_of_nonneg_right (le_max_left (Cs i) 0)
        (Finset.prod_nonneg fun w _ => by rw [hcomp]; exact hfac_nonneg w _)).trans
        (mul_le_mul_of_nonneg_left (hPε i) (le_max_right _ _))
    calc ‖cs i‖ * ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys i) 1
              (diagOne (a * ε) * g)‖
        ≤ |M| * (max (Cs i) 0 * P) := mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (abs_nonneg M)
      _ = |M| * max (Cs i) 0 * P := by ring
  calc ‖∑ i, cs i * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys i) 1
              (diagOne (a * ε) * g)‖
      ≤ ∑ i, ‖cs i * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys i) 1
              (diagOne (a * ε) * g)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |M| * max (Cs i) 0 * P := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, |M| * max (Cs i) 0) * P := by rw [Finset.sum_mul]

end S_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one_of_forall_isReal
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one_of_forall_isReal (solution)
