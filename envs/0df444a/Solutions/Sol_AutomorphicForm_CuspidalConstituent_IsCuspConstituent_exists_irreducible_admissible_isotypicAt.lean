-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.IsCuspConstituent.exists_irreducible_admissible_isotypicAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b47f3afe-ce03-501a-b3ce-4be88219255f

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_IntegralSubgroupCompact
import Theorems.Thm_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_finiteDimensional_of_forall_rightTranslate_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_exists_irreducible_admissible_isotypicAt
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CuspidalConstituent.rightTranslate CuspidalConstituent.rightTranslate_apply CuspidalConstituent.rightTranslate_rightTranslate CuspidalConstituent.rightTranslate_add CuspidalConstituent.rightTranslate_smul CuspidalConstituent.rightTranslate_zero CuspidalConstituent.IsCuspSubrep CuspidalConstituent.IsCuspConstituent rightConv_add_left typeSubmodule comp_mul_mem_typeSubmodule_of_commute comp_mul_mem_typeSubmodule_of_hom comp_mul_mem_iSup_of_forall rowIsometryInclAt₀ rowIsometryInclAt₀_apply archTypeSubmoduleAt archDualTypeSubmoduleAt ArchTypeFamily archCutSubmodule archDualCutSubmodule mem_archCutSubmodule_iff mem_archDualCutSubmodule_iff archCutSubmodule_mono IsArchBiFinite glFin_rowIsometryInclAt₀ productionPinsGeneral CarrierPins AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth rightConv rightConv_zero_right rowIsometrySubgroup₀ archGLIncl adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl archEntries archEntries_apply IsArchTestFactor IsFinTestFactor IsFactorizableTestFn exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen continuous_and_hasCompactSupport_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply CuspidalConstituent.IsCuspConstituent.finiteDimensional_of_forall_rightTranslate_eq"
namespace CuspidalConstituent
p2m_export "AutomorphicForm.CuspidalConstituent" "rightTranslate rightTranslate_apply rightRegular rightRegular_apply rightTranslate_rightTranslate rightTranslate_add rightTranslate_smul rightTranslate_zero cuspKFiniteSubmodule IsCuspSubrep IsCuspConstituent IsCuspConstituent.finiteDimensional_of_forall_rightTranslate_eq"
namespace LocalComponent
p2m_open "AutomorphicForm.CuspidalConstituent AutomorphicForm"

section Spine

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section FiniteAdelic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem ext_of_finComponent {a b : GL (Fin 2) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R, finComponent R K w a = finComponent R K w b) : a = b :=
  Matrix.GeneralLinearGroup.ext fun i j => FiniteAdeleRing.ext K fun w => by
    have hw := congrArg
      (fun g : GL (Fin 2) (w.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) (h w)
    simpa only [finComponent_apply] using hw

variable (v : HeightOneSpectrum R)

private theorem localEmbed_mul_comm {h : GL (Fin 2) (FiniteAdeleRing R K)}
    (hh : finComponent R K v h = 1) (g : GL (Fin 2) (v.adicCompletion K)) :
    localEmbed R K v g * h = h * localEmbed R K v g := by
  refine ext_of_finComponent fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [map_mul, map_mul, finComponent_localEmbed_self, hh, mul_one, one_mul]
  · rw [map_mul, map_mul, finComponent_localEmbed_of_ne R K v g hw, mul_one, one_mul]

private def awayPart (k : GL (Fin 2) (FiniteAdeleRing R K)) : GL (Fin 2) (FiniteAdeleRing R K) :=
  k * (localEmbed R K v (finComponent R K v k))⁻¹

private theorem finComponent_awayPart (k : GL (Fin 2) (FiniteAdeleRing R K)) :
    finComponent R K v (awayPart v k) = 1 := by
  rw [awayPart, map_mul, map_inv, finComponent_localEmbed_self, mul_inv_cancel]

private theorem awayPart_mul_localEmbed (k : GL (Fin 2) (FiniteAdeleRing R K)) :
    awayPart v k * localEmbed R K v (finComponent R K v k) = k := by
  rw [awayPart, inv_mul_cancel_right]

private theorem awayPart_eq_self_of_finComponent_eq_one {k : GL (Fin 2) (FiniteAdeleRing R K)}
    (hk : finComponent R K v k = 1) : awayPart v k = k := by
  rw [awayPart, hk, map_one, inv_one, mul_one]

private theorem awayPart_localEmbed (g : GL (Fin 2) (v.adicCompletion K)) : awayPart v (localEmbed R K v g) = 1 := by
  rw [awayPart, finComponent_localEmbed_self, mul_inv_cancel]

private theorem finComponent_awayPart_of_ne (k : GL (Fin 2) (FiniteAdeleRing R K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : finComponent R K w (awayPart v k) = finComponent R K w k := by
  rw [awayPart, map_mul, map_inv, finComponent_localEmbed_of_ne R K v _ hw, inv_one, mul_one]

private theorem awayPart_mul (k k' : GL (Fin 2) (FiniteAdeleRing R K)) :
    awayPart v (k * k') = awayPart v k * awayPart v k' := by
  refine ext_of_finComponent fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [map_mul, finComponent_awayPart, finComponent_awayPart, finComponent_awayPart, mul_one]
  · rw [map_mul, finComponent_awayPart_of_ne v _ hw, finComponent_awayPart_of_ne v _ hw,
      finComponent_awayPart_of_ne v _ hw, map_mul]

end FiniteAdelic

section Action

variable (F : Type) [Field F] [NumberField F]

private theorem eq_finEmbed_glFin {h : AdelicGL2 (𝓞 F) F} (hh : h ∈ finiteAdelicGL2Subgroup F) :
    h = finEmbed (𝓞 F) F (glFin (𝓞 F) F h) := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hh
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · have h₁ := congrArg
      (fun g : GL (Fin 2) (InfiniteAdeleRing F) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) hh
    have h₂ := congrArg
      (fun g : GL (Fin 2) (InfiniteAdeleRing F) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
      (glArch_finEmbed (𝓞 F) F (glFin (𝓞 F) F h))
    simp only [glArch_apply] at h₁ h₂
    rw [h₁, h₂]
  · have h₂ := congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
      (glFin_finEmbed (𝓞 F) F (glFin (𝓞 F) F h))
    simp only [glFin_apply] at h₂
    rw [h₂]

private def finAct (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
  rightRegular F (finEmbed (𝓞 F) F k)

private theorem finAct_apply (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    finAct F k φ = rightTranslate F (finEmbed (𝓞 F) F k) φ := rfl

private theorem finAct_mul (k k' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    finAct F (k * k') φ = finAct F k (finAct F k' φ) := by
  simp only [finAct_apply, map_mul, rightTranslate_rightTranslate]

private theorem finAct_one (φ : AdelicGL2 (𝓞 F) F → ℂ) : finAct F 1 φ = φ := by
  rw [finAct_apply, map_one]
  funext x
  rw [rightTranslate_apply, mul_one]

private theorem finAct_mem {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hV : IsCuspSubrep F pins ξ V) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ V) : finAct F k φ ∈ V :=
  hV.rightTranslate_fin_mem _ (by rw [mem_finiteAdelicGL2Subgroup_iff, glArch_finEmbed]) φ hφ

variable (v : HeightOneSpectrum (𝓞 F))

private def locAct (g : GL (Fin 2) (v.adicCompletion F)) : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
  finAct F (localEmbed (𝓞 F) F v g)

private theorem locAct_apply (g : GL (Fin 2) (v.adicCompletion F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    locAct F v g φ = rightTranslate F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v g)) φ := rfl

private theorem locAct_mul (g g' : GL (Fin 2) (v.adicCompletion F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    locAct F v (g * g') φ = locAct F v g (locAct F v g' φ) := by
  simp only [locAct, map_mul, finAct_mul]

private theorem locAct_one (φ : AdelicGL2 (𝓞 F) F → ℂ) : locAct F v 1 φ = φ := by
  rw [locAct, map_one, finAct_one]

private theorem finAct_locAct_comm {h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hh : finComponent (𝓞 F) F v h = 1)
    (g : GL (Fin 2) (v.adicCompletion F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    finAct F h (locAct F v g φ) = locAct F v g (finAct F h φ) := by
  rw [locAct, ← finAct_mul, ← localEmbed_mul_comm v hh g, finAct_mul]

private theorem finAct_eq_awayPart_locAct (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    finAct F k φ = finAct F (awayPart v k) (locAct F v (finComponent (𝓞 F) F v k) φ) := by
  rw [locAct, ← finAct_mul, awayPart_mul_localEmbed]

end Action

section Generation

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable (V Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))

private def IsLocIntertwiner (b : ↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) : Prop :=
  (∀ y : ↥Y, b y ∈ V) ∧
    ∀ (g : GL (Fin 2) (v.adicCompletion F)) (y : ↥Y) (h : locAct F v g (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ Y),
      b ⟨locAct F v g y, h⟩ = locAct F v g (b y)

private def intertwinerSpan : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | ∃ (n : ℕ) (y : Fin n → ↥Y) (b : Fin n → (↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))),
    (∀ i, IsLocIntertwiner F v V Y (b i)) ∧ φ = ∑ i, b i (y i)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  add_mem' := by
    rintro _ _ ⟨n, y, b, hb, rfl⟩ ⟨m, y', b', hb', rfl⟩
    refine ⟨n + m, Fin.append y y', Fin.append b b', fun i => ?_, ?_⟩
    · induction i using Fin.addCases with
      | left i => simpa only [Fin.append_left] using hb i
      | right i => simpa only [Fin.append_right] using hb' i
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  smul_mem' := by
    rintro c _ ⟨n, y, b, hb, rfl⟩
    refine ⟨n, fun i => c • y i, b, hb, ?_⟩
    rw [Finset.smul_sum]
    simp only [map_smul]

variable {F v V Y}

private theorem mem_intertwinerSpan_iff {φ : AdelicGL2 (𝓞 F) F → ℂ} :
    φ ∈ intertwinerSpan F v V Y ↔ ∃ (n : ℕ) (y : Fin n → ↥Y) (b : Fin n → (↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))),
      (∀ i, IsLocIntertwiner F v V Y (b i)) ∧ φ = ∑ i, b i (y i) :=
  Iff.rfl

private theorem apply_mem_intertwinerSpan {b : ↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)} (hb : IsLocIntertwiner F v V Y b)
    (y : ↥Y) : b y ∈ intertwinerSpan F v V Y :=
  ⟨1, fun _ => y, fun _ => b, fun _ => hb, by simp⟩

private theorem intertwinerSpan_le : intertwinerSpan F v V Y ≤ V := by
  rintro _ ⟨n, y, b, hb, rfl⟩
  exact V.sum_mem fun i _ => (hb i).1 (y i)

private theorem le_intertwinerSpan (hYV : Y ≤ V) : Y ≤ intertwinerSpan F v V Y := by
  intro y hy
  have hb : IsLocIntertwiner F v V Y Y.subtype := ⟨fun y => hYV y.2, fun g y h => rfl⟩
  exact apply_mem_intertwinerSpan hb ⟨y, hy⟩

private def postcompose (T : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hadd : ∀ ψ ∈ V, ∀ ψ' ∈ V, T (ψ + ψ') = T ψ + T ψ') (hsmul : ∀ (c : ℂ), ∀ ψ ∈ V, T (c • ψ) = c • T ψ)
    (b : ↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) (hbV : ∀ y : ↥Y, b y ∈ V) : ↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun y := T (b y)
  map_add' y y' := by rw [map_add, hadd _ (hbV y) _ (hbV y')]
  map_smul' c y := by rw [map_smul, hsmul c _ (hbV y), RingHom.id_apply]

private theorem postcompose_apply (T : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hadd : ∀ ψ ∈ V, ∀ ψ' ∈ V, T (ψ + ψ') = T ψ + T ψ') (hsmul : ∀ (c : ℂ), ∀ ψ ∈ V, T (c • ψ) = c • T ψ)
    (b : ↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) (hbV : ∀ y : ↥Y, b y ∈ V) (y : ↥Y) :
    postcompose T hadd hsmul b hbV y = T (b y) := rfl

private theorem isLocIntertwiner_postcompose {T : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ)}
    (hTV : ∀ ψ ∈ V, T ψ ∈ V)
    (hadd : ∀ ψ ∈ V, ∀ ψ' ∈ V, T (ψ + ψ') = T ψ + T ψ') (hsmul : ∀ (c : ℂ), ∀ ψ ∈ V, T (c • ψ) = c • T ψ)
    (hcomm : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ ψ ∈ V, T (locAct F v g ψ) = locAct F v g (T ψ))
    {b : ↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)} (hb : IsLocIntertwiner F v V Y b) :
    IsLocIntertwiner F v V Y (postcompose T hadd hsmul b hb.1) := by
  refine ⟨fun y => hTV _ (hb.1 y), fun g y h => ?_⟩
  rw [postcompose_apply, postcompose_apply, hb.2 g y h, hcomm g _ (hb.1 y)]

private theorem apply_mem_intertwinerSpan_of_comm {T : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ)}
    (hTV : ∀ ψ ∈ V, T ψ ∈ V)
    (hadd : ∀ ψ ∈ V, ∀ ψ' ∈ V, T (ψ + ψ') = T ψ + T ψ') (hsmul : ∀ (c : ℂ), ∀ ψ ∈ V, T (c • ψ) = c • T ψ)
    (hcomm : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ ψ ∈ V, T (locAct F v g ψ) = locAct F v g (T ψ))
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ intertwinerSpan F v V Y) : T φ ∈ intertwinerSpan F v V Y := by
  obtain ⟨n, y, b, hb, rfl⟩ := hφ
  have hT0 : T 0 = 0 := by simpa using hsmul 0 0 V.zero_mem
  have hsum : ∀ (m : ℕ) (ψ : Fin m → (AdelicGL2 (𝓞 F) F → ℂ)), (∀ i, ψ i ∈ V) → T (∑ i, ψ i) = ∑ i, T (ψ i) := by
    intro m ψ hψ
    induction m with
    | zero => simp [hT0]
    | succ m ih =>
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hadd _ (V.sum_mem fun i _ => hψ _) _ (hψ _),
          ih (fun i => ψ i.castSucc) fun i => hψ _]
  rw [hsum n (fun i => b i (y i)) fun i => (hb i).1 (y i)]
  exact Submodule.sum_mem _ fun i _ =>
    apply_mem_intertwinerSpan (isLocIntertwiner_postcompose hTV hadd hsmul hcomm (hb i)) (y i)

private theorem isLocIntertwiner_finAct_comp {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} (hV : IsCuspSubrep F pins ξ V)
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hh : finComponent (𝓞 F) F v h = 1)
    {b : ↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)} (hb : IsLocIntertwiner F v V Y b) :
    IsLocIntertwiner F v V Y ((finAct F h).comp b) := by
  refine ⟨fun y => finAct_mem F hV h (hb.1 y), fun g y hgy => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hb.2 g y hgy, finAct_locAct_comm F v hh]

private theorem locAct_mem_intertwinerSpan (hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y)
    (g : GL (Fin 2) (v.adicCompletion F)) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ intertwinerSpan F v V Y) :
    locAct F v g φ ∈ intertwinerSpan F v V Y := by
  obtain ⟨n, y, b, hb, rfl⟩ := hφ
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := (hb i).2 g (y i) (hY g _ (y i).2)
  rw [← this]
  exact apply_mem_intertwinerSpan (hb i) _

private theorem finAct_mem_intertwinerSpan {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} (hV : IsCuspSubrep F pins ξ V)
    (hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y)
    (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ intertwinerSpan F v V Y) :
    finAct F k φ ∈ intertwinerSpan F v V Y := by
  rw [finAct_eq_awayPart_locAct F v k]
  obtain ⟨n, y, b, hb, hsum⟩ := locAct_mem_intertwinerSpan hY (finComponent (𝓞 F) F v k) hφ
  rw [hsum, map_sum]
  exact Submodule.sum_mem _ fun i _ =>
    apply_mem_intertwinerSpan (isLocIntertwiner_finAct_comp hV (finComponent_awayPart v k) (hb i)) (y i)

variable (F V) in

private def HasFiniteExpansion (f : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∃ T : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ),
    (∀ ψ ∈ V, T ψ ∈ V) ∧
    (∀ (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)), ∀ ψ ∈ V, T (finAct F k ψ) = finAct F k (T ψ)) ∧
    (∀ ψ ∈ V, ∀ ψ' ∈ V, T (ψ + ψ') = T ψ + T ψ') ∧ (∀ (c : ℂ), ∀ ψ ∈ V, T (c • ψ) = c • T ψ) ∧
    ∀ ψ ∈ V, ∃ (n : ℕ) (a : Fin n → GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (c : Fin n → ℂ),
      rightConv F ψ f = ∑ i, c i • finAct F (a i) (T ψ)

private theorem rightConv_mem_intertwinerSpan {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} (hV : IsCuspSubrep F pins ξ V)
    (hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : HasFiniteExpansion F V f)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ intertwinerSpan F v V Y) : rightConv F φ f ∈ intertwinerSpan F v V Y := by
  obtain ⟨T, hTV, hTcomm, hadd, hsmul, hexp⟩ := hf
  obtain ⟨n, a, c, hconv⟩ := hexp φ (intertwinerSpan_le hφ)
  rw [hconv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (finAct_mem_intertwinerSpan hV hY (a i) ?_)
  exact apply_mem_intertwinerSpan_of_comm hTV hadd hsmul (fun g ψ hψ => hTcomm _ ψ hψ) hφ

private theorem intertwinerSpan_eq {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} (hV : IsCuspConstituent F pins ξ V)
    (hexp : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
      IsFactorizableTestFn F f → IsArchBiFinite F tys f → HasFiniteExpansion F V f)
    (harch : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
      (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)),
      rowIsometryInclAt₀ F w k * finEmbed (𝓞 F) F x = finEmbed (𝓞 F) F x * rowIsometryInclAt₀ F w k)
    (hYV : Y ≤ V) (hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y) (hY0 : Y ≠ ⊥) :
    intertwinerSpan F v V Y = V := by
  have hsub : IsCuspSubrep F pins ξ (intertwinerSpan F v V Y) := by
    refine ⟨intertwinerSpan_le.trans hV.1.le, fun h hh φ hφ => ?_, fun w k φ hφ => ?_, fun f tys hf hbf φ hφ => ?_⟩
    · have hmem := finAct_mem_intertwinerSpan hV.1 hY (glFin (𝓞 F) F h) hφ
      rw [finAct_apply, ← eq_finEmbed_glFin F hh] at hmem
      exact hmem
    · obtain ⟨n, y, b, hb, rfl⟩ := hφ
      rw [← rightRegular_apply, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hb' : IsLocIntertwiner F v V Y ((rightRegular F (rowIsometryInclAt₀ F w k)).comp (b i)) := by
        refine ⟨fun y => hV.1.rightTranslate_arch_mem w k _ ((hb i).1 y), fun g y hgy => ?_⟩
        rw [LinearMap.comp_apply, LinearMap.comp_apply, (hb i).2 g y hgy]
        simp only [locAct_apply, rightRegular_apply, rightTranslate_rightTranslate]
        rw [harch w k]
      exact apply_mem_intertwinerSpan hb' (y i)
    · exact rightConv_mem_intertwinerSpan hV.1 hY (hexp f tys hf hbf) hφ
  rcases hV.2.2 _ hsub intertwinerSpan_le with h | h
  · exfalso
    exact hY0 (eq_bot_iff.mpr (h ▸ le_intertwinerSpan hYV))
  · exact h

private theorem exists_eq_sum_of_mem {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} (hV : IsCuspConstituent F pins ξ V)
    (hexp : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
      IsFactorizableTestFn F f → IsArchBiFinite F tys f → HasFiniteExpansion F V f)
    (harch : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
      (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)),
      rowIsometryInclAt₀ F w k * finEmbed (𝓞 F) F x = finEmbed (𝓞 F) F x * rowIsometryInclAt₀ F w k)
    (hYV : Y ≤ V) (hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y) (hY0 : Y ≠ ⊥)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ V) :
    ∃ (n : ℕ) (y : Fin n → ↥Y) (b : Fin n → (↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))),
      (∀ i, IsLocIntertwiner F v V Y (b i)) ∧ φ = ∑ i, b i (y i) := by
  rw [← intertwinerSpan_eq hV hexp harch hYV hY hY0] at hφ
  exact mem_intertwinerSpan_iff.mp hφ

end Generation

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private def finFixing (φ : AdelicGL2 (𝓞 F) F → ℂ) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) where
  carrier := {k | finAct F k φ = φ}
  one_mem' := finAct_one F φ
  mul_mem' := fun {a b} ha hb => by
    show finAct F (a * b) φ = φ
    rw [finAct_mul, hb, ha]
  inv_mem' := fun {a} ha => by
    show finAct F a⁻¹ φ = φ
    conv_lhs => rw [← ha]
    rw [← finAct_mul, inv_mul_cancel, finAct_one]

private theorem mem_finFixing_iff {φ : AdelicGL2 (𝓞 F) F → ℂ} {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} :
    k ∈ finFixing F φ ↔ finAct F k φ = φ :=
  Iff.rfl

private def awayHom : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) where
  toFun := awayPart v
  map_one' := by simp only [awayPart, map_one, inv_one, mul_one]
  map_mul' := awayPart_mul v

private theorem awayHom_apply (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : awayHom F v k = awayPart v k := rfl

private theorem continuous_awayHom (hι : Continuous (localEmbed (𝓞 F) F v)) : Continuous (awayHom F v) := by
  show Continuous fun k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    k * (localEmbed (𝓞 F) F v (finComponent (𝓞 F) F v k))⁻¹
  exact continuous_id.mul (hι.comp (continuous_finComponent (R := 𝓞 F) (K := F) v)).inv

private def locFixed (L : Subgroup (GL (Fin 2) (v.adicCompletion F))) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | ∀ l ∈ L, locAct F v l φ = φ}
  zero_mem' := fun l _ => map_zero _
  add_mem' := fun {a b} ha hb l hl => by rw [map_add, ha l hl, hb l hl]
  smul_mem' := fun c {a} ha l hl => by rw [map_smul, ha l hl]

private def awayFixed (U : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | ∀ h ∈ U, finComponent (𝓞 F) F v h = 1 → finAct F h φ = φ}
  zero_mem' := fun h _ _ => map_zero _
  add_mem' := fun {a b} ha hb h hU hh => by rw [map_add, ha h hU hh, hb h hU hh]
  smul_mem' := fun c {a} ha h hU hh => by rw [map_smul, ha h hU hh]

variable {F v}

private theorem locAct_mem_awayFixed {U : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))}
    (g : GL (Fin 2) (v.adicCompletion F)) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ awayFixed F v U) :
    locAct F v g φ ∈ awayFixed F v U := fun h hU hh => by
  rw [finAct_locAct_comm F v hh, hφ h hU hh]

variable {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}

variable (v) in

private def subRep (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hW : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ φ ∈ W, locAct F v g φ ∈ W) :
    Representation ℂ (GL (Fin 2) (v.adicCompletion F)) ↥W where
  toFun g := (locAct F v g).restrict (hW g)
  map_one' := by
    refine LinearMap.ext fun φ => Subtype.ext ?_
    show locAct F v 1 (φ : AdelicGL2 (𝓞 F) F → ℂ) = φ
    exact locAct_one F v _
  map_mul' g g' := by
    refine LinearMap.ext fun φ => Subtype.ext ?_
    show locAct F v (g * g') (φ : AdelicGL2 (𝓞 F) F → ℂ) = locAct F v g (locAct F v g' φ)
    exact locAct_mul F v g g' _

private theorem subRep_apply_coe (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hW : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ φ ∈ W, locAct F v g φ ∈ W)
    (g : GL (Fin 2) (v.adicCompletion F)) (φ : ↥W) :
    ((subRep v W hW g φ : ↥W) : AdelicGL2 (𝓞 F) F → ℂ) = locAct F v g φ :=
  rfl

private theorem locAct_mem_of_isCuspSubrep (hV : IsCuspSubrep F pins ξ V) (g : GL (Fin 2) (v.adicCompletion F)) :
    ∀ φ ∈ V, locAct F v g φ ∈ V := fun _ hφ =>
  finAct_mem F hV _ hφ

variable (v) in

private def locRep (hV : IsCuspSubrep F pins ξ V) : Representation ℂ (GL (Fin 2) (v.adicCompletion F)) ↥V :=
  subRep v V (locAct_mem_of_isCuspSubrep hV)

private theorem locRep_apply_coe (hV : IsCuspSubrep F pins ξ V) (g : GL (Fin 2) (v.adicCompletion F)) (φ : ↥V) :
    ((locRep v hV g φ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) = locAct F v g φ :=
  rfl

end Local

section Averaging

private structure AveragingOps {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W)
    (L : Subgroup G) where

  average : W →ₗ[ℂ] W
  exists_finite : ∀ w : W, ∃ S : Subgroup L, Finite (L ⧸ S) ∧ ∀ s ∈ S, π ((s : L) : G) w = w
  average_eq : ∀ (S : Subgroup L) (w : W), Finite (L ⧸ S) → (∀ s ∈ S, π ((s : L) : G) w = w) →
    average w = (Nat.card (L ⧸ S) : ℂ)⁻¹ • ∑ᶠ q : L ⧸ S, π ((q.out : L) : G) w
  apply_average : ∀ (w : W), ∀ l ∈ L, π l (average w) = average w
  average_eq_self : ∀ w : W, (∀ l ∈ L, π l w = w) → average w = w
  average_mem_span : ∀ w : W, average w ∈ Submodule.span ℂ (Set.range fun l : L => π (l : G) w)

end Averaging

section Component

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}

variable (F v V) in

private structure CutAt where
  U₀ : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
  L : Subgroup (GL (Fin 2) (v.adicCompletion F))
  tys : ArchTypeFamily F
  φ₀ : AdelicGL2 (𝓞 F) F → ℂ
  φ₀_mem : φ₀ ∈ V
  φ₀_ne : φ₀ ≠ 0
  finAct_φ₀ : ∀ k ∈ U₀, finAct F k φ₀ = φ₀
  localEmbed_mem : ∀ l ∈ L, localEmbed (𝓞 F) F v l ∈ U₀
  φ₀_mem_arch : φ₀ ∈ archCutSubmodule F tys
  isOpen_U₀ : IsOpen (U₀ : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
  isCompact_L : IsCompact (L : Set (GL (Fin 2) (v.adicCompletion F)))
  isOpen_L : IsOpen (L : Set (GL (Fin 2) (v.adicCompletion F)))

private def cutSub (c : CutAt F v V) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  V ⊓ locFixed F v c.L ⊓ awayFixed F v c.U₀ ⊓ archCutSubmodule F c.tys

private theorem mem_cutSub_iff (c : CutAt F v V) {φ : AdelicGL2 (𝓞 F) F → ℂ} :
    φ ∈ cutSub c ↔ φ ∈ V ∧ (∀ l ∈ c.L, locAct F v l φ = φ) ∧
      (∀ h ∈ c.U₀, finComponent (𝓞 F) F v h = 1 → finAct F h φ = φ) ∧ φ ∈ archCutSubmodule F c.tys :=
  ⟨fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩⟩

private theorem cutSub_le (c : CutAt F v V) : cutSub c ≤ V := fun _ hφ => ((mem_cutSub_iff c).mp hφ).1

private theorem φ₀_mem_cutSub (c : CutAt F v V) : c.φ₀ ∈ cutSub c :=
  (mem_cutSub_iff c).mpr ⟨c.φ₀_mem, fun l hl => c.finAct_φ₀ _ (c.localEmbed_mem l hl),
    fun h hU _ => c.finAct_φ₀ h hU, c.φ₀_mem_arch⟩

private theorem cutSub_ne_bot (c : CutAt F v V) : cutSub c ≠ ⊥ := fun h =>
  c.φ₀_ne ((Submodule.mem_bot ℂ).mp (h ▸ φ₀_mem_cutSub c))

private def cutGroup (c : CutAt F v V) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  c.L.comap (finComponent (𝓞 F) F v) ⊓ c.U₀.comap (awayHom F v)

private theorem isOpen_cutGroup (c : CutAt F v V) (hι : Continuous (localEmbed (𝓞 F) F v)) :
    IsOpen (cutGroup c : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
  (c.isOpen_L.preimage (continuous_finComponent (R := 𝓞 F) (K := F) v)).inter
    (c.isOpen_U₀.preimage (continuous_awayHom F v hι))

private theorem finAct_eq_of_mem_cutGroup (c : CutAt F v V) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cutSub c)
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ cutGroup c) : finAct F k φ = φ := by
  obtain ⟨hkL, hkU⟩ := Subgroup.mem_inf.mp hk
  obtain ⟨-, hL, hU, -⟩ := (mem_cutSub_iff c).mp hφ
  have hkU' : awayPart v k ∈ c.U₀ := Subgroup.mem_comap.mp hkU
  rw [finAct_eq_awayPart_locAct F v k, hL _ (Subgroup.mem_comap.mp hkL), hU _ hkU' (finComponent_awayPart v k)]

private theorem coe_average_mem (hV : IsCuspSubrep F pins ξ V) {L : Subgroup (GL (Fin 2) (v.adicCompletion F))}
    (ops : AveragingOps (locRep v hV) L) {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hY : ∀ l ∈ L, ∀ y ∈ Y, locAct F v l y ∈ Y) (w : ↥V) (hw : (w : AdelicGL2 (𝓞 F) F → ℂ) ∈ Y) :
    ((ops.average w : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) ∈ Y := by
  have h := Submodule.mem_map_of_mem (f := V.subtype) (ops.average_mem_span w)
  rw [Submodule.map_span] at h
  refine (Submodule.span_le.mpr ?_) h
  rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
  exact hY _ l.2 _ hw

private theorem locAct_coe_average (hV : IsCuspSubrep F pins ξ V) {L : Subgroup (GL (Fin 2) (v.adicCompletion F))}
    (ops : AveragingOps (locRep v hV) L) (w : ↥V) {l : GL (Fin 2) (v.adicCompletion F)} (hl : l ∈ L) :
    locAct F v l ((ops.average w : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) = ops.average w :=
  congrArg Subtype.val (ops.apply_average w l hl)

private theorem average_eq_self_of_mem (c : CutAt F v V) (hV : IsCuspSubrep F pins ξ V)
    (ops : AveragingOps (locRep v hV) c.L)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cutSub c) :
    ops.average ⟨φ, cutSub_le c hφ⟩ = ⟨φ, cutSub_le c hφ⟩ :=
  ops.average_eq_self _ fun l hl => Subtype.ext (((mem_cutSub_iff c).mp hφ).2.1 l hl)

private def IsHeckeStable (hV : IsCuspSubrep F pins ξ V) {L : Subgroup (GL (Fin 2) (v.adicCompletion F))}
    (ops : AveragingOps (locRep v hV) L) (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Prop :=
  ∀ (g : GL (Fin 2) (v.adicCompletion F)) (φ : AdelicGL2 (𝓞 F) F → ℂ), φ ∈ M →
    ∀ (hgφ : locAct F v g φ ∈ V), ((ops.average ⟨locAct F v g φ, hgφ⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) ∈ M

private theorem isHeckeStable_cutSub (c : CutAt F v V) (hV : IsCuspSubrep F pins ξ V)
    (ops : AveragingOps (locRep v hV) c.L)
    (harchcut : ∀ (tys : ArchTypeFamily F) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ),
      φ ∈ archCutSubmodule F tys → finAct F k φ ∈ archCutSubmodule F tys) :
    IsHeckeStable hV ops (cutSub c) := by
  intro g φ hφ hgφ
  obtain ⟨-, -, hU, hA⟩ := (mem_cutSub_iff c).mp hφ
  have hY : ∀ l ∈ c.L, ∀ y ∈ awayFixed F v c.U₀ ⊓ archCutSubmodule F c.tys,
      locAct F v l y ∈ awayFixed F v c.U₀ ⊓ archCutSubmodule F c.tys := fun l _ y hy =>
    ⟨locAct_mem_awayFixed l hy.1, harchcut _ _ _ hy.2⟩
  have hmem := coe_average_mem hV ops hY ⟨locAct F v g φ, hgφ⟩ ⟨locAct_mem_awayFixed g hU, harchcut _ _ _ hA⟩
  exact (mem_cutSub_iff c).mpr ⟨(ops.average _).2, fun l hl => locAct_coe_average hV ops _ hl, hmem.1, hmem.2⟩

private theorem exists_minimal_isHeckeStable (c : CutAt F v V) (hV : IsCuspSubrep F pins ξ V)
    (ops : AveragingOps (locRep v hV) c.L) [FiniteDimensional ℂ ↥(cutSub c)] (hE : IsHeckeStable hV ops (cutSub c)) :
    ∃ M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), M ≤ cutSub c ∧ M ≠ ⊥ ∧ IsHeckeStable hV ops M ∧
      ∀ M' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), M' ≤ M → M' ≠ ⊥ → IsHeckeStable hV ops M' → M' = M := by
  classical
  have hP : ∃ n : ℕ, ∃ M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      M ≤ cutSub c ∧ M ≠ ⊥ ∧ IsHeckeStable hV ops M ∧ Module.finrank ℂ ↥M = n :=
    ⟨_, cutSub c, le_rfl, cutSub_ne_bot c, hE, rfl⟩
  obtain ⟨M, hME, hM0, hMs, hMn⟩ := Nat.find_spec hP
  refine ⟨M, hME, hM0, hMs, fun M' hM'M hM'0 hM's => ?_⟩
  haveI : FiniteDimensional ℂ ↥M := Submodule.finiteDimensional_of_le hME
  refine Submodule.eq_of_le_of_finrank_eq hM'M (le_antisymm (Submodule.finrank_mono hM'M) ?_)
  rw [hMn]
  exact Nat.find_min' hP ⟨M', hM'M.trans hME, hM'0, hM's, rfl⟩

variable (v) in

private def locSpan (Ev : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ {x | ∃ (g : GL (Fin 2) (v.adicCompletion F)) (e : AdelicGL2 (𝓞 F) F → ℂ),
    e ∈ Ev ∧ x = locAct F v g e}

private theorem le_locSpan (Ev : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Ev ≤ locSpan v Ev := fun e he =>
  Submodule.subset_span ⟨1, e, he, (locAct_one F v e).symm⟩

private theorem locAct_mem_locSpan (Ev : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (g : GL (Fin 2) (v.adicCompletion F))
    {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : x ∈ locSpan v Ev) : locAct F v g x ∈ locSpan v Ev := by
  have h := Submodule.mem_map_of_mem (f := locAct F v g) hx
  rw [locSpan, Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨g', e, he, rfl⟩, rfl⟩
  exact ⟨g * g', e, he, (locAct_mul F v g g' e).symm⟩

private theorem locSpan_le_of_le (Ev : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y) (hEY : Ev ≤ Y) :
    locSpan v Ev ≤ Y := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, e, he, rfl⟩
  exact hY g e (hEY he)

private theorem locSpan_le_V (c : CutAt F v V) (hV : IsCuspSubrep F pins ξ V)
    {Ev : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hEvE : Ev ≤ cutSub c) : locSpan v Ev ≤ V :=
  locSpan_le_of_le Ev (locAct_mem_of_isCuspSubrep hV) (hEvE.trans (cutSub_le c))

private theorem locSpan_le_awayFixed_inf (c : CutAt F v V) {Ev : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hEvE : Ev ≤ cutSub c)
    (harchcut : ∀ (tys : ArchTypeFamily F) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ),
      φ ∈ archCutSubmodule F tys → finAct F k φ ∈ archCutSubmodule F tys) :
    locSpan v Ev ≤ awayFixed F v c.U₀ ⊓ archCutSubmodule F c.tys :=
  locSpan_le_of_le Ev (fun g _ hy => ⟨locAct_mem_awayFixed g hy.1, harchcut _ _ _ hy.2⟩) fun _ he =>
    ⟨((mem_cutSub_iff c).mp (hEvE he)).2.2.1, ((mem_cutSub_iff c).mp (hEvE he)).2.2.2⟩

private theorem coe_average_mem_of_mem_locSpan (c : CutAt F v V) (hV : IsCuspSubrep F pins ξ V)
    (ops : AveragingOps (locRep v hV) c.L) {Ev : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hEvE : Ev ≤ cutSub c)
    (hEvs : IsHeckeStable hV ops Ev) {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : x ∈ locSpan v Ev) (hxV : x ∈ V) :
    ((ops.average ⟨x, hxV⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) ∈ Ev := by
  revert hxV
  refine Submodule.span_induction (p := fun x _ => ∀ hxV : x ∈ V,
    ((ops.average ⟨x, hxV⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) ∈ Ev) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨g, e, he, rfl⟩ hxV
    exact hEvs g e he hxV
  · intro h0
    have h : (⟨0, h0⟩ : ↥V) = 0 := rfl
    rw [h, map_zero]
    exact Ev.zero_mem
  · intro x y hx hy px py hxyV
    have hxV : x ∈ V := locSpan_le_V c hV hEvE hx
    have hyV : y ∈ V := locSpan_le_V c hV hEvE hy
    have h : (⟨x + y, hxyV⟩ : ↥V) = ⟨x, hxV⟩ + ⟨y, hyV⟩ := rfl
    rw [h, map_add, Submodule.coe_add]
    exact Ev.add_mem (px hxV) (py hyV)
  · intro a x hx px haxV
    have hxV : x ∈ V := locSpan_le_V c hV hEvE hx
    have h : (⟨a • x, haxV⟩ : ↥V) = a • ⟨x, hxV⟩ := rfl
    rw [h, map_smul, Submodule.coe_smul]
    exact Ev.smul_mem a (px hxV)

private theorem coe_average_apply_intertwiner (hV : IsCuspSubrep F pins ξ V)
    {L : Subgroup (GL (Fin 2) (v.adicCompletion F))} (ops : AveragingOps (locRep v hV) L)
    {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hYV : Y ≤ V)
    (hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y)
    {b : ↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)} (hb : IsLocIntertwiner F v V Y b) (y : ↥Y) :
    ((ops.average ⟨b y, hb.1 y⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) =
      b ⟨((ops.average ⟨y, hYV y.2⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ),
        coe_average_mem hV ops (fun l _ y hy => hY l y hy) ⟨y, hYV y.2⟩ y.2⟩ := by
  obtain ⟨S, hfin, hS⟩ := ops.exists_finite ⟨(y : AdelicGL2 (𝓞 F) F → ℂ), hYV y.2⟩
  haveI := hfin
  haveI : Fintype (↥L ⧸ S) := Fintype.ofFinite _
  have hmemY : ∀ q : ↥L ⧸ S,
      locAct F v ((q.out : ↥L) : GL (Fin 2) (v.adicCompletion F)) (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ Y :=
    fun q => hY _ _ y.2
  have hSb : ∀ s ∈ S,
      locRep v hV ((s : ↥L) : GL (Fin 2) (v.adicCompletion F)) ⟨b y, hb.1 y⟩ = ⟨b y, hb.1 y⟩ := by
    intro s hs
    apply Subtype.ext
    show locAct F v ((s : ↥L) : GL (Fin 2) (v.adicCompletion F)) (b y) = b y
    have hy : locAct F v ((s : ↥L) : GL (Fin 2) (v.adicCompletion F)) (y : AdelicGL2 (𝓞 F) F → ℂ) = y :=
      congrArg Subtype.val (hS s hs)
    rw [← hb.2 ((s : ↥L) : GL (Fin 2) (v.adicCompletion F)) y (hY _ _ y.2)]
    congr 1
    exact Subtype.ext hy
  have key : (⟨((ops.average ⟨y, hYV y.2⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ),
      coe_average_mem hV ops (fun l _ y hy => hY l y hy) ⟨y, hYV y.2⟩ y.2⟩ : ↥Y) =
      (Nat.card (↥L ⧸ S) : ℂ)⁻¹ • ∑ q : ↥L ⧸ S,
        (⟨locAct F v ((q.out : ↥L) : GL (Fin 2) (v.adicCompletion F)) (y : AdelicGL2 (𝓞 F) F → ℂ), hmemY q⟩ :
          ↥Y) := by
    apply Subtype.ext
    rw [Submodule.coe_mk, ops.average_eq S _ hfin hS]
    simp only [finsum_eq_sum_of_fintype, Submodule.coe_smul, Submodule.coe_sum, locRep_apply_coe]
  rw [key, map_smul, map_sum, ops.average_eq S _ hfin hSb]
  simp only [finsum_eq_sum_of_fintype, Submodule.coe_smul, Submodule.coe_sum, locRep_apply_coe]
  congr 1
  exact Finset.sum_congr rfl fun q _ => (hb.2 _ y (hmemY q)).symm

private theorem locSpan_le_of_average_ne_zero (c : CutAt F v V) (hV : IsCuspSubrep F pins ξ V)
    (ops : AveragingOps (locRep v hV) c.L) {Ev : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hEvE : Ev ≤ cutSub c)
    (hEvs : IsHeckeStable hV ops Ev)
    (hmin : ∀ M' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), M' ≤ Ev → M' ≠ ⊥ → IsHeckeStable hV ops M' → M' = Ev)
    {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hYX : Y ≤ locSpan v Ev)
    (hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : y ∈ Y) (hyV : y ∈ V)
    (hne : ((ops.average ⟨y, hyV⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) ≠ 0) : locSpan v Ev ≤ Y := by
  have hM : Ev ⊓ Y = Ev := by
    refine hmin (Ev ⊓ Y) inf_le_left ?_ fun g φ hφ hgφ => ?_
    · intro h
      apply hne
      have hm : ((ops.average ⟨y, hyV⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) ∈ Ev ⊓ Y :=
        ⟨coe_average_mem_of_mem_locSpan c hV ops hEvE hEvs (hYX hy) hyV,
          coe_average_mem hV ops (fun l _ y hy => hY l y hy) ⟨y, hyV⟩ hy⟩
      rw [h] at hm
      exact (Submodule.mem_bot ℂ).mp hm
    · exact ⟨hEvs g φ hφ.1 hgφ, coe_average_mem hV ops (fun l _ y hy => hY l y hy) ⟨_, hgφ⟩ (hY g φ hφ.2)⟩
  exact locSpan_le_of_le Ev hY (hM ▸ inf_le_right)

private theorem false_of_average_eq_zero (c : CutAt F v V) (hV : IsCuspConstituent F pins ξ V)
    (ops : AveragingOps (locRep v hV.1) c.L) {Ev : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hEvE : Ev ≤ cutSub c)
    (hexp : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
      IsFactorizableTestFn F f → IsArchBiFinite F tys f → HasFiniteExpansion F V f)
    (harch : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
      (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)),
      rowIsometryInclAt₀ F w k * finEmbed (𝓞 F) F x = finEmbed (𝓞 F) F x * rowIsometryInclAt₀ F w k)
    {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hYX : Y ≤ locSpan v Ev)
    (hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y) (hY0 : Y ≠ ⊥)
    (hzero : ∀ y ∈ Y, ∀ hyV : y ∈ V, ((ops.average ⟨y, hyV⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) = 0) : False := by
  have hYV : Y ≤ V := hYX.trans (locSpan_le_V c hV.1 hEvE)
  obtain ⟨n, y, b, hb, hsum⟩ := exists_eq_sum_of_mem hV hexp harch hYV hY hY0 c.φ₀_mem
  apply c.φ₀_ne
  have h₀ : (⟨c.φ₀, c.φ₀_mem⟩ : ↥V) = ∑ i, ⟨b i (y i), (hb i).1 (y i)⟩ :=
    Subtype.ext (by rw [Submodule.coe_sum]; exact hsum)
  have havg : ops.average ⟨c.φ₀, c.φ₀_mem⟩ = ⟨c.φ₀, c.φ₀_mem⟩ := average_eq_self_of_mem c hV.1 ops (φ₀_mem_cutSub c)
  have hφ₀ : c.φ₀ = ((ops.average ⟨c.φ₀, c.φ₀_mem⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) := by rw [havg]
  rw [hφ₀, h₀, map_sum, Submodule.coe_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coe_average_apply_intertwiner hV.1 ops hYV hY (hb i) (y i)]
  have hz : (⟨((ops.average ⟨y i, hYV (y i).2⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ),
      coe_average_mem hV.1 ops (fun l _ y hy => hY l y hy) ⟨y i, hYV (y i).2⟩ (y i).2⟩ : ↥Y) = 0 :=
    Subtype.ext (hzero _ (y i).2 _)
  rw [hz, map_zero]

end Component

section Main

variable {F : Type} [Field F] [NumberField F]
variable {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}

private def fixedSubmodule (v : HeightOneSpectrum (𝓞 F)) (X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hX : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ x ∈ X, locAct F v g x ∈ X)
    (U : Subgroup (GL (Fin 2) (v.adicCompletion F))) : Submodule ℂ ↥X where
  carrier := {x | ∀ u ∈ U, subRep v X hX u x = x}
  zero_mem' := fun u _ => map_zero _
  add_mem' := fun {a b} ha hb u hu => by rw [map_add, ha u hu, hb u hu]
  smul_mem' := fun c {a} ha u hu => by rw [map_smul, ha u hu]

private theorem exists_localComponent (hV : IsCuspConstituent F pins ξ V) (v : HeightOneSpectrum (𝓞 F))
    (hι : Continuous (localEmbed (𝓞 F) F v))
    (hC : ∃ C : Subgroup (GL (Fin 2) (v.adicCompletion F)),
      IsCompact (C : Set (GL (Fin 2) (v.adicCompletion F))) ∧ IsOpen (C : Set (GL (Fin 2) (v.adicCompletion F))))
    (hstab : ∀ φ ∈ V, IsOpen (finFixing F φ : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))))
    (hdir : ∀ φ ∈ V, ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys)
    (harchcut : ∀ (tys : ArchTypeFamily F) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ),
      φ ∈ archCutSubmodule F tys → finAct F k φ ∈ archCutSubmodule F tys)
    (harch : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
      (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)),
      rowIsometryInclAt₀ F w k * finEmbed (𝓞 F) F x = finEmbed (𝓞 F) F x * rowIsometryInclAt₀ F w k)
    (hexp : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
      IsFactorizableTestFn F f → IsArchBiFinite F tys f → HasFiniteExpansion F V f)
    (hfd : ∀ (K : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))),
      IsOpen (K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) →
      ∀ (tys : ArchTypeFamily F) (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), W ≤ V →
        (∀ φ ∈ W, ∀ k ∈ K, rightTranslate F (finEmbed (𝓞 F) F k) φ = φ) →
          W ≤ archCutSubmodule F tys → FiniteDimensional ℂ ↥W)
    (havg : ∀ (L : Subgroup (GL (Fin 2) (v.adicCompletion F))),
      IsCompact (L : Set (GL (Fin 2) (v.adicCompletion F))) → IsOpen (L : Set (GL (Fin 2) (v.adicCompletion F))) →
        AveragingOps (locRep v hV.1) L) :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (π : Representation ℂ (GL (Fin 2) (v.adicCompletion F)) X),
      (∀ x : X, ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion F)),
          IsOpen (U : Set (GL (Fin 2) (v.adicCompletion F))) ∧ ∀ u ∈ U, π u x = x) ∧
      (∃ x : X, x ≠ 0) ∧
      (∀ T : Submodule ℂ X, (∀ (g : GL (Fin 2) (v.adicCompletion F)) (x : X), x ∈ T → π g x ∈ T) →
          T = ⊥ ∨ T = ⊤) ∧
      (∀ U : Subgroup (GL (Fin 2) (v.adicCompletion F)),
          IsOpen (U : Set (GL (Fin 2) (v.adicCompletion F))) →
          ∃ T : Submodule ℂ X, FiniteDimensional ℂ T ∧
            ∀ x : X, (∀ u ∈ U, π u x = x) → x ∈ T) ∧
      ∀ φ ∈ V, ∃ (n : ℕ) (x : Fin n → X) (f : Fin n → (X →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))),
          (∀ i : Fin n, (∀ y : X, f i y ∈ V) ∧
            ∀ (g : GL (Fin 2) (v.adicCompletion F)) (y : X),
              f i (π g y) = rightTranslate F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v g)) (f i y)) ∧
          φ = ∑ i : Fin n, f i (x i) := by

  obtain ⟨φ₀, hφ₀V, hφ₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.2.1
  obtain ⟨C, hCc, hCo⟩ := hC
  obtain ⟨tys, htys⟩ := hdir φ₀ hφ₀V
  have hUo : IsOpen (finFixing F φ₀ : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := hstab φ₀ hφ₀V
  let L : Subgroup (GL (Fin 2) (v.adicCompletion F)) := (finFixing F φ₀).comap (localEmbed (𝓞 F) F v) ⊓ C
  have hLo : IsOpen (L : Set (GL (Fin 2) (v.adicCompletion F))) := (hUo.preimage hι).inter hCo
  have hLc : IsCompact (L : Set (GL (Fin 2) (v.adicCompletion F))) :=
    hCc.of_isClosed_subset ((((finFixing F φ₀).comap (localEmbed (𝓞 F) F v)).isClosed_of_isOpen
      (hUo.preimage hι)).inter (C.isClosed_of_isOpen hCo)) Set.inter_subset_right
  let c : CutAt F v V := ⟨finFixing F φ₀, L, tys, φ₀, hφ₀V, hφ₀, fun k hk => hk,
    fun l hl => (Subgroup.mem_inf.mp hl).1, htys, hUo, hLc, hLo⟩
  let ops : AveragingOps (locRep v hV.1) c.L := havg c.L c.isCompact_L c.isOpen_L
  haveI : FiniteDimensional ℂ ↥(cutSub c) :=
    hfd (cutGroup c) (isOpen_cutGroup c hι) c.tys (cutSub c) (cutSub_le c)
      (fun φ hφ k hk => finAct_eq_of_mem_cutGroup c hφ hk) fun φ hφ => ((mem_cutSub_iff c).mp hφ).2.2.2

  obtain ⟨Ev, hEvE, hEv0, hEvs, hmin⟩ :=
    exists_minimal_isHeckeStable c hV.1 ops (isHeckeStable_cutSub c hV.1 ops harchcut)
  let X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := locSpan v Ev
  have hX : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ x ∈ X, locAct F v g x ∈ X :=
    fun g x hx => locAct_mem_locSpan Ev g hx
  have hXV : X ≤ V := locSpan_le_V c hV.1 hEvE
  have hXaway : X ≤ awayFixed F v c.U₀ ⊓ archCutSubmodule F c.tys :=
    locSpan_le_awayFixed_inf c hEvE harchcut
  refine ⟨↥X, inferInstance, inferInstance, subRep v X hX, ?_, ?_, ?_, ?_, ?_⟩

  · intro x
    refine ⟨(finFixing F (x : AdelicGL2 (𝓞 F) F → ℂ)).comap (localEmbed (𝓞 F) F v),
      (hstab _ (hXV x.2)).preimage hι, fun u hu => Subtype.ext ?_⟩
    exact Subgroup.mem_comap.mp hu

  · obtain ⟨e, heE, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hEv0
    exact ⟨⟨e, le_locSpan Ev heE⟩, fun h => hne (congrArg Subtype.val h)⟩

  · intro T hT
    let Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := T.map X.subtype
    have hYX : Y ≤ X := Submodule.map_subtype_le X T
    have hY : ∀ (g : GL (Fin 2) (v.adicCompletion F)), ∀ y ∈ Y, locAct F v g y ∈ Y :=
      fun g _ ⟨x, hxT, hx⟩ => ⟨subRep v X hX g x, hT g x hxT, hx ▸ rfl⟩
    by_cases h : ∃ y ∈ Y, ∃ hyV : y ∈ V, ((ops.average ⟨y, hyV⟩ : ↥V) : AdelicGL2 (𝓞 F) F → ℂ) ≠ 0
    · right
      obtain ⟨y, hyY, hyV, hne⟩ := h
      have hXY : X ≤ Y := locSpan_le_of_average_ne_zero c hV.1 ops hEvE hEvs hmin hYX hY hyY hyV hne
      refine eq_top_iff.mpr fun x _ => ?_
      obtain ⟨x', hx'T, hx'⟩ := hXY x.2
      rwa [← Subtype.ext hx']
    · left
      by_contra hT0
      refine false_of_average_eq_zero c hV ops hEvE hexp harch hYX hY ?_ fun y hyY hyV => ?_
      · intro hY0
        apply hT0
        refine eq_bot_iff.mpr fun x hxT => (Submodule.mem_bot ℂ).mpr (Subtype.ext ?_)
        have hx : (x : AdelicGL2 (𝓞 F) F → ℂ) ∈ Y := ⟨x, hxT, rfl⟩
        rw [hY0] at hx
        exact (Submodule.mem_bot ℂ).mp hx
      · by_contra hne
        exact h ⟨y, hyY, hyV, hne⟩

  · intro U hU
    refine ⟨fixedSubmodule v X hX U, ?_, fun x hx => hx⟩
    let W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (fixedSubmodule v X hX U).map X.subtype
    have hWX : W ≤ X := Submodule.map_subtype_le X _
    have hK : IsOpen ((U.comap (finComponent (𝓞 F) F v) ⊓ c.U₀.comap (awayHom F v) :
        Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
      (hU.preimage (continuous_finComponent (R := 𝓞 F) (K := F) v)).inter
        (c.isOpen_U₀.preimage (continuous_awayHom F v hι))
    haveI : FiniteDimensional ℂ ↥W := by
      refine hfd _ hK c.tys W (hWX.trans hXV) ?_ fun φ hφ => (hXaway (hWX hφ)).2
      rintro _ ⟨x, hxU, rfl⟩ k hk
      obtain ⟨hkU, hkU₀⟩ := Subgroup.mem_inf.mp hk
      have h₁ : locAct F v (finComponent (𝓞 F) F v k) (x : AdelicGL2 (𝓞 F) F → ℂ) = x :=
        congrArg Subtype.val (hxU _ (Subgroup.mem_comap.mp hkU))
      have hk₀ : awayPart v k ∈ c.U₀ := Subgroup.mem_comap.mp hkU₀
      have h₂ := (hXaway x.2).1 _ hk₀ (finComponent_awayPart v k)
      show finAct F k (x : AdelicGL2 (𝓞 F) F → ℂ) = x
      rw [finAct_eq_awayPart_locAct F v k, h₁]
      exact h₂
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective X.subtype X.injective_subtype (fixedSubmodule v X hX U)).symm

  · intro φ hφ
    obtain ⟨n, y, b, hb, hsum⟩ := exists_eq_sum_of_mem hV hexp harch hXV hX
      (fun h => hEv0 (eq_bot_iff.mpr (h ▸ le_locSpan Ev))) hφ
    exact ⟨n, y, b, fun i => ⟨(hb i).1, fun g y => (hb i).2 g y (hX g _ y.2)⟩, hsum⟩

end Main

end Spine

section Embeddings

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

private def integralStructureMap
    (z : Π w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), w.adicCompletionIntegers ℚ) :
    IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ :=
  RestrictedProduct.structureMap
    (fun w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) => w.adicCompletion ℚ)
    (fun w => (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) Filter.cofinite z

private theorem continuous_integralStructureMap : Continuous integralStructureMap :=
  (RestrictedProduct.isEmbedding_structureMap).continuous

private def insertAt (t : v.adicCompletion ℚ) : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ :=
  AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v 0 t

private theorem insertAt_apply_self (t : v.adicCompletion ℚ) : insertAt v t v = t :=
  AdelicDock.splice_apply_self (NumberField.RingOfIntegers ℚ) ℚ v 0 t

private theorem insertAt_apply_of_ne (t : v.adicCompletion ℚ)
    {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)} (hw : w ≠ v) : insertAt v t w = 0 :=
  AdelicDock.splice_apply_of_ne (NumberField.RingOfIntegers ℚ) ℚ v 0 t hw

private theorem insertAt_zero : insertAt v 0 = 0 :=
  RestrictedProduct.ext _ _ fun w => by
    by_cases hw : w = v
    · subst hw; exact insertAt_apply_self w 0
    · exact insertAt_apply_of_ne v 0 hw

private theorem insertAt_add (s t : v.adicCompletion ℚ) : insertAt v (s + t) = insertAt v s + insertAt v t :=
  RestrictedProduct.ext _ _ fun w => by
    by_cases hw : w = v
    · subst hw
      show insertAt w (s + t) w = insertAt w s w + insertAt w t w
      rw [insertAt_apply_self, insertAt_apply_self, insertAt_apply_self]
    · show insertAt v (s + t) w = insertAt v s w + insertAt v t w
      rw [insertAt_apply_of_ne v _ hw, insertAt_apply_of_ne v _ hw, insertAt_apply_of_ne v _ hw, add_zero]

private def insertAtHom : v.adicCompletion ℚ →+ IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ where
  toFun := insertAt v
  map_zero' := insertAt_zero v
  map_add' := insertAt_add v

open scoped Classical in

private theorem insertAt_eq_integralStructureMap (x : v.adicCompletionIntegers ℚ) :
    insertAt v (x : v.adicCompletion ℚ) =
      integralStructureMap (Function.update
        (0 : Π w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), w.adicCompletionIntegers ℚ)
        v x) :=
  RestrictedProduct.ext _ _ fun w => by
    show insertAt v (x : v.adicCompletion ℚ) w =
      ((Function.update
        (0 : Π w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), w.adicCompletionIntegers ℚ)
        v x w : w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ)
    by_cases hw : w = v
    · subst hw; simp [insertAt_apply_self]
    · simp [insertAt_apply_of_ne v _ hw, Function.update_of_ne hw]

open scoped Classical in
private theorem continuousOn_insertAt :
    ContinuousOn (insertAt v) (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hres : (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).domRestrict (insertAt v) =
      fun x => integralStructureMap (Function.update
        (0 : Π w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), w.adicCompletionIntegers ℚ) v
        ⟨x.1, x.2⟩) :=
    funext fun x => insertAt_eq_integralStructureMap v ⟨x.1, x.2⟩
  rw [hres]
  exact continuous_integralStructureMap.comp
    (continuous_const.update v
      (Continuous.subtype_mk (p := fun a => a ∈ v.adicCompletionIntegers ℚ) continuous_subtype_val fun x => x.2))

private theorem continuous_insertAt : Continuous (insertAt v) := by
  have hopen : IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    Valued.isOpen_valuationSubring _
  have h0 : ContinuousAt (insertAt v) 0 :=
    (continuousOn_insertAt v).continuousAt (hopen.mem_nhds (SetLike.mem_coe.mpr (zero_mem _)))
  exact continuous_of_continuousAt_zero (insertAtHom v) h0

private theorem continuous_splice (a : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :
    Continuous (AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v a) := by
  have h : AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v a = fun t => a + insertAt v (t - a v) :=
    funext fun t => RestrictedProduct.ext _ _ fun w => by
      by_cases hw : w = v
      · subst hw
        show AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ w a t w = a w + insertAt w (t - a w) w
        rw [AdelicDock.splice_apply_self, insertAt_apply_self, add_sub_cancel]
      · show AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v a t w = a w + insertAt v (t - a v) w
        rw [AdelicDock.splice_apply_of_ne (NumberField.RingOfIntegers ℚ) ℚ v a t hw, insertAt_apply_of_ne v _ hw,
          add_zero]
  rw [h]
  exact continuous_const.add ((continuous_insertAt v).comp (continuous_id.sub continuous_const))

private theorem continuous_localMat :
    Continuous fun g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) =>
      AdelicDock.localMat (NumberField.RingOfIntegers ℚ) ℚ v g :=
  continuous_matrix fun i j => (continuous_splice v _).comp (continuous_id.matrix_elem i j)

private theorem continuous_localEmbed : Continuous (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v) :=
  Units.continuous_iff.mpr ⟨(continuous_localMat v).comp Units.continuous_val,
    (continuous_localMat v).comp Units.continuous_coe_inv⟩

private theorem continuous_finMat :
    Continuous fun g : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) =>
      AdelicDock.finMat (NumberField.RingOfIntegers ℚ) ℚ g :=
  continuous_matrix fun i j => continuous_const.prodMk (continuous_id.matrix_elem i j)

private theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ) :=
  Units.continuous_iff.mpr
    ⟨continuous_finMat.comp Units.continuous_val, continuous_finMat.comp Units.continuous_coe_inv⟩

end Embeddings

section Stabilizers

private def toFiniteAdelicSubgroup :
    GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) →* finiteAdelicGL2Subgroup ℚ :=
  (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ).codRestrict (finiteAdelicGL2Subgroup ℚ) fun k =>
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (NumberField.RingOfIntegers ℚ) ℚ k)

private theorem continuous_toFiniteAdelicSubgroup : Continuous toFiniteAdelicSubgroup :=
  Continuous.subtype_mk continuous_finEmbed fun k =>
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (NumberField.RingOfIntegers ℚ) ℚ k)

private def finiteFixing (φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    Subgroup (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :=
  (MulAction.stabilizer (finiteAdelicGL2Subgroup ℚ)
    (FLT.SmoothVectors.RightTranslationFn.mk φ :
      FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) ℂ)).comap
    toFiniteAdelicSubgroup

private theorem mem_finiteFixing_iff (φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    k ∈ finiteFixing φ ↔ rightTranslate ℚ (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k) φ = φ := by
  rw [finiteFixing, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  exact Iff.rfl

private theorem isOpen_finiteFixing_of_isKfSmooth {φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}
    (hφ : IsKfSmooth ℚ φ) :
    IsOpen (finiteFixing φ :
      Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))) := by
  have h : IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup ℚ)
      (FLT.SmoothVectors.RightTranslationFn.mk φ :
        FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) ℂ) :
          Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) := hφ
  rw [finiteFixing, Subgroup.coe_comap]
  exact h.preimage continuous_toFiniteAdelicSubgroup

private theorem rightTranslate_one (φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    rightTranslate ℚ 1 φ = φ :=
  funext fun x => by rw [rightTranslate_apply, mul_one]

private theorem finiteFixing_zero : finiteFixing (0 : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) = ⊤ :=
  Subgroup.ext fun k => by simp [mem_finiteFixing_iff, rightTranslate_zero]

private theorem inf_le_finiteFixing_add (φ ψ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    finiteFixing φ ⊓ finiteFixing ψ ≤ finiteFixing (φ + ψ) := fun k hk => by
  obtain ⟨hkφ, hkψ⟩ := Subgroup.mem_inf.mp hk
  rw [mem_finiteFixing_iff] at hkφ hkψ ⊢
  rw [rightTranslate_add, hkφ, hkψ]

private theorem finiteFixing_le_finiteFixing_smul (c : ℂ) (φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    finiteFixing φ ≤ finiteFixing (c • φ) := fun k hk => by
  rw [mem_finiteFixing_iff] at hk ⊢
  rw [rightTranslate_smul, hk]

private theorem isOpen_finiteFixing_of_mem_cuspKFiniteSubmodule (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule ℚ pins ξ) :
    IsOpen (finiteFixing φ :
      Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))) := by
  refine Submodule.span_induction (p := fun φ _ => IsOpen (finiteFixing φ :
    Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)))) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, -, -⟩
    have h := (hsat 1).2
    rw [rightTranslate_one] at h
    exact isOpen_finiteFixing_of_isKfSmooth h
  · simp only [finiteFixing_zero, Subgroup.coe_top, isOpen_univ]
  · intro φ ψ _ _ hφ' hψ'
    refine Subgroup.isOpen_mono (inf_le_finiteFixing_add φ ψ) ?_
    rw [Subgroup.coe_inf]
    exact hφ'.inter hψ'
  · intro c φ _ hφ'
    exact Subgroup.isOpen_mono (finiteFixing_le_finiteFixing_smul c φ) hφ'

private theorem continuous_of_mem_cuspKFiniteSubmodule (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule ℚ pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hcont, -⟩
    exact hcont
  · exact continuous_zero
  · intro φ ψ _ _ hφ' hψ'
    exact hφ'.add hψ'
  · intro c φ _ hφ'
    exact hφ'.const_smul c

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

private def localFixing (φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    Subgroup (GL (Fin 2) (v.adicCompletion ℚ)) :=
  (finiteFixing φ).comap (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v)

private theorem mem_localFixing_iff (φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    g ∈ localFixing v φ ↔
      rightTranslate ℚ (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g)) φ = φ := by
  rw [localFixing, Subgroup.mem_comap, mem_finiteFixing_iff]

private theorem isOpen_localFixing_of_mem_cuspKFiniteSubmodule (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule ℚ pins ξ) :
    IsOpen (localFixing v φ : Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  rw [localFixing, Subgroup.coe_comap]
  exact (isOpen_finiteFixing_of_mem_cuspKFiniteSubmodule pins ξ hφ).preimage (continuous_localEmbed v)

end Stabilizers

section IntegralSubgroup

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

private theorem range_algebraMap_adicCompletionIntegers :
    Set.range (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) =
      (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact r.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem injective_algebraMap_adicCompletionIntegers :
    Function.Injective (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) :=
  fun _ _ hab => Subtype.ext hab

private theorem isOpen_integralSubgroup :
    IsOpen ((LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) :
      Set (GL (Fin 2) (v.adicCompletion ℚ)))) := by
  have hOopen : IsOpen (Set.range (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))) := by
    rw [range_algebraMap_adicCompletionIntegers]
    exact Valued.isOpen_valuationSubring _
  have hchar : (LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) :
        Set (GL (Fin 2) (v.adicCompletion ℚ)))
      = (⋂ i, ⋂ j, {g : GL (Fin 2) (v.adicCompletion ℚ) |
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
              ∈ Set.range (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))})
        ∩ (⋂ i, ⋂ j, {g : GL (Fin 2) (v.adicCompletion ℚ) |
            ((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
              ∈ Set.range (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))}) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem (injective_algebraMap_adicCompletionIntegers v) g
  rw [hchar]
  refine IsOpen.inter ?_ ?_
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hOopen.preimage (Units.continuous_val.matrix_elem i j)
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hOopen.preimage (Units.continuous_coe_inv.matrix_elem i j)

private theorem isCompact_integralSubgroup :
    IsCompact ((LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) :
      Set (GL (Fin 2) (v.adicCompletion ℚ)))) :=
  FLT.SpectralSide.isCompact_coe_integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
    continuous_subtype_val

private theorem exists_isCompact_isOpen_subgroup :
    ∃ C : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
      IsCompact (C : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧ IsOpen (C : Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
  ⟨LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ), isCompact_integralSubgroup v,
    isOpen_integralSubgroup v⟩

end IntegralSubgroup

section Translation

private theorem rightTranslate_finEmbed_mem_archCutSubmodule
    (hcomm : ∀ (a : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ))
      (h : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      adelicArchGLIncl ℚ a * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h =
        AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h * adelicArchGLIncl ℚ a)
    (tys : ArchTypeFamily ℚ) {φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : φ ∈ archCutSubmodule ℚ tys)
    (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    rightTranslate ℚ (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k) φ ∈ archCutSubmodule ℚ tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have key : ∀ i : Fin (tys.card w),
      (archTypeSubmoduleAt ℚ w (tys.rep w i)).map
          (rightRegular ℚ (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k))
        ≤ archTypeSubmoduleAt ℚ w (tys.rep w i) := by
    intro i f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
    refine comp_mul_mem_typeSubmodule_of_commute hf₀ _ fun k' => ?_
    rw [rowIsometryInclAt₀_apply]
    exact (hcomm (archGLIncl ℚ w (k' : GL (Fin 2) w.Completion)) k).symm
  have hmap : (⨆ i, archTypeSubmoduleAt ℚ w (tys.rep w i)).map
        (rightRegular ℚ (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k))
      ≤ ⨆ i, archTypeSubmoduleAt ℚ w (tys.rep w i) := by
    rw [Submodule.map_iSup]
    exact iSup_mono key
  exact hmap (Submodule.mem_map_of_mem (hφ w))

end Translation

section Directed

private def appendFamily (tys₁ tys₂ : ArchTypeFamily ℚ) : ArchTypeFamily ℚ where
  card w := tys₁.card w + tys₂.card w
  rep w := Fin.append (tys₁.rep w) (tys₂.rep w)

private theorem isContainedIn_appendFamily_left (tys₁ tys₂ : ArchTypeFamily ℚ) :
    tys₁.IsContainedIn ℚ (appendFamily tys₁ tys₂) :=
  fun w i => ⟨Fin.castAdd (tys₂.card w) i, Fin.append_left (tys₁.rep w) (tys₂.rep w) i⟩

private theorem isContainedIn_appendFamily_right (tys₁ tys₂ : ArchTypeFamily ℚ) :
    tys₂.IsContainedIn ℚ (appendFamily tys₁ tys₂) :=
  fun w i => ⟨Fin.natAdd (tys₁.card w) i, Fin.append_right (tys₁.rep w) (tys₂.rep w) i⟩

private def emptyFamily : ArchTypeFamily ℚ where
  card _ := 0
  rep _ i := i.elim0

private def archCutUnionSubmodule : Submodule ℂ (AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) where
  carrier := {φ | ∃ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys}
  zero_mem' := ⟨emptyFamily, (archCutSubmodule ℚ emptyFamily).zero_mem⟩
  add_mem' := by
    rintro φ ψ ⟨tys₁, hφ⟩ ⟨tys₂, hψ⟩
    exact ⟨appendFamily tys₁ tys₂,
      (archCutSubmodule ℚ _).add_mem (archCutSubmodule_mono ℚ (isContainedIn_appendFamily_left tys₁ tys₂) hφ)
        (archCutSubmodule_mono ℚ (isContainedIn_appendFamily_right tys₁ tys₂) hψ)⟩
  smul_mem' := by
    rintro c φ ⟨tys, hφ⟩
    exact ⟨tys, (archCutSubmodule ℚ tys).smul_mem c hφ⟩

private theorem exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule ℚ pins ξ) :
    ∃ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys := by
  have hle : cuspKFiniteSubmodule ℚ pins ξ ≤ archCutUnionSubmodule :=
    Submodule.span_le.mpr fun _ hψ => hψ.2.2
  exact hle hφ

end Directed

section CosetAverage

variable {K : Type*} [Group K] {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W)

private def cosetAverage (S : Subgroup K) (w : W) : W :=
  (Nat.card (K ⧸ S) : ℂ)⁻¹ • ∑ᶠ c : K ⧸ S, ρ c.out w

private theorem cosetAverage_eq_sum (S : Subgroup K) [Fintype (K ⧸ S)] (w : W) :
    cosetAverage ρ S w = (Nat.card (K ⧸ S) : ℂ)⁻¹ • ∑ c : K ⧸ S, ρ c.out w := by
  rw [cosetAverage, finsum_eq_sum_of_fintype]

private theorem natCard_quotient_ne_zero (S : Subgroup K) [Finite (K ⧸ S)] : (Nat.card (K ⧸ S) : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.card_pos (α := K ⧸ S)).ne'

private theorem rep_out_mk_apply {S : Subgroup K} {w : W} (hS : ∀ s ∈ S, ρ s w = w) (g : K) :
    ρ (QuotientGroup.mk g : K ⧸ S).out w = ρ g w := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S g
  rw [hh, map_mul, Module.End.mul_apply, hS h h.2]

private theorem cosetAverage_eq_of_le {S' S : Subgroup K} (hle : S' ≤ S) [Finite (K ⧸ S')] {w : W}
    (hS : ∀ s ∈ S, ρ s w = w) : cosetAverage ρ S' w = cosetAverage ρ S w := by
  let e := Subgroup.quotientEquivProdOfLE hle
  haveI : Finite ((K ⧸ S) × (S ⧸ S'.subgroupOf S)) := Finite.of_equiv _ e
  haveI : Finite (K ⧸ S) := Finite.of_surjective (Prod.fst : (K ⧸ S) × (S ⧸ S'.subgroupOf S) → K ⧸ S)
    Prod.fst_surjective
  haveI : Finite (S ⧸ S'.subgroupOf S) :=
    Finite.of_surjective (Prod.snd : (K ⧸ S) × (S ⧸ S'.subgroupOf S) → S ⧸ S'.subgroupOf S) Prod.snd_surjective
  letI : Fintype (K ⧸ S') := Fintype.ofFinite _
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  letI : Fintype (S ⧸ S'.subgroupOf S) := Fintype.ofFinite _
  have hS' : ∀ s ∈ S', ρ s w = w := fun s hs => hS s (hle hs)
  have hterm : ∀ c : K ⧸ S', ρ c.out w = ρ (e c).1.out w := by
    intro c
    refine QuotientGroup.induction_on c fun g => ?_
    have h1 : (e (QuotientGroup.mk g)).1 = (QuotientGroup.mk g : K ⧸ S) := rfl
    rw [h1, rep_out_mk_apply ρ hS', rep_out_mk_apply ρ hS]
  have hsum : ∑ c : K ⧸ S', ρ c.out w = ∑ p : (K ⧸ S) × (S ⧸ S'.subgroupOf S), ρ p.1.out w :=
    Fintype.sum_equiv e _ _ hterm
  have hcard : Nat.card (K ⧸ S') = Nat.card (K ⧸ S) * Nat.card (S ⧸ S'.subgroupOf S) := by
    rw [Nat.card_congr e, Nat.card_prod]
  have hscalar : (Nat.card (K ⧸ S') : ℂ)⁻¹ * (Nat.card (S ⧸ S'.subgroupOf S) : ℂ) = (Nat.card (K ⧸ S) : ℂ)⁻¹ := by
    rw [hcard, Nat.cast_mul, mul_inv, inv_mul_cancel_right₀ (natCard_quotient_ne_zero (S'.subgroupOf S))]
  rw [cosetAverage_eq_sum, cosetAverage_eq_sum, hsum, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [← Finset.smul_sum, smul_smul, hscalar]

private theorem cosetAverage_eq_self (S : Subgroup K) [Finite (K ⧸ S)] {w : W} (hw : ∀ k : K, ρ k w = w) :
    cosetAverage ρ S w = w := by
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  rw [cosetAverage_eq_sum]
  simp only [hw, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  rw [inv_mul_cancel₀ (natCard_quotient_ne_zero S), one_smul]

private theorem rep_cosetAverage {S : Subgroup K} [Finite (K ⧸ S)] {w : W} (hS : ∀ s ∈ S, ρ s w = w) (k : K) :
    ρ k (cosetAverage ρ S w) = cosetAverage ρ S w := by
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  rw [cosetAverage_eq_sum, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (MulAction.toPerm k) _ _ fun c => ?_
  refine QuotientGroup.induction_on c fun g => ?_
  show ρ k (ρ (QuotientGroup.mk g : K ⧸ S).out w) = ρ (QuotientGroup.mk (k * g) : K ⧸ S).out w
  rw [rep_out_mk_apply ρ hS, rep_out_mk_apply ρ hS, map_mul, Module.End.mul_apply]

private theorem cosetAverage_mem_span (S : Subgroup K) [Finite (K ⧸ S)] (w : W) :
    cosetAverage ρ S w ∈ Submodule.span ℂ (Set.range fun k : K => ρ k w) := by
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  rw [cosetAverage_eq_sum]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c _ => Submodule.subset_span ⟨c.out, rfl⟩)

private theorem cosetAverage_add (S : Subgroup K) [Finite (K ⧸ S)] (w₁ w₂ : W) :
    cosetAverage ρ S (w₁ + w₂) = cosetAverage ρ S w₁ + cosetAverage ρ S w₂ := by
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  simp only [cosetAverage_eq_sum, map_add, Finset.sum_add_distrib, smul_add]

private theorem cosetAverage_smul (S : Subgroup K) [Finite (K ⧸ S)] (a : ℂ) (w : W) :
    cosetAverage ρ S (a • w) = a • cosetAverage ρ S w := by
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  simp only [cosetAverage_eq_sum, map_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

end CosetAverage

section LocalAverage

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G W} {L : Subgroup G}

variable (π L) in

private def restrictRep : Representation ℂ L W := π.comp L.subtype

private theorem finite_quotient_comap_subtype (hL : IsCompact (L : Set G)) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) : Finite (L ⧸ U.comap L.subtype) := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  refine Subgroup.quotient_finite_of_isOpen _ ?_
  rw [Subgroup.coe_comap]
  show IsOpen ((Subtype.val : L → G) ⁻¹' (U : Set G))
  exact hU.preimage continuous_subtype_val

variable (L) in

private def fixingSubgroup (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) (w : W) :
    Subgroup L :=
  (Classical.choose (hsm w)).comap L.subtype

private theorem finite_quotient_fixingSubgroup (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) (w : W) :
    Finite (L ⧸ fixingSubgroup L hsm w) :=
  finite_quotient_comap_subtype hL _ (Classical.choose_spec (hsm w)).1

omit [IsTopologicalGroup G] in
private theorem fixingSubgroup_fixes (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w)
    (w : W) : ∀ s ∈ fixingSubgroup L hsm w, restrictRep π L s w = w :=
  fun s hs => (Classical.choose_spec (hsm w)).2 (s : G) (Subgroup.mem_comap.mp hs)

variable (L) in

private def localAverage (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) (w : W) : W :=
  cosetAverage (restrictRep π L) (fixingSubgroup L hsm w) w

private theorem exists_finite_quotient_fixing (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) (w : W) :
    ∃ S : Subgroup L, Finite (L ⧸ S) ∧ ∀ s ∈ S, π (s : G) w = w :=
  ⟨fixingSubgroup L hsm w, finite_quotient_fixingSubgroup hL hsm w, fun s hs => fixingSubgroup_fixes hsm w s hs⟩

private theorem localAverage_eq_cosetAverage (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) {w : W} (S : Subgroup L)
    [Finite (L ⧸ S)] (hS : ∀ s ∈ S, π (s : G) w = w) : localAverage L hsm w = cosetAverage (restrictRep π L) S w := by
  haveI := finite_quotient_fixingSubgroup hL hsm w
  haveI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient (H := S)
  haveI : (fixingSubgroup L hsm w).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient (H := fixingSubgroup L hsm w)
  have h₁ := cosetAverage_eq_of_le (restrictRep π L)
    (inf_le_right : S ⊓ fixingSubgroup L hsm w ≤ fixingSubgroup L hsm w) (fixingSubgroup_fixes hsm w)
  have h₂ := cosetAverage_eq_of_le (restrictRep π L) (inf_le_left : S ⊓ fixingSubgroup L hsm w ≤ S)
    (fun s hs => hS s hs)
  exact h₁.symm.trans h₂

private theorem rep_localAverage (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) (w : W) (l : L) :
    π (l : G) (localAverage L hsm w) = localAverage L hsm w := by
  haveI := finite_quotient_fixingSubgroup hL hsm w
  exact rep_cosetAverage (restrictRep π L) (fixingSubgroup_fixes hsm w) l

private theorem localAverage_eq_self (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) {w : W}
    (hw : ∀ l : L, π (l : G) w = w) : localAverage L hsm w = w := by
  haveI := finite_quotient_fixingSubgroup hL hsm w
  exact cosetAverage_eq_self (restrictRep π L) (fixingSubgroup L hsm w) fun l => hw l

private theorem localAverage_mem_span (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) (w : W) :
    localAverage L hsm w ∈ Submodule.span ℂ (Set.range fun l : L => π (l : G) w) := by
  haveI := finite_quotient_fixingSubgroup hL hsm w
  exact cosetAverage_mem_span (restrictRep π L) (fixingSubgroup L hsm w) w

private theorem localAverage_add (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) (w₁ w₂ : W) :
    localAverage L hsm (w₁ + w₂) = localAverage L hsm w₁ + localAverage L hsm w₂ := by
  haveI := finite_quotient_fixingSubgroup hL hsm w₁
  haveI := finite_quotient_fixingSubgroup hL hsm w₂
  haveI : (fixingSubgroup L hsm w₁).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient (H := fixingSubgroup L hsm w₁)
  haveI : (fixingSubgroup L hsm w₂).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient (H := fixingSubgroup L hsm w₂)
  have h₁ : ∀ s ∈ fixingSubgroup L hsm w₁ ⊓ fixingSubgroup L hsm w₂, π (s : G) w₁ = w₁ :=
    fun s hs => fixingSubgroup_fixes hsm w₁ s (Subgroup.mem_inf.mp hs).1
  have h₂ : ∀ s ∈ fixingSubgroup L hsm w₁ ⊓ fixingSubgroup L hsm w₂, π (s : G) w₂ = w₂ :=
    fun s hs => fixingSubgroup_fixes hsm w₂ s (Subgroup.mem_inf.mp hs).2
  have h₁₂ : ∀ s ∈ fixingSubgroup L hsm w₁ ⊓ fixingSubgroup L hsm w₂, π (s : G) (w₁ + w₂) = w₁ + w₂ :=
    fun s hs => by rw [map_add, h₁ s hs, h₂ s hs]
  rw [localAverage_eq_cosetAverage hL hsm _ h₁₂, localAverage_eq_cosetAverage hL hsm _ h₁,
    localAverage_eq_cosetAverage hL hsm _ h₂, cosetAverage_add]

private theorem localAverage_smul (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) (a : ℂ) (w : W) :
    localAverage L hsm (a • w) = a • localAverage L hsm w := by
  haveI := finite_quotient_fixingSubgroup hL hsm w
  have hw : ∀ s ∈ fixingSubgroup L hsm w, π (s : G) w = w := fun s hs => fixingSubgroup_fixes hsm w s hs
  have haw : ∀ s ∈ fixingSubgroup L hsm w, π (s : G) (a • w) = a • w := fun s hs => by rw [map_smul, hw s hs]
  rw [localAverage_eq_cosetAverage hL hsm _ haw, cosetAverage_smul, localAverage_eq_cosetAverage hL hsm _ hw]

variable (L) in

private def localAverageLinear (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) : W →ₗ[ℂ] W where
  toFun := localAverage L hsm
  map_add' := localAverage_add hL hsm
  map_smul' := localAverage_smul hL hsm

private theorem localAverageLinear_apply (hL : IsCompact (L : Set G))
    (hsm : ∀ w : W, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u w = w) (w : W) :
    localAverageLinear L hL hsm w = localAverage L hsm w := rfl

end LocalAverage

private noncomputable def liftMatrix (E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) :
    Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing ℚ) :=
  (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm.toRingHom.mapMatrix (Matrix.of E)

private theorem det_liftMatrix (E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) :
    (liftMatrix E).det =
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm.toRingHom (Matrix.of E).det :=
  (RingHom.map_det _ _).symm

private theorem isUnit_liftMatrix {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ}
    (h : IsUnit (Matrix.det (Matrix.of E))) : IsUnit (liftMatrix E) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_liftMatrix]
  exact h.map _

private noncomputable def archLift (E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) :
    GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) :=
  open scoped Classical in
  if h : IsUnit (Matrix.det (Matrix.of E)) then (isUnit_liftMatrix h).unit else 1

private noncomputable def archCutoff (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ)
    (E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) : ℂ :=
  open scoped Classical in
  if IsUnit (Matrix.det (Matrix.of E)) then fa (archLift E) else 0

private theorem liftMatrix_archEntries (g : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) :
    liftMatrix (AutomorphicForm.archEntries ℚ g) = (g : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) := by
  refine Matrix.ext fun i j => ?_
  simp only [liftMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    AutomorphicForm.archEntries_apply]
  exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm_apply_apply _

private theorem isUnit_det_of_archEntries (g : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) :
    IsUnit (Matrix.det (Matrix.of (AutomorphicForm.archEntries ℚ g))) := by
  have h1 : (Matrix.of (AutomorphicForm.archEntries ℚ g)) =
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).toRingHom.mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, AutomorphicForm.archEntries_apply]
    rfl
  rw [h1, ← RingHom.map_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).map _

private theorem archLift_archEntries (g : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) :
    archLift (AutomorphicForm.archEntries ℚ g) = g := by
  unfold archLift
  rw [dif_pos (isUnit_det_of_archEntries g)]
  exact Units.ext (by rw [IsUnit.unit_spec, liftMatrix_archEntries])

private theorem archCutoff_archEntries (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ)
    (g : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) :
    archCutoff fa (AutomorphicForm.archEntries ℚ g) = fa g := by
  unfold archCutoff
  rw [if_pos (isUnit_det_of_archEntries g), archLift_archEntries]

private theorem continuous_archEntries : Continuous (AutomorphicForm.archEntries ℚ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [AutomorphicForm.archEntries_apply]
  exact (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace (K := ℚ)).comp (Units.continuous_val.matrix_elem i j)

open scoped Classical in
private theorem continuous_of_isArchTestFactor {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) : Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩ := hfa
  have h : fa = Φ ∘ AutomorphicForm.archEntries ℚ := funext hfaΦ
  rw [h]
  exact hΦ.continuous.comp continuous_archEntries

private theorem adelicGL2_ext {x y : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ}
    (ha : NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ x =
      NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ y)
    (hf : NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x =
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  refine Prod.ext ?_ ?_
  · have h := congrArg (fun u : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) =>
      (u : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) i j) ha
    simpa only [NumberField.AdelicLevel.glArch_apply] using h
  · have h := congrArg (fun u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) =>
      (u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) i j) hf
    simpa only [NumberField.AdelicLevel.glFin_apply] using h

private theorem eq_adelicArchGLIncl_mul_finEmbed (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    x = AutomorphicForm.adelicArchGLIncl ℚ (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ x) *
      AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x) := by
  refine adelicGL2_ext ?_ ?_
  · rw [map_mul, AutomorphicForm.glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  · rw [map_mul, AutomorphicForm.glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]

private theorem adelicArchGLIncl_mul_finEmbed_comm (a : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ))
    (h : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    AutomorphicForm.adelicArchGLIncl ℚ a * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h =
      AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h * AutomorphicForm.adelicArchGLIncl ℚ a := by
  refine adelicGL2_ext ?_ ?_
  · rw [map_mul, map_mul, AutomorphicForm.glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one, one_mul]
  · rw [map_mul, map_mul, AutomorphicForm.glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, mul_one, one_mul]

private theorem coe_adelicArchGLIncl_apply (a : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) (i j : Fin 2) :
    ((AutomorphicForm.adelicArchGLIncl ℚ a : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) i j =
      ((a : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) i j) := by
  refine Prod.ext ?_ ?_
  · have h := congrArg (fun u : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) =>
      (u : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) i j) (AutomorphicForm.glArch_adelicArchGLIncl ℚ a)
    simpa only [NumberField.AdelicLevel.glArch_apply] using h
  · have h := congrArg (fun u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) =>
      (u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) i j)
      (AutomorphicForm.glFin_adelicArchGLIncl ℚ a)
    simpa [NumberField.AdelicLevel.glFin_apply] using h

private theorem continuous_coe_adelicArchGLIncl :
    Continuous fun a : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) =>
      ((AutomorphicForm.adelicArchGLIncl ℚ a : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) := by
  refine continuous_matrix fun i j => ?_
  simp only [coe_adelicArchGLIncl_apply]
  exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const

private theorem continuous_adelicArchGLIncl : Continuous (AutomorphicForm.adelicArchGLIncl ℚ) := by
  refine Units.continuous_iff.2 ⟨continuous_coe_adelicArchGLIncl, ?_⟩
  simp only [← map_inv]
  exact continuous_coe_adelicArchGLIncl.comp continuous_inv

private theorem rightConv_smul_right (a : ℂ) (ψ f : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    AutomorphicForm.rightConv ℚ ψ (a • f) = a • AutomorphicForm.rightConv ℚ ψ f := by
  funext y
  simp only [AutomorphicForm.rightConv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ a]
  exact MeasureTheory.integral_const_mul a _

private theorem integrable_mul_of_continuous {ψ f : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}
    (hψ : Continuous ψ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (y : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    letI := NumberField.AdelicHaar.glBorel (Fin 2) (NumberField.RingOfIntegers ℚ) ℚ
    MeasureTheory.Integrable (fun x => ψ (y * x) * f x)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (NumberField.RingOfIntegers ℚ) ℚ) := by
  letI : MeasurableSpace (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :=
    NumberField.AdelicHaar.glBorel (Fin 2) (NumberField.RingOfIntegers ℚ) ℚ
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (NumberField.RingOfIntegers ℚ) ℚ
  haveI : (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (NumberField.RingOfIntegers ℚ) ℚ).IsHaarMeasure :=
    NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (NumberField.RingOfIntegers ℚ) ℚ
  have hc : Continuous fun x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ => ψ (y * x) * f x :=
    (hψ.comp (continuous_const.mul continuous_id)).mul hf
  have hs : HasCompactSupport fun x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ => ψ (y * x) * f x :=
    hfc.mul_left
  exact hc.integrable_of_hasCompactSupport hs

private theorem rightConv_add_right {ψ f₁ f₂ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}
    (hψ : Continuous ψ) (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁) (hf₂ : Continuous f₂)
    (hf₂c : HasCompactSupport f₂) :
    AutomorphicForm.rightConv ℚ ψ (f₁ + f₂) = AutomorphicForm.rightConv ℚ ψ f₁ + AutomorphicForm.rightConv ℚ ψ f₂ := by
  funext y
  simp only [AutomorphicForm.rightConv, Pi.add_apply, mul_add]
  exact MeasureTheory.integral_add (integrable_mul_of_continuous hψ hf₁ hf₁c y)
    (integrable_mul_of_continuous hψ hf₂ hf₂c y)

private theorem rightConv_finset_sum_right {ι : Type} (s : Finset ι)
    {ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hψ : Continuous ψ)
    {f : ι → AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hf : ∀ i ∈ s, Continuous (f i))
    (hfc : ∀ i ∈ s, HasCompactSupport (f i)) :
    AutomorphicForm.rightConv ℚ ψ (∑ i ∈ s, f i) = ∑ i ∈ s, AutomorphicForm.rightConv ℚ ψ (f i) := by
  funext y
  simp only [AutomorphicForm.rightConv, Finset.sum_apply, Finset.mul_sum]
  exact MeasureTheory.integral_finsetSum s fun i hi => integrable_mul_of_continuous hψ (hf i hi) (hfc i hi) y

private abbrev archLocus : Set (Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) :=
  {E | IsUnit (Matrix.det (Matrix.of E))}

private theorem archCutoff_of_isUnit (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ)
    {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ} (h : IsUnit (Matrix.det (Matrix.of E))) :
    archCutoff fa E = fa (archLift E) := by
  unfold archCutoff
  rw [if_pos h]

private theorem archCutoff_of_not_isUnit (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ)
    {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ} (h : ¬ IsUnit (Matrix.det (Matrix.of E))) :
    archCutoff fa E = 0 := by
  unfold archCutoff
  rw [if_neg h]

private theorem archEntries_archLift {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ}
    (h : IsUnit (Matrix.det (Matrix.of E))) : AutomorphicForm.archEntries ℚ (archLift E) = E := by
  unfold archLift
  rw [dif_pos h]
  funext i j
  simp only [AutomorphicForm.archEntries_apply, IsUnit.unit_spec, liftMatrix, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.of_apply]
  exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).apply_symm_apply _

private theorem isUnit_det_of_mem_image {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ}
    (hE : E ∈ AutomorphicForm.archEntries ℚ '' tsupport fa) :
    IsUnit (Matrix.det (Matrix.of E)) := by
  obtain ⟨g, -, rfl⟩ := hE
  exact isUnit_det_of_archEntries g

private theorem archCutoff_eq_zero_of_not_mem_image (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ)
    {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ}
    (hE : E ∉ AutomorphicForm.archEntries ℚ '' tsupport fa) :
    archCutoff fa E = 0 := by
  by_cases h : IsUnit (Matrix.det (Matrix.of E))
  · rw [archCutoff_of_isUnit fa h]
    by_contra hne
    exact hE ⟨archLift E, subset_tsupport fa (Function.mem_support.2 hne), archEntries_archLift h⟩
  · exact archCutoff_of_not_isUnit fa h

private theorem isCompact_image_tsupport {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) :
    IsCompact (AutomorphicForm.archEntries ℚ '' tsupport fa) :=
  hfa.2.isCompact.image continuous_archEntries

open scoped Classical in

private theorem continuous_archCutoff_mul
    (hopen : IsOpen archLocus)
    (hlift : ContinuousOn archLift archLocus)
    {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ} (hfa : AutomorphicForm.IsArchTestFactor ℚ fa)
    {Θ : (Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) → ℂ}
    (hΘ : ContinuousOn Θ archLocus) :
    Continuous fun E => archCutoff fa E * Θ E := by
  rw [continuous_iff_continuousAt]
  intro E₀
  by_cases hE₀ : E₀ ∈ AutomorphicForm.archEntries ℚ '' tsupport fa
  · have hΩ : archLocus ∈ nhds E₀ :=
      hopen.mem_nhds (isUnit_det_of_mem_image hE₀)
    have h1 : ContinuousAt (fun E => fa (archLift E) * Θ E) E₀ :=
      (((continuous_of_isArchTestFactor hfa).comp_continuousOn hlift).mul hΘ).continuousAt hΩ
    refine h1.congr ?_
    filter_upwards [hΩ] with E hE
    show fa (archLift E) * Θ E = archCutoff fa E * Θ E
    rw [archCutoff_of_isUnit fa hE]
  · have hc : (AutomorphicForm.archEntries ℚ '' tsupport fa)ᶜ ∈ nhds E₀ :=
      (isCompact_image_tsupport hfa).isClosed.isOpen_compl.mem_nhds hE₀
    have h0 : ContinuousAt (fun _ : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ => (0 : ℂ)) E₀ :=
      continuousAt_const
    refine h0.congr ?_
    filter_upwards [hc] with E hE
    show (0 : ℂ) = archCutoff fa E * Θ E
    rw [archCutoff_eq_zero_of_not_mem_image fa hE, zero_mul]

private theorem hasCompactSupport_archCutoff_mul {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) (Θ : (Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) → ℂ) :
    HasCompactSupport fun E => archCutoff fa E * Θ E := by
  refine HasCompactSupport.intro (isCompact_image_tsupport hfa) ?_
  intro E hE
  show archCutoff fa E * Θ E = 0
  rw [archCutoff_eq_zero_of_not_mem_image fa hE, zero_mul]

private theorem tsupport_archCutoff_mul_subset {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) (Θ : (Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) → ℂ) :
    tsupport (fun E => archCutoff fa E * Θ E) ⊆
      archLocus := by
  have hsupp : Function.support (fun E => archCutoff fa E * Θ E) ⊆ AutomorphicForm.archEntries ℚ '' tsupport fa := by
    intro E hE
    by_contra hn
    refine (Function.mem_support.1 hE) ?_
    show archCutoff fa E * Θ E = 0
    rw [archCutoff_eq_zero_of_not_mem_image fa hn, zero_mul]
  intro E hE
  have h1 : E ∈ closure (AutomorphicForm.archEntries ℚ '' tsupport fa) := closure_mono hsupp hE
  rw [(isCompact_image_tsupport hfa).isClosed.closure_eq] at h1
  exact isUnit_det_of_mem_image h1

open scoped Classical in

private noncomputable def archIntegralOp (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ)
    (ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ :=
  fun y => ∫ E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ,
    archCutoff fa E * ψ (y * AutomorphicForm.adelicArchGLIncl ℚ (archLift E)) *
      (((NumberField.mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 : ℝ) : ℂ)

private theorem archIntegralOp_smul (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ) (a : ℂ)
    (ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    archIntegralOp fa (a • ψ) = a • archIntegralOp fa ψ := by
  funext y
  unfold archIntegralOp
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm _ a]
  exact MeasureTheory.integral_const_mul a _

private theorem archIntegralOp_rightTranslate_finEmbed (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ)
    (h : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
    (ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    archIntegralOp fa
        (AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
          (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h) ψ) =
      AutomorphicForm.CuspidalConstituent.rightTranslate ℚ (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h)
        (archIntegralOp fa ψ) := by
  funext y
  unfold archIntegralOp
  simp only [AutomorphicForm.CuspidalConstituent.rightTranslate_apply, mul_assoc,
    adelicArchGLIncl_mul_finEmbed_comm]

open scoped Classical in

private theorem exists_rightConv_mul_indicator_eq_smul_archIntegralOp
    (hopen : IsOpen archLocus)
    (hlift : ContinuousOn archLift archLocus)
    {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ} (hfa : AutomorphicForm.IsArchTestFactor ℚ fa)
    (U' : Subgroup (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)))
    (hU'c : IsCompact (U' : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))))
    (hU'o : IsOpen (U' : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ, Continuous ψ →
        (∀ u ∈ U', AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
            (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) ψ = ψ) →
        AutomorphicForm.rightConv ℚ ψ
            (fun x => fa (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ x) *
              (U' : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))).indicator
                (fun _ => (1 : ℂ)) (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x)) =
          (c : ℂ) • archIntegralOp fa ψ := by
  obtain ⟨c, hc, hΦ⟩ :=
    AutomorphicForm.exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen ℚ U' hU'c hU'o
  refine ⟨c, hc, ?_⟩
  intro ψ hψ hinv
  funext y
  have hΘ : ContinuousOn (fun E => ψ (y * AutomorphicForm.adelicArchGLIncl ℚ (archLift E)))
      archLocus :=
    (hψ.comp (continuous_const.mul continuous_adelicArchGLIncl)).comp_continuousOn hlift
  have key := hΦ (fun E => archCutoff fa E * ψ (y * AutomorphicForm.adelicArchGLIncl ℚ (archLift E)))
    (continuous_archCutoff_mul hopen hlift hfa hΘ) (hasCompactSupport_archCutoff_mul hfa _)
    (tsupport_archCutoff_mul_subset hfa _)
  have hinv' : ∀ (a : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ))
      (u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      u ∈ (U' : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))) →
        ψ (y * AutomorphicForm.adelicArchGLIncl ℚ a * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) =
          ψ (y * AutomorphicForm.adelicArchGLIncl ℚ a) :=
    fun a u hu => congrFun (hinv u hu) _
  have hpt : ∀ x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      ψ (y * x) =
        ψ (y * AutomorphicForm.adelicArchGLIncl ℚ
            (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ x) *
          AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
            (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x)) := by
    intro x
    rw [mul_assoc, ← eq_adelicArchGLIncl_mul_finEmbed x]
  rw [Pi.smul_apply, smul_eq_mul]
  refine Eq.trans ?_ key
  simp only [AutomorphicForm.rightConv]
  congr 1
  funext x
  simp only [archCutoff_archEntries, archLift_archEntries]
  by_cases hx : NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x ∈
      (U' : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)))
  · rw [Set.indicator_apply, if_pos hx, hpt x, hinv' _ _ hx]
    ring
  · rw [Set.indicator_apply, if_neg hx]
    ring

private abbrev FinGLQ : Type := GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)

private abbrev AdelicGLQ : Type := AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ

private def rightFixing (A : Set FinGLQ) : Subgroup FinGLQ where
  carrier := {u | (∀ a ∈ A, a * u ∈ A) ∧ ∀ a ∈ A, a * u⁻¹ ∈ A}
  one_mem' := ⟨fun a ha => by simpa using ha, fun a ha => by simpa using ha⟩
  mul_mem' := by
    intro u v hu hv
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [← mul_assoc]
      exact hv.1 _ (hu.1 a ha)
    · rw [mul_inv_rev, ← mul_assoc]
      exact hu.2 _ (hv.2 a ha)
  inv_mem' := by
    intro u hu
    refine ⟨hu.2, fun a ha => ?_⟩
    rw [inv_inv]
    exact hu.1 a ha

private theorem mem_rightFixing {A : Set FinGLQ} {u : FinGLQ} :
    u ∈ rightFixing A ↔ (∀ a ∈ A, a * u ∈ A) ∧ ∀ a ∈ A, a * u⁻¹ ∈ A :=
  Iff.rfl

private theorem isOpen_rightFixing {A : Set FinGLQ} (hAc : IsCompact A) (hAo : IsOpen A) :
    IsOpen (rightFixing A : Set FinGLQ) := by
  obtain ⟨V, hV, hAV⟩ := compact_open_separated_mul_right hAc hAo subset_rfl
  have hVinv : (fun u : FinGLQ => u⁻¹) ⁻¹' V ∈ nhds (1 : FinGLQ) :=
    continuous_inv.continuousAt.preimage_mem_nhds (by simpa using hV)
  refine (rightFixing A).isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (Filter.inter_mem hV hVinv) ?_)
  intro u hu
  rw [SetLike.mem_coe, mem_rightFixing]
  exact ⟨fun a ha => hAV (Set.mul_mem_mul ha hu.1), fun a ha => hAV (Set.mul_mem_mul ha hu.2)⟩

private theorem isCompact_rightFixing {A : Set FinGLQ} (hAc : IsCompact A) (hAo : IsOpen A) {a₀ : FinGLQ}
    (ha₀ : a₀ ∈ A) : IsCompact (rightFixing A : Set FinGLQ) := by
  refine (hAc.image (continuous_const_mul a₀⁻¹)).of_isClosed_subset
    ((rightFixing A).isClosed_of_isOpen (isOpen_rightFixing hAc hAo)) ?_
  intro u hu
  rw [SetLike.mem_coe, mem_rightFixing] at hu
  exact ⟨a₀ * u, hu.1 a₀ ha₀, inv_mul_cancel_left a₀ u⟩

private theorem exists_rightFixing_of_isFinTestFactor {ff : FinGLQ → ℂ}
    (hff : AutomorphicForm.IsFinTestFactor ℚ ff) {x : FinGLQ} (hx : ff x ≠ 0) :
    ∃ H : Subgroup FinGLQ, IsCompact (H : Set FinGLQ) ∧ IsOpen (H : Set FinGLQ) ∧
      ∀ a, ff a = ff x → ∀ u ∈ H, ff (a * u) = ff x := by
  have hlc : IsLocallyConstant ff := hff.1
  have hcs : HasCompactSupport ff := hff.2
  have hAo : IsOpen (ff ⁻¹' {ff x}) := hlc _
  have hAcl : IsClosed (ff ⁻¹' {ff x}) := isClosed_singleton.preimage hlc.continuous
  have hAc : IsCompact (ff ⁻¹' {ff x}) := by
    refine hcs.isCompact.of_isClosed_subset hAcl ?_
    intro a ha
    have ha' : ff a = ff x := ha
    refine subset_tsupport ff (Function.mem_support.2 ?_)
    rw [ha']
    exact hx
  refine ⟨rightFixing (ff ⁻¹' {ff x}), isCompact_rightFixing hAc hAo (show x ∈ ff ⁻¹' {ff x} from Set.mem_singleton _),
    isOpen_rightFixing hAc hAo, ?_⟩
  intro a ha u hu
  exact (mem_rightFixing.1 hu).1 a ha

private theorem exists_expansion_of_isFinTestFactor {ff : FinGLQ → ℂ}
    (hff : AutomorphicForm.IsFinTestFactor ℚ ff) {x₀ : FinGLQ} (hx₀ : ff x₀ ≠ 0)
    (S : Subgroup FinGLQ) (hS : IsOpen (S : Set FinGLQ)) :
    ∃ U : Subgroup FinGLQ, IsCompact (U : Set FinGLQ) ∧ IsOpen (U : Set FinGLQ) ∧ U ≤ S ∧
      (∀ x : FinGLQ, ∀ u ∈ U, ff (x * u) = ff x) ∧
      ∃ r : Finset FinGLQ,
        (∀ h ∈ r, ∀ h' ∈ r, h ≠ h' → ∀ y : FinGLQ, h⁻¹ * y ∈ U → h'⁻¹ * y ∉ U) ∧
        ∀ x : FinGLQ, ff x = ∑ h ∈ r, ff h * (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (h⁻¹ * x) := by
  classical
  have hlc : IsLocallyConstant ff := hff.1
  have hcs : HasCompactSupport ff := hff.2
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover (fun z => ff ⁻¹' {ff z})
    (fun z _ => (hlc _).mem_nhds (Set.mem_singleton _))
  obtain ⟨tne, htne⟩ : ∃ tne : Finset FinGLQ, tne = t.filter (fun z => ff z ≠ 0) := ⟨_, rfl⟩
  have hchoice : ∀ z : tne, ∃ H : Subgroup FinGLQ, IsCompact (H : Set FinGLQ) ∧ IsOpen (H : Set FinGLQ) ∧
      ∀ a, ff a = ff (z : FinGLQ) → ∀ u ∈ H, ff (a * u) = ff (z : FinGLQ) := by
    intro z
    have hz : (z : FinGLQ) ∈ t.filter (fun z => ff z ≠ 0) :=
      Eq.mp (congrArg (fun s : Finset FinGLQ => (z : FinGLQ) ∈ s) htne) z.2
    exact exists_rightFixing_of_isFinTestFactor hff (Finset.mem_filter.1 hz).2
  choose H hHc hHo hH using hchoice
  have hmem_tne : ∀ {y : FinGLQ}, ff y ≠ 0 → ∃ z, z ∈ tne ∧ ff y = ff z := by
    intro y hy
    obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport ff (Function.mem_support.2 hy)))
    have hyz' : ff y = ff z := hyz
    refine ⟨z, ?_, hyz'⟩
    rw [htne, Finset.mem_filter]
    refine ⟨hzt, ?_⟩
    rw [← hyz']
    exact hy
  obtain ⟨z₁, hz₁, -⟩ := hmem_tne hx₀
  obtain ⟨U, hU⟩ : ∃ U : Subgroup FinGLQ, U = S ⊓ ⨅ z : tne, H z := ⟨_, rfl⟩
  have hUo : IsOpen (U : Set FinGLQ) := by
    rw [hU, Subgroup.coe_inf, Subgroup.coe_iInf]
    exact hS.inter (isOpen_iInter_of_finite fun z => hHo z)
  have hUS : U ≤ S := by
    rw [hU]
    exact inf_le_left
  have hU_le : ∀ z : tne, U ≤ H z := by
    intro z
    rw [hU]
    exact inf_le_right.trans (iInf_le _ z)
  have hUc : IsCompact (U : Set FinGLQ) := by
    refine (hHc ⟨z₁, hz₁⟩).of_isClosed_subset (U.isClosed_of_isOpen hUo) ?_
    intro u hu
    exact hU_le ⟨z₁, hz₁⟩ hu
  have hL : ∀ y : FinGLQ, ff y ≠ 0 → ∀ u ∈ U, ff (y * u) = ff y := by
    intro y hy u hu
    obtain ⟨z, hz, hyz⟩ := hmem_tne hy
    rw [hyz]
    exact hH ⟨z, hz⟩ y hyz u (hU_le ⟨z, hz⟩ hu)
  have hinv : ∀ x : FinGLQ, ∀ u ∈ U, ff (x * u) = ff x := by
    intro x u hu
    by_cases hx : ff x = 0
    · by_contra hne
      have hxu : ff (x * u) ≠ 0 := by
        rw [hx] at hne
        exact hne
      have h2 := hL (x * u) hxu u⁻¹ (U.inv_mem hu)
      rw [mul_inv_cancel_right] at h2
      exact hne h2.symm
    · exact hL x hx u hu
  obtain ⟨t₂, -, ht₂⟩ := hcs.isCompact.elim_nhds_subcover (fun z => {y : FinGLQ | z⁻¹ * y ∈ U})
    (fun z _ => (hUo.preimage (continuous_const_mul z⁻¹)).mem_nhds (by simp))
  obtain ⟨r, hr⟩ : ∃ r : Finset FinGLQ,
      r = (t₂.image (fun z : FinGLQ => (z : FinGLQ ⧸ U))).image (fun q : FinGLQ ⧸ U => Quotient.out q) := ⟨_, rfl⟩
  have hr_out : ∀ h ∈ r, Quotient.out (h : FinGLQ ⧸ U) = h := by
    intro h hh
    rw [hr] at hh
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hh
    rw [QuotientGroup.out_eq']
  have hdisj : ∀ h ∈ r, ∀ h' ∈ r, h ≠ h' → ∀ y : FinGLQ, h⁻¹ * y ∈ U → h'⁻¹ * y ∉ U := by
    intro h hh h' hh' hne y hy hy'
    apply hne
    have h1 : (h : FinGLQ ⧸ U) = (y : FinGLQ ⧸ U) := QuotientGroup.eq.2 hy
    have h2 : (h' : FinGLQ ⧸ U) = (y : FinGLQ ⧸ U) := QuotientGroup.eq.2 hy'
    rw [← hr_out h hh, ← hr_out h' hh', h1, h2]
  have hexp : ∀ x : FinGLQ, ff x = ∑ h ∈ r, ff h * (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (h⁻¹ * x) := by
    intro x
    by_cases hx : ∃ h ∈ r, h⁻¹ * x ∈ U
    · obtain ⟨h₀, hh₀, hx₀U⟩ := hx
      rw [Finset.sum_eq_single h₀]
      · rw [Set.indicator_apply, if_pos (show h₀⁻¹ * x ∈ (U : Set FinGLQ) from hx₀U), mul_one]
        calc ff x = ff (h₀ * (h₀⁻¹ * x)) := by rw [mul_inv_cancel_left]
          _ = ff h₀ := hinv h₀ _ hx₀U
      · intro h hh hne
        rw [Set.indicator_apply,
          if_neg (show h⁻¹ * x ∉ (U : Set FinGLQ) from hdisj h₀ hh₀ h hh (Ne.symm hne) x hx₀U), mul_zero]
      · intro h
        exact absurd hh₀ h
    · rw [Finset.sum_eq_zero]
      · by_contra hne
        obtain ⟨z, hzt₂, hzx⟩ := Set.mem_iUnion₂.1 (ht₂ (subset_tsupport ff (Function.mem_support.2 hne)))
        have hzx' : z⁻¹ * x ∈ U := hzx
        refine hx ⟨Quotient.out (z : FinGLQ ⧸ U), ?_, ?_⟩
        · rw [hr]
          exact Finset.mem_image.2 ⟨(z : FinGLQ ⧸ U), Finset.mem_image.2 ⟨z, hzt₂, rfl⟩, rfl⟩
        · have h1 : ((Quotient.out (z : FinGLQ ⧸ U) : FinGLQ) : FinGLQ ⧸ U) = (x : FinGLQ ⧸ U) := by
            rw [QuotientGroup.out_eq']
            exact QuotientGroup.eq.2 hzx'
          exact QuotientGroup.eq.1 h1
      · intro h hh
        rw [Set.indicator_apply, if_neg (show h⁻¹ * x ∉ (U : Set FinGLQ) from fun hm => hx ⟨h, hh, hm⟩), mul_zero]
  exact ⟨U, hUc, hUo, hUS, hinv, r, hdisj, hexp⟩

private theorem isFinTestFactor_indicator_coset (U : Subgroup FinGLQ) (hUc : IsCompact (U : Set FinGLQ))
    (hUo : IsOpen (U : Set FinGLQ)) (h : FinGLQ) :
    AutomorphicForm.IsFinTestFactor ℚ (fun u => (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (h⁻¹ * u)) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : h⁻¹ * x ∈ (U : Set FinGLQ)
    · refine ⟨{y : FinGLQ | h⁻¹ * y ∈ (U : Set FinGLQ)}, hUo.preimage (continuous_const_mul h⁻¹), hx, ?_⟩
      intro x' hx'
      have hx'' : h⁻¹ * x' ∈ (U : Set FinGLQ) := hx'
      show (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (h⁻¹ * x') =
        (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (h⁻¹ * x)
      rw [Set.indicator_apply, if_pos hx'', Set.indicator_apply, if_pos hx]
    · refine ⟨{y : FinGLQ | h⁻¹ * y ∈ (U : Set FinGLQ)}ᶜ,
        ((U.isClosed_of_isOpen hUo).preimage (continuous_const_mul h⁻¹)).isOpen_compl, hx, ?_⟩
      intro x' hx'
      have hx'' : h⁻¹ * x' ∉ (U : Set FinGLQ) := hx'
      show (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (h⁻¹ * x') =
        (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (h⁻¹ * x)
      rw [Set.indicator_apply, if_neg hx'', Set.indicator_apply, if_neg hx]
  · refine HasCompactSupport.intro (hUc.image (continuous_const_mul h)) ?_
    intro u hu
    have hnot : h⁻¹ * u ∉ (U : Set FinGLQ) := fun hmem => hu ⟨h⁻¹ * u, hmem, mul_inv_cancel_left h u⟩
    show (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (h⁻¹ * u) = 0
    rw [Set.indicator_apply, if_neg hnot]

private theorem isFactorizableTestFn_mul {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) {ff : FinGLQ → ℂ} (hff : AutomorphicForm.IsFinTestFactor ℚ ff) :
    AutomorphicForm.IsFactorizableTestFn ℚ fun g =>
      fa (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ g) *
        ff (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g) :=
  ⟨fa, ff, hfa, hff, fun _ => rfl⟩

private theorem mul_mem_typeSubmodule_of_forall_mul_eq {H G : Type*} [Group H] [Group G] {W : Type*}
    [AddCommGroup W] [Module ℂ W] {ι : H →* G} {ρ : Representation ℂ H W} {fa : G → ℂ}
    (hfa : fa ∈ AutomorphicForm.typeSubmodule ι ρ) {m : G → ℂ} (hm : ∀ (k : H) (x : G), m (x * ι k) = m x) :
    (fun x => fa (id x) * m x) ∈ AutomorphicForm.typeSubmodule ι ρ :=
  AutomorphicForm.comp_mul_mem_typeSubmodule_of_hom (ι := ι) (ι' := ι) (m := m) (MonoidHom.id G) (fun _ => rfl) hm hfa

private theorem isArchBiFinite_mul_comp_glFin {tys : AutomorphicForm.ArchTypeFamily ℚ} {f : AdelicGLQ → ℂ}
    (hbf : AutomorphicForm.IsArchBiFinite ℚ tys f) (m : FinGLQ → ℂ) :
    AutomorphicForm.IsArchBiFinite ℚ tys fun g =>
      f g * m (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g) := by
  have hl := hbf.1
  have hr := hbf.2
  rw [AutomorphicForm.mem_archCutSubmodule_iff] at hl
  rw [AutomorphicForm.mem_archDualCutSubmodule_iff] at hr
  have hmr : ∀ (w : NumberField.InfinitePlace ℚ) k (x : AdelicGLQ),
      m (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ
          (x * AutomorphicForm.rowIsometryInclAt₀ ℚ w k)) =
        m (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x) := by
    intro w k x
    rw [map_mul, AutomorphicForm.glFin_rowIsometryInclAt₀, mul_one]
  have hml : ∀ (w : NumberField.InfinitePlace ℚ) k (x : AdelicGLQ),
      m ((NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ
          (x * AutomorphicForm.rowIsometryInclAt₀ ℚ w k))⁻¹) =
        m ((NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x)⁻¹) := by
    intro w k x
    rw [map_mul, AutomorphicForm.glFin_rowIsometryInclAt₀, mul_one]
  have h1 : (fun x : AdelicGLQ => f x⁻¹ * m (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x⁻¹)) ∈
      AutomorphicForm.archCutSubmodule ℚ tys := by
    rw [AutomorphicForm.mem_archCutSubmodule_iff]
    intro w
    have hw := AutomorphicForm.comp_mul_mem_iSup_of_forall id
      (fun x : AdelicGLQ => m ((NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x)⁻¹))
      (fun i => AutomorphicForm.archTypeSubmoduleAt ℚ w (tys.rep w i))
      (fun i => AutomorphicForm.archTypeSubmoduleAt ℚ w (tys.rep w i))
      (fun _ _ hfa' => mul_mem_typeSubmodule_of_forall_mul_eq hfa' (hml w)) (hl w)
    simp only [id_eq] at hw
    simp only [map_inv]
    exact hw
  have h2 : (fun g : AdelicGLQ => f g * m (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g)) ∈
      AutomorphicForm.archDualCutSubmodule ℚ tys := by
    rw [AutomorphicForm.mem_archDualCutSubmodule_iff]
    intro w
    have hw := AutomorphicForm.comp_mul_mem_iSup_of_forall id
      (fun x : AdelicGLQ => m (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x))
      (fun i => AutomorphicForm.archDualTypeSubmoduleAt ℚ w (tys.rep w i))
      (fun i => AutomorphicForm.archDualTypeSubmoduleAt ℚ w (tys.rep w i))
      (fun _ _ hfa' => mul_mem_typeSubmodule_of_forall_mul_eq hfa' (hmr w)) (hr w)
    simp only [id_eq] at hw
    exact hw
  exact ⟨h1, h2⟩

private theorem isArchBiFinite_mul_comp_glFin_of_isArchBiFinite {tys : AutomorphicForm.ArchTypeFamily ℚ}
    {f : AdelicGLQ → ℂ} {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ} {ff : FinGLQ → ℂ}
    (hf : ∀ g, f g = fa (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ g) *
      ff (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g))
    (hbf : AutomorphicForm.IsArchBiFinite ℚ tys f) {h₀ : FinGLQ} (hh₀ : ff h₀ ≠ 0)
    (θ : FinGLQ → ℂ) (hθ : ∀ u, θ u ≠ 0 → ff u = ff h₀) :
    AutomorphicForm.IsArchBiFinite ℚ tys fun g =>
      fa (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ g) *
        θ (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g) := by
  have hG : (fun g : AdelicGLQ =>
        fa (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ g) *
          θ (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g)) =
      fun g : AdelicGLQ =>
        f g * ((ff h₀)⁻¹ * θ (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g)) := by
    funext g
    show fa (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ g) *
        θ (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g) =
      f g * ((ff h₀)⁻¹ * θ (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g))
    rw [hf g]
    by_cases hu : θ (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g) = 0
    · simp [hu]
    · rw [hθ _ hu, mul_assoc, mul_inv_cancel_left₀ hh₀]
  rw [hG]
  exact isArchBiFinite_mul_comp_glFin hbf fun u => (ff h₀)⁻¹ * θ u

private theorem rightConv_zero_right (ψ : AdelicGLQ → ℂ) : AutomorphicForm.rightConv ℚ ψ 0 = 0 := by
  have h := rightConv_smul_right (0 : ℂ) ψ 0
  rw [zero_smul, zero_smul] at h
  exact h

private theorem isFinTestFactor_indicator (U : Subgroup FinGLQ) (hUc : IsCompact (U : Set FinGLQ))
    (hUo : IsOpen (U : Set FinGLQ)) :
    AutomorphicForm.IsFinTestFactor ℚ (fun u => (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) u) := by
  have h := isFinTestFactor_indicator_coset U hUc hUo 1
  simp only [inv_one, one_mul] at h
  exact h

private noncomputable def levelTest (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ) (U : Subgroup FinGLQ) :
    AdelicGLQ → ℂ :=
  fun g => fa (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ g) *
    (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g)

private noncomputable def cosetTest (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ) (U : Subgroup FinGLQ)
    (h : FinGLQ) : AdelicGLQ → ℂ :=
  fun g => fa (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ g) *
    (U : Set FinGLQ).indicator (fun _ => (1 : ℂ))
      (h⁻¹ * NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g)

private theorem isFactorizableTestFn_levelTest {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) (U : Subgroup FinGLQ) (hUc : IsCompact (U : Set FinGLQ))
    (hUo : IsOpen (U : Set FinGLQ)) : AutomorphicForm.IsFactorizableTestFn ℚ (levelTest fa U) :=
  isFactorizableTestFn_mul hfa (isFinTestFactor_indicator U hUc hUo)

private theorem isFactorizableTestFn_cosetTest {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) (U : Subgroup FinGLQ) (hUc : IsCompact (U : Set FinGLQ))
    (hUo : IsOpen (U : Set FinGLQ)) (h : FinGLQ) : AutomorphicForm.IsFactorizableTestFn ℚ (cosetTest fa U h) :=
  isFactorizableTestFn_mul hfa (isFinTestFactor_indicator_coset U hUc hUo h)

private theorem continuous_and_hasCompactSupport_levelTest {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) (U : Subgroup FinGLQ) (hUc : IsCompact (U : Set FinGLQ))
    (hUo : IsOpen (U : Set FinGLQ)) : Continuous (levelTest fa U) ∧ HasCompactSupport (levelTest fa U) :=
  AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ _
    (isFactorizableTestFn_levelTest hfa U hUc hUo)

private theorem continuous_and_hasCompactSupport_cosetTest {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) (U : Subgroup FinGLQ) (hUc : IsCompact (U : Set FinGLQ))
    (hUo : IsOpen (U : Set FinGLQ)) (h : FinGLQ) :
    Continuous (cosetTest fa U h) ∧ HasCompactSupport (cosetTest fa U h) :=
  AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ _
    (isFactorizableTestFn_cosetTest hfa U hUc hUo h)

private theorem rightConv_cosetTest (fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ) (U : Subgroup FinGLQ)
    (ψ : AdelicGLQ → ℂ) (h : FinGLQ) :
    AutomorphicForm.rightConv ℚ ψ (cosetTest fa U h) =
      AutomorphicForm.CuspidalConstituent.rightTranslate ℚ (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h)
        (AutomorphicForm.rightConv ℚ ψ (levelTest fa U)) := by
  have hfun : cosetTest fa U h =
      fun y => levelTest fa U ((AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h)⁻¹ * y) := by
    funext y
    simp only [cosetTest, levelTest, map_mul, map_inv, AdelicDock.glArch_finEmbed, AdelicDock.glFin_finEmbed, inv_one,
      one_mul]
  rw [hfun]
  funext g
  exact (AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply ℚ ψ (levelTest fa U) g
    (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h)).symm

private theorem eq_sum_smul_cosetTest {f : AdelicGLQ → ℂ} {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ}
    {ff : FinGLQ → ℂ}
    (hfeq : ∀ g, f g = fa (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ g) *
      ff (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ g))
    (U : Subgroup FinGLQ) (r : Finset FinGLQ)
    (hexp : ∀ x, ff x = ∑ h ∈ r, ff h * (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (h⁻¹ * x)) :
    f = ∑ h ∈ r, ff h • cosetTest fa U h := by
  funext g
  rw [hfeq g, hexp, Finset.mul_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cosetTest]
  ring

open scoped Classical in

private theorem archIntegralOp_add_of_invariant
    (hopen : IsOpen archLocus) (hlift : ContinuousOn archLift archLocus)
    {fa : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) → ℂ} (hfa : AutomorphicForm.IsArchTestFactor ℚ fa)
    (U : Subgroup FinGLQ) (hUc : IsCompact (U : Set FinGLQ)) (hUo : IsOpen (U : Set FinGLQ))
    {φ ψ : AdelicGLQ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφU : ∀ u ∈ U,
      AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) φ = φ)
    (hψU : ∀ u ∈ U,
      AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) ψ = ψ) :
    archIntegralOp fa (φ + ψ) = archIntegralOp fa φ + archIntegralOp fa ψ := by
  obtain ⟨c, hc, hconv⟩ := exists_rightConv_mul_indicator_eq_smul_archIntegralOp hopen hlift hfa U hUc hUo
  have hsum : ∀ u ∈ U,
      AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) (φ + ψ) = φ + ψ := by
    intro u hu
    rw [AutomorphicForm.CuspidalConstituent.rightTranslate_add, hφU u hu, hψU u hu]
  have h1 : AutomorphicForm.rightConv ℚ φ (levelTest fa U) = (c : ℂ) • archIntegralOp fa φ := hconv φ hφ hφU
  have h2 : AutomorphicForm.rightConv ℚ ψ (levelTest fa U) = (c : ℂ) • archIntegralOp fa ψ := hconv ψ hψ hψU
  have h3 : AutomorphicForm.rightConv ℚ (φ + ψ) (levelTest fa U) = (c : ℂ) • archIntegralOp fa (φ + ψ) :=
    hconv (φ + ψ) (hφ.add hψ) hsum
  obtain ⟨hlc, hlcs⟩ := continuous_and_hasCompactSupport_levelTest hfa U hUc hUo
  have h4 := AutomorphicForm.rightConv_add_left ℚ hφ hψ hlc hlcs (f := levelTest fa U)
  rw [h1, h2, h3, ← smul_add] at h4
  exact smul_right_injective (AdelicGLQ → ℂ) (Complex.ofReal_ne_zero.2 hc.ne') h4

open scoped Classical in

private theorem exists_rightConv_eq_sum_rightTranslate_of_isCuspSubrep
    (hopen : IsOpen archLocus) (hlift : ContinuousOn archLift archLocus)
    (ξ : (AutomorphicForm.productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspSubrep ℚ (AutomorphicForm.productionPinsGeneral ℚ) ξ V)
    (hcont : ∀ ψ ∈ V, Continuous ψ)
    (hstab : ∀ ψ ∈ V, ∃ S : Subgroup (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      IsOpen (S : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))) ∧
        ∀ u ∈ S, AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
          (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) ψ = ψ)
    (f : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (tys : AutomorphicForm.ArchTypeFamily ℚ)
    (hf : AutomorphicForm.IsFactorizableTestFn ℚ f) (hbf : AutomorphicForm.IsArchBiFinite ℚ tys f) :
    ∃ R : (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) →
        (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ),
      (∀ φ ∈ V, ∀ ψ ∈ V, R (φ + ψ) = R φ + R ψ) ∧
      (∀ (a : ℂ) (ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ), R (a • ψ) = a • R ψ) ∧
      (∀ (h : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
          (ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ),
        R (AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
            (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h) ψ)
          = AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
              (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h) (R ψ)) ∧
      (∀ ψ ∈ V, R ψ ∈ V) ∧
      ∀ ψ ∈ V, ∃ (n : ℕ) (c : Fin n → ℂ)
        (a : Fin n → GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
        AutomorphicForm.rightConv ℚ ψ f = ∑ i, c i • AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
          (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (a i)) (R ψ) := by
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
  by_cases hex : ∃ x₀, ff x₀ ≠ 0
  swap
  ·
    have hff0 : ∀ x, ff x = 0 := fun x => by
      by_contra hx
      exact hex ⟨x, hx⟩
    have hf0 : f = 0 := by
      funext g
      show f g = 0
      rw [hfeq g, hff0, mul_zero]
    refine ⟨fun _ => 0, fun _ _ _ _ => (add_zero _).symm, fun a _ => (smul_zero a).symm,
      fun h _ => (AutomorphicForm.CuspidalConstituent.rightTranslate_zero ℚ _).symm, fun _ _ => V.zero_mem,
      fun ψ _ => ⟨0, Fin.elim0, Fin.elim0, ?_⟩⟩
    rw [hf0, rightConv_zero_right, Fin.sum_univ_zero]
  obtain ⟨x₀, hx₀⟩ := hex

  have hlevel : ∀ S : Subgroup FinGLQ, IsOpen (S : Set FinGLQ) →
      ∃ U : Subgroup FinGLQ, IsCompact (U : Set FinGLQ) ∧ IsOpen (U : Set FinGLQ) ∧ U ≤ S ∧
        (∀ x : FinGLQ, ∀ u ∈ U, ff (x * u) = ff x) ∧
        ∃ r : Finset FinGLQ, f = ∑ h ∈ r, ff h • cosetTest fa U h := by
    intro S hS
    obtain ⟨U, hUc, hUo, hUS, hUinv, r, -, hexp⟩ := exists_expansion_of_isFinTestFactor hff hx₀ S hS
    exact ⟨U, hUc, hUo, hUS, hUinv, r, eq_sum_smul_cosetTest hfeq U r hexp⟩
  refine ⟨archIntegralOp fa, ?_, archIntegralOp_smul fa, archIntegralOp_rightTranslate_finEmbed fa, ?_, ?_⟩
  ·
    intro φ hφ ψ hψ
    obtain ⟨Sφ, hSφ, hφS⟩ := hstab φ hφ
    obtain ⟨Sψ, hSψ, hψS⟩ := hstab ψ hψ
    obtain ⟨U, hUc, hUo, hUS, -, -⟩ := hlevel (Sφ ⊓ Sψ) (by rw [Subgroup.coe_inf]; exact hSφ.inter hSψ)
    exact archIntegralOp_add_of_invariant hopen hlift hfa U hUc hUo (hcont φ hφ) (hcont ψ hψ)
      (fun u hu => hφS u (Subgroup.mem_inf.1 (hUS hu)).1) (fun u hu => hψS u (Subgroup.mem_inf.1 (hUS hu)).2)
  ·
    intro ψ hψ
    obtain ⟨S, hS, hψS⟩ := hstab ψ hψ
    obtain ⟨U, hUc, hUo, hUS, hUinv, -⟩ := hlevel S hS
    obtain ⟨c, hc, hconv⟩ := exists_rightConv_mul_indicator_eq_smul_archIntegralOp hopen hlift hfa U hUc hUo
    have h1 : AutomorphicForm.rightConv ℚ ψ (levelTest fa U) = (c : ℂ) • archIntegralOp fa ψ :=
      hconv ψ (hcont ψ hψ) fun u hu => hψS u (hUS hu)

    have hθ : ∀ u : FinGLQ, (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (x₀⁻¹ * u) ≠ 0 → ff u = ff x₀ := by
      intro u hu
      by_cases hm : x₀⁻¹ * u ∈ (U : Set FinGLQ)
      · have h := hUinv x₀ (x₀⁻¹ * u) hm
        rwa [mul_inv_cancel_left] at h
      · rw [Set.indicator_apply, if_neg hm] at hu
        exact (hu rfl).elim
    have hbf' : AutomorphicForm.IsArchBiFinite ℚ tys (cosetTest fa U x₀) :=
      isArchBiFinite_mul_comp_glFin_of_isArchBiFinite hfeq hbf hx₀
        (fun u => (U : Set FinGLQ).indicator (fun _ => (1 : ℂ)) (x₀⁻¹ * u)) hθ
    have hmem : AutomorphicForm.rightConv ℚ ψ (cosetTest fa U x₀) ∈ V :=
      hV.rightConv_mem _ tys (isFactorizableTestFn_cosetTest hfa U hUc hUo x₀) hbf' ψ hψ
    rw [rightConv_cosetTest, h1, AutomorphicForm.CuspidalConstituent.rightTranslate_smul] at hmem
    have hT : AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ x₀) (archIntegralOp fa ψ) ∈ V :=
      (V.smul_mem_iff (Complex.ofReal_ne_zero.2 hc.ne')).1 hmem
    have hfin : AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ x₀⁻¹ ∈
        AutomorphicForm.finiteAdelicGL2Subgroup ℚ := by
      rw [AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]
    have hT' := hV.rightTranslate_fin_mem _ hfin _ hT
    rw [AutomorphicForm.CuspidalConstituent.rightTranslate_rightTranslate,
      ← map_mul (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ), inv_mul_cancel, map_one] at hT'
    have hone : AutomorphicForm.CuspidalConstituent.rightTranslate ℚ 1 (archIntegralOp fa ψ) =
        archIntegralOp fa ψ := by
      funext x
      show archIntegralOp fa ψ (x * 1) = archIntegralOp fa ψ x
      rw [mul_one]
    rwa [hone] at hT'
  ·
    intro ψ hψ
    obtain ⟨S, hS, hψS⟩ := hstab ψ hψ
    obtain ⟨U, hUc, hUo, hUS, -, r, hfr⟩ := hlevel S hS
    obtain ⟨c, hc, hconv⟩ := exists_rightConv_mul_indicator_eq_smul_archIntegralOp hopen hlift hfa U hUc hUo
    have h1 : AutomorphicForm.rightConv ℚ ψ (levelTest fa U) = (c : ℂ) • archIntegralOp fa ψ :=
      hconv ψ (hcont ψ hψ) fun u hu => hψS u (hUS hu)
    have hterm : ∀ h ∈ r, AutomorphicForm.rightConv ℚ ψ (ff h • cosetTest fa U h) =
        (ff h * (c : ℂ)) • AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
          (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h) (archIntegralOp fa ψ) := by
      intro h _
      rw [rightConv_smul_right, rightConv_cosetTest, h1, AutomorphicForm.CuspidalConstituent.rightTranslate_smul,
        smul_smul]
    have hFc : ∀ h ∈ r, Continuous (ff h • cosetTest fa U h) := fun h _ =>
      (continuous_and_hasCompactSupport_cosetTest hfa U hUc hUo h).1.const_smul (ff h)
    have hFcs : ∀ h ∈ r, HasCompactSupport (ff h • cosetTest fa U h) := fun h _ =>
      (continuous_and_hasCompactSupport_cosetTest hfa U hUc hUo h).2.mono fun g hg =>
        Function.mem_support.2 fun hz => Function.mem_support.1 hg (by
          show ff h * cosetTest fa U h g = 0
          rw [hz, mul_zero])
    have hsum : AutomorphicForm.rightConv ℚ ψ f =
        ∑ h ∈ r, (ff h * (c : ℂ)) • AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
          (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ h) (archIntegralOp fa ψ) := by
      rw [hfr, rightConv_finset_sum_right r (hcont ψ hψ) hFc hFcs]
      exact Finset.sum_congr rfl hterm
    refine ⟨r.card, fun i => ff ((r.equivFin.symm i : r) : FinGLQ) * (c : ℂ),
      fun i => ((r.equivFin.symm i : r) : FinGLQ), ?_⟩
    rw [hsum, ← Finset.sum_coe_sort r _]
    exact Fintype.sum_equiv r.equivFin _ _ fun x => by simp only [Equiv.symm_apply_apply]

open scoped Classical in

private theorem norm_ringEquiv_mixedSpace_symm_apply_le (y : NumberField.mixedEmbedding.mixedSpace ℚ)
    (w : NumberField.InfinitePlace ℚ) :
    ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y w‖ ≤ ‖y‖ := by
  have h : ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y w‖ ≤
      ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ
        ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y)‖ := by
    by_cases hw : w.IsReal
    · exact NumberField.AdelicBox.norm_apply_le_of_isReal (K := ℚ) _ hw
    · exact NumberField.AdelicBox.norm_apply_le_of_isComplex (K := ℚ) _
        (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw)
  rwa [RingEquiv.apply_symm_apply] at h

open scoped Classical in

private theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm := by
  refine continuous_of_continuousAt_zero (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm ?_
  have hw : ∀ w : NumberField.InfinitePlace ℚ,
      ContinuousAt (fun y : NumberField.mixedEmbedding.mixedSpace ℚ =>
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y w) 0 := by
    intro w
    show Filter.Tendsto _ (nhds 0) (nhds ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm 0 w))
    rw [map_zero]
    exact squeeze_zero_norm (fun y => norm_ringEquiv_mixedSpace_symm_apply_le y w) tendsto_norm_zero
  exact continuousAt_pi.mpr hw

private theorem continuous_liftMatrix : Continuous liftMatrix := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ =>
    (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm (E i j)
  exact continuous_ringEquiv_mixedSpace_symm.comp ((continuous_apply j).comp (continuous_apply i))

private def nonzeroLocus : Set (NumberField.InfiniteAdeleRing ℚ) :=
  {x | ∀ w : NumberField.InfinitePlace ℚ, NumberField.AdelicLevel.archEval ℚ w x ≠ 0}

private theorem isOpen_nonzeroLocus : IsOpen nonzeroLocus := by
  have h : nonzeroLocus =
      ⋂ w : NumberField.InfinitePlace ℚ, {x | NumberField.AdelicLevel.archEval ℚ w x ≠ 0} := by
    ext x
    simp only [nonzeroLocus, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun w => isOpen_ne.preimage (NumberField.AdelicLevel.continuous_archEval ℚ w)

private theorem mem_nonzeroLocus_of_isUnit {x : NumberField.InfiniteAdeleRing ℚ} (hx : IsUnit x) :
    x ∈ nonzeroLocus := by
  intro w
  exact (hx.map (NumberField.AdelicLevel.archEval ℚ w)).ne_zero

private noncomputable def coordInverse (x : NumberField.InfiniteAdeleRing ℚ) : NumberField.InfiniteAdeleRing ℚ :=
  fun w => (NumberField.AdelicLevel.archEval ℚ w x)⁻¹

private noncomputable def unitOfMemNonzeroLocus {x : NumberField.InfiniteAdeleRing ℚ} (hx : x ∈ nonzeroLocus) :
    (NumberField.InfiniteAdeleRing ℚ)ˣ where
  val := x
  inv := coordInverse x
  val_inv := funext fun w => mul_inv_cancel₀ (hx w)
  inv_val := funext fun w => inv_mul_cancel₀ (hx w)

private theorem isUnit_of_mem_nonzeroLocus {x : NumberField.InfiniteAdeleRing ℚ} (hx : x ∈ nonzeroLocus) :
    IsUnit x :=
  ⟨unitOfMemNonzeroLocus hx, rfl⟩

private theorem ringInverse_eq_coordInverse {x : NumberField.InfiniteAdeleRing ℚ} (hx : x ∈ nonzeroLocus) :
    Ring.inverse x = coordInverse x :=
  Ring.inverse_unit (unitOfMemNonzeroLocus hx)

private theorem continuousOn_ringInverse_nonzeroLocus :
    ContinuousOn (Ring.inverse : NumberField.InfiniteAdeleRing ℚ → NumberField.InfiniteAdeleRing ℚ)
      nonzeroLocus := by
  have hc : ContinuousOn (fun x : NumberField.InfiniteAdeleRing ℚ =>
      (coordInverse x : Π w : NumberField.InfinitePlace ℚ, w.Completion)) nonzeroLocus :=
    continuousOn_pi.mpr fun w =>
      (NumberField.AdelicLevel.continuous_archEval ℚ w).continuousOn.inv₀ fun x (hx : x ∈ nonzeroLocus) => hx w
  exact hc.congr fun x hx => ringInverse_eq_coordInverse hx

private def invertibleLocus : Set (Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) :=
  {E | IsUnit (Matrix.det (Matrix.of E))}

private theorem mem_invertibleLocus_iff (E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ) :
    E ∈ invertibleLocus ↔ (liftMatrix E).det ∈ nonzeroLocus := by
  constructor
  · intro h
    exact mem_nonzeroLocus_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_liftMatrix h))
  · intro h
    show IsUnit (Matrix.det (Matrix.of E))
    have h1 : IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm.toRingHom (Matrix.of E).det) := by
      rw [← det_liftMatrix]
      exact isUnit_of_mem_nonzeroLocus h
    have h2 : IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm (Matrix.of E).det) := h1
    have h3 := h2.map (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace ℚ)
    rwa [RingEquiv.apply_symm_apply] at h3

private theorem isOpen_setOf_isUnit_det :
    IsOpen {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ | IsUnit (Matrix.det (Matrix.of E))} := by
  show IsOpen invertibleLocus
  have h : invertibleLocus = (fun E => (liftMatrix E).det) ⁻¹' nonzeroLocus := Set.ext mem_invertibleLocus_iff
  rw [h]
  exact isOpen_nonzeroLocus.preimage continuous_liftMatrix.matrix_det

private theorem coe_archLift_of_isUnit {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ}
    (h : IsUnit (Matrix.det (Matrix.of E))) :
    (archLift E : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) = liftMatrix E := by
  unfold archLift
  rw [dif_pos h]
  exact (isUnit_liftMatrix h).unit_spec

private theorem coe_archLift_inv_of_isUnit {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ}
    (h : IsUnit (Matrix.det (Matrix.of E))) :
    (((archLift E)⁻¹ : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) :
        Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) =
      Ring.inverse (liftMatrix E).det • (liftMatrix E).adjugate := by
  rw [Matrix.coe_units_inv, coe_archLift_of_isUnit h, Matrix.inv_def]

private theorem continuousOn_archLift :
    ContinuousOn archLift
      {E : Fin 2 → Fin 2 → NumberField.mixedEmbedding.mixedSpace ℚ | IsUnit (Matrix.det (Matrix.of E))} := by
  show ContinuousOn archLift invertibleLocus
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine (continuous_liftMatrix.comp continuous_subtype_val).congr fun E => ?_
    exact (coe_archLift_of_isUnit E.2).symm
  · have hdet : Continuous fun E : invertibleLocus => (liftMatrix E.1).det :=
      continuous_liftMatrix.matrix_det.comp continuous_subtype_val
    have hinv : Continuous fun E : invertibleLocus => Ring.inverse (liftMatrix E.1).det :=
      continuousOn_ringInverse_nonzeroLocus.comp_continuous hdet fun E => (mem_invertibleLocus_iff E.1).mp E.2
    have hadj : Continuous fun E : invertibleLocus => (liftMatrix E.1).adjugate :=
      (continuous_liftMatrix.comp continuous_subtype_val).matrix_adjugate
    refine (hinv.smul hadj).congr fun E => ?_
    exact (coe_archLift_inv_of_isUnit E.2).symm

section Rational

variable {pins : CarrierPins ℚ} {ξ : pins.Z →* ℂˣ}
variable {V : Submodule ℂ (AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)}

private theorem finFixing_eq_finiteFixing (φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    finFixing ℚ φ = finiteFixing φ :=
  Subgroup.ext fun k => (mem_finiteFixing_iff φ k).symm

private theorem isOpen_finFixing_of_mem (hV : IsCuspSubrep ℚ pins ξ V)
    {φ : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : φ ∈ V) :
    IsOpen (finFixing ℚ φ :
      Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))) := by
  rw [finFixing_eq_finiteFixing]
  exact isOpen_finiteFixing_of_mem_cuspKFiniteSubmodule pins ξ (hV.le hφ)

private theorem rowIsometryInclAt₀_mul_finEmbed_comm (w : NumberField.InfinitePlace ℚ)
    (k : rowIsometrySubgroup₀ w.Completion)
    (x : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    rowIsometryInclAt₀ ℚ w k * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ x =
      AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ x * rowIsometryInclAt₀ ℚ w k := by
  rw [rowIsometryInclAt₀_apply]
  exact adelicArchGLIncl_mul_finEmbed_comm (archGLIncl ℚ w (k : GL (Fin 2) w.Completion)) x

private theorem exists_isOpen_forall_locRep_eq (hV : IsCuspSubrep ℚ pins ξ V)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (w : ↥V) :
    ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧
      ∀ u ∈ U, locRep v hV u w = w :=
  ⟨localFixing v (w : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ),
    isOpen_localFixing_of_mem_cuspKFiniteSubmodule v pins ξ (hV.le w.2),
    fun u hu => Subtype.ext ((mem_localFixing_iff v _ u).mp hu)⟩

private def averagingOpsAt (hV : IsCuspSubrep ℚ pins ξ V)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (L : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) (hL : IsCompact (L : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :
    AveragingOps (locRep v hV) L where
  average := localAverageLinear L hL (exists_isOpen_forall_locRep_eq hV v)
  exists_finite := exists_finite_quotient_fixing hL (exists_isOpen_forall_locRep_eq hV v)
  average_eq S w hfin hS := by
    haveI := hfin
    exact localAverage_eq_cosetAverage hL (exists_isOpen_forall_locRep_eq hV v) S hS
  apply_average w l hl := rep_localAverage hL (exists_isOpen_forall_locRep_eq hV v) w ⟨l, hl⟩
  average_eq_self w hw := localAverage_eq_self hL (exists_isOpen_forall_locRep_eq hV v) fun l => hw l l.2
  average_mem_span w := localAverage_mem_span hL (exists_isOpen_forall_locRep_eq hV v) w

private theorem hasFiniteExpansion_of_isCuspSubrep (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ))
    (hV : IsCuspSubrep ℚ (productionPinsGeneral ℚ) ξ V) (f : AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (tys : ArchTypeFamily ℚ) (hf : IsFactorizableTestFn ℚ f) (hbf : IsArchBiFinite ℚ tys f) :
    HasFiniteExpansion ℚ V f := by
  obtain ⟨R, hadd, hsmul, hcomm, hRV, hsum⟩ :=
    exists_rightConv_eq_sum_rightTranslate_of_isCuspSubrep isOpen_setOf_isUnit_det continuousOn_archLift ξ V hV
      (fun ψ hψ => continuous_of_mem_cuspKFiniteSubmodule _ ξ (hV.le hψ))
      (fun ψ hψ => ⟨finiteFixing ψ, isOpen_finiteFixing_of_mem_cuspKFiniteSubmodule _ ξ (hV.le hψ),
        fun u hu => (mem_finiteFixing_iff ψ u).mp hu⟩)
      f tys hf hbf
  refine ⟨R, hRV, fun k ψ _ => hcomm k ψ, hadd, fun a ψ _ => hsmul a ψ, fun ψ hψ => ?_⟩
  obtain ⟨n, c, a, h⟩ := hsum ψ hψ
  exact ⟨n, a, c, h⟩

end Rational

end AutomorphicForm.CuspidalConstituent.LocalComponent

open AutomorphicForm.CuspidalConstituent.LocalComponent in

theorem solution
    (ξ : (AutomorphicForm.productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent ℚ
      (AutomorphicForm.productionPinsGeneral ℚ) ξ V)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X)
      (π : Representation ℂ (GL (Fin 2) (v.adicCompletion ℚ)) X),
      (∀ x : X, ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
          IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧ ∀ u ∈ U, π u x = x) ∧
      (∃ x : X, x ≠ 0) ∧
      (∀ T : Submodule ℂ X, (∀ (g : GL (Fin 2) (v.adicCompletion ℚ)) (x : X), x ∈ T → π g x ∈ T) →
          T = ⊥ ∨ T = ⊤) ∧
      (∀ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
          IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) →
          ∃ T : Submodule ℂ X, FiniteDimensional ℂ T ∧
            ∀ x : X, (∀ u ∈ U, π u x = x) → x ∈ T) ∧
      ∀ φ ∈ V, ∃ (n : ℕ) (x : Fin n → X)
          (f : Fin n → (X →ₗ[ℂ] (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ))),
          (∀ i : Fin n, (∀ y : X, f i y ∈ V) ∧
            ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)) (y : X),
              f i (π g y) =
                AutomorphicForm.CuspidalConstituent.rightTranslate ℚ
                  (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
                    (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g)) (f i y)) ∧
          φ = ∑ i : Fin n, f i (x i) :=
  exists_localComponent hV v (continuous_localEmbed v) (exists_isCompact_isOpen_subgroup v)
    (fun _ hφ => isOpen_finFixing_of_mem hV.1 hφ)
    (fun _ hφ => exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule _ ξ (hV.1.le hφ))
    (fun tys k _ hφ => rightTranslate_finEmbed_mem_archCutSubmodule adelicArchGLIncl_mul_finEmbed_comm tys hφ k)
    rowIsometryInclAt₀_mul_finEmbed_comm
    (fun f tys hf hbf => hasFiniteExpansion_of_isCuspSubrep ξ V hV.1 f tys hf hbf)
    (fun K hK tys W hWV hWK hWt =>
      AutomorphicForm.CuspidalConstituent.IsCuspConstituent.finiteDimensional_of_forall_rightTranslate_eq ξ V hV
        K hK tys W hWV hWK hWt)
    fun L hL _ => averagingOpsAt hV.1 v L hL

end

end S_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_exists_irreducible_admissible_isotypicAt
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_exists_irreducible_admissible_isotypicAt (solution)
