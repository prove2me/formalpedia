-- Prove2me | solution 1 for AutomorphicForm.exists_finset_sum_convOp_eq_self_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/72a64a68-ebcd-52ad-ac15-f752d8c42fd2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_sum_convOp_eq_self_of_isCuspConstituent
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

open AutomorphicForm AutomorphicForm.CuspidalConstituent

namespace TierCompression

section OneField

variable (F : Type) [Field F] [NumberField F]

private theorem continuous_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hcont, -⟩
    exact hcont
  · exact continuous_zero
  · intro x y _ _ hx hy
    exact hx.add hy
  · intro c x _ hx
    exact hx.const_smul c

private theorem rightConv_mem_levelInvariantSubmodule (pins : CarrierPins F) (N : Ideal (𝓞 F))
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : ∀ k ∈ pins.U N, ∀ y, f (k * y) = f y) (w : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F w f ∈ levelInvariantSubmodule F pins N := by
  show ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ pins.U N, rightConv F w f (g * k) = rightConv F w f g
  intro g k hk
  rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F w f g k]
  have hfk : (fun y => f (k⁻¹ * y)) = f := funext fun y => hf k⁻¹ (inv_mem hk) y
  rw [hfk]

end OneField

private theorem map_algebraMap_ne_bot (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥) : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ :=
  fun h => hNK ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).mp h)

section

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private abbrev pinsAt (D : Set (AdelicGL2 (𝓞 L) L)) : CarrierPins L :=
  productionPinsOf L D (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
    (adelicBox L)

private abbrev levU (NK : Ideal (𝓞 K)) : Subgroup (AdelicGL2 (𝓞 L) L) :=
  levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L

private abbrev tierFn (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (tys : ArchTypeFamily L)
    (g : AdelicGL2 (𝓞 L) L → ℂ) : Prop :=
  IsUnitFactorizableAboveOfType K L tys (levU K L NK) SK g

private abbrev Ecut (D : Set (AdelicGL2 (𝓞 L) L)) (NK : Ideal (𝓞 K)) (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)) : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) :=
  V ⊓ levelInvariantSubmodule L (pinsAt L D) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ archCutSubmodule L tys

private structure Ctx (D : Set (AdelicGL2 (𝓞 L) L)) (ξ : (pinsAt L D).Z →* ℂˣ) (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)) : Prop where
  hV : IsCuspConstituent L (pinsAt L D) ξ V
  hTYS : ∀ g : AdelicGL2 (𝓞 L) L → ℂ, IsFactorizableTestFn L g → (fun x => g x⁻¹) ∈ archCutSubmodule L tys →
    ∀ w : AdelicGL2 (𝓞 L) L → ℂ, Continuous w → rightConv L w g ∈ archCutSubmodule L tys

private theorem tier_isFactorizableTestFn {NK : Ideal (𝓞 K)} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {tys : ArchTypeFamily L} {g : AdelicGL2 (𝓞 L) L → ℂ} (hg : tierFn K L NK SK tys g) :
    IsFactorizableTestFn L g := by
  obtain ⟨φa, φf, φS, h₁, h₂, -, -, -, h₆⟩ := hg.1.2
  exact ⟨φa, φf, h₁, h₂, h₆⟩

end

section Operators

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {D : Set (AdelicGL2 (𝓞 L) L)} {ξ : (pinsAt L D).Z →* ℂˣ} {NK : Ideal (𝓞 K)}
  {SK : Finset (HeightOneSpectrum (𝓞 K))} {tys : ArchTypeFamily L} {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)}

omit [NumberField K] in
private theorem continuous_of_mem_E (hc : Ctx L D ξ tys V) {y : AdelicGL2 (𝓞 L) L → ℂ} (hy : y ∈ Ecut K L D NK tys V) :
    Continuous y :=
  continuous_of_mem_cuspKFiniteSubmodule L _ _ (hc.hV.1.le (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).1)

private theorem rightConv_mem_E (hc : Ctx L D ξ tys V) {g : AdelicGL2 (𝓞 L) L → ℂ} (hg : tierFn K L NK SK tys g)
    {y : AdelicGL2 (𝓞 L) L → ℂ} (hy : y ∈ Ecut K L D NK tys V) : rightConv L y g ∈ Ecut K L D NK tys V := by
  obtain ⟨hy', hyt⟩ := Submodule.mem_inf.mp hy
  obtain ⟨hyV, -⟩ := Submodule.mem_inf.mp hy'
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact hc.hV.1.rightConv_mem g tys (tier_isFactorizableTestFn K L hg) hg.2 y hyV
  · exact rightConv_mem_levelInvariantSubmodule L (pinsAt L D) _ (fun k hk z => (hg.1.1 k hk z).1) y
  · exact hc.hTYS g (tier_isFactorizableTestFn K L hg) hg.2.1 y (continuous_of_mem_E hc hy)

private def opOf (hc : Ctx L D ξ tys V) {g : AdelicGL2 (𝓞 L) L → ℂ} (hg : tierFn K L NK SK tys g) :
    Module.End ℂ (Ecut K L D NK tys V) where
  toFun y := ⟨rightConv L y.1 g, rightConv_mem_E hc hg y.2⟩
  map_add' y z := by
    apply Subtype.ext
    obtain ⟨hgc, hgs⟩ :=
      AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L g (tier_isFactorizableTestFn K L hg)
    show rightConv L (y.1 + z.1) g = rightConv L y.1 g + rightConv L z.1 g
    exact rightConv_add_left L (continuous_of_mem_E hc y.2) (continuous_of_mem_E hc z.2) hgc hgs
  map_smul' a y := by
    apply Subtype.ext
    show rightConv L (a • y.1) g = a • rightConv L y.1 g
    exact convOp_smul L g a y.1

private theorem opOf_apply_coe (hc : Ctx L D ξ tys V) {g : AdelicGL2 (𝓞 L) L → ℂ} (hg : tierFn K L NK SK tys g)
    (y : Ecut K L D NK tys V) : (opOf hc hg y).1 = rightConv L y.1 g :=
  rfl

private def opAlg (hc : Ctx L D ξ tys V) (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) :
    Submodule ℂ (Module.End ℂ (Ecut K L D NK tys V)) :=
  Submodule.span ℂ (Set.range fun gt : {g : AdelicGL2 (𝓞 L) L → ℂ // tierFn K L NK SK tys g} => opOf hc gt.2)

private theorem opOf_mem_alg (hc : Ctx L D ξ tys V) {g : AdelicGL2 (𝓞 L) L → ℂ} (hg : tierFn K L NK SK tys g) :
    opOf hc hg ∈ opAlg hc NK SK :=
  Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩

private theorem opOf_mul_opOf_mem (hc : Ctx L D ξ tys V) {φ ψ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : tierFn K L NK SK tys φ)
    (hψ : tierFn K L NK SK tys ψ) : opOf hc hψ * opOf hc hφ ∈ opAlg hc NK SK := by
  obtain ⟨hφc, hφs⟩ :=
    AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ (tier_isFactorizableTestFn K L hφ)
  obtain ⟨hψc, hψs⟩ :=
    AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L ψ (tier_isFactorizableTestFn K L hψ)
  let χ : AdelicGL2 (𝓞 L) L → ℂ := fun g => ∫ y, ψ y * φ (y⁻¹ * g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
  obtain ⟨-, hcomp, -, -, hlt, hrt, hunit⟩ :=
    AutomorphicForm.convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul K L (levU K L NK) SK φ ψ
      ⟨tier_isFactorizableTestFn K L hφ, hφc, hφs⟩ ⟨tier_isFactorizableTestFn K L hψ, hψc, hψs⟩ χ rfl
  have hχ : tierFn K L NK SK tys χ := ⟨hunit hψ.1 hφ.1, hlt tys hψ.2.1, hrt tys hφ.2.2⟩
  have hmul : opOf hc hψ * opOf hc hφ = opOf hc hχ := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    show convOp L ψ (convOp L φ y.1) = convOp L χ y.1
    exact hcomp y.1 (continuous_of_mem_E hc y.2)
  rw [hmul]
  exact opOf_mem_alg hc hχ

private theorem aux_mul_mem_alg (hc : Ctx L D ξ tys V) {s : Module.End ℂ (Ecut K L D NK tys V)}
    (hs : s ∈ opAlg hc NK SK)
    {t : Module.End ℂ (Ecut K L D NK tys V)} (ht : t ∈ opAlg hc NK SK) : t * s ∈ opAlg hc NK SK := by
  have key : ∀ {g : AdelicGL2 (𝓞 L) L → ℂ} (hg : tierFn K L NK SK tys g),
      ∀ s ∈ opAlg hc NK SK, opOf hc hg * s ∈ opAlg hc NK SK := by
    intro g hg s hs
    refine Submodule.span_induction (p := fun s _ => opOf hc hg * s ∈ opAlg hc NK SK) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨⟨φ, hφ⟩, rfl⟩
      exact opOf_mul_opOf_mem hc hφ hg
    · show opOf hc hg * (0 : Module.End ℂ (Ecut K L D NK tys V)) ∈ opAlg hc NK SK
      rw [mul_zero]
      exact (opAlg hc NK SK).zero_mem
    · intro x y _ _ hx hy
      rw [mul_add]
      exact (opAlg hc NK SK).add_mem hx hy
    · intro a x _ hx
      rw [mul_smul_comm]
      exact (opAlg hc NK SK).smul_mem a hx
  refine Submodule.span_induction (p := fun t _ => t * s ∈ opAlg hc NK SK) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact key hg s hs
  · show (0 : Module.End ℂ (Ecut K L D NK tys V)) * s ∈ opAlg hc NK SK
    rw [zero_mul]
    exact (opAlg hc NK SK).zero_mem
  · intro x y _ _ hx hy
    rw [add_mul]
    exact (opAlg hc NK SK).add_mem hx hy
  · intro a x _ hx
    rw [smul_mul_assoc]
    exact (opAlg hc NK SK).smul_mem a hx

private theorem aux_exists_mem_alg_apply_eq (hc : Ctx L D ξ tys V)
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK) [FiniteDimensional ℂ (Ecut K L D NK tys V)]
    (y : Ecut K L D NK tys V) : ∃ t ∈ opAlg hc NK SK, t y = y := by
  obtain ⟨hy', hyt⟩ := Submodule.mem_inf.mp y.2
  obtain ⟨-, hylev⟩ := Submodule.mem_inf.mp hy'
  have hlev : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levU K L NK, y.1 (g * k) = y.1 g := hylev
  obtain ⟨φ, hφ, htend⟩ :=
    AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule K L NK SK hNS tys
      y.1 (continuous_of_mem_E hc y.2) hlev hyt
  let S : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) :=
    ((opAlg hc NK SK).map (LinearMap.applyₗ y)).map (Ecut K L D NK tys V).subtype
  have hS : IsClosed (S : Set (AdelicGL2 (𝓞 L) L → ℂ)) := S.closed_of_finiteDimensional
  have hmem : ∀ n, rightConv L y.1 (φ n) ∈ S := fun n =>
    Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (opOf_mem_alg hc (hφ n)))
  have hlim : Filter.Tendsto (fun n => rightConv L y.1 (φ n)) Filter.atTop (nhds y.1) := tendsto_pi_nhds.mpr htend
  have hyS : y.1 ∈ S := hS.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hyS
  obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hz
  exact ⟨t, ht, Subtype.ext hzy⟩

end Operators

private theorem aux_finiteDimensional_E (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (pinsAt L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)).Z →* ℂˣ)
    {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥) (tys : ArchTypeFamily L) {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)}
    (hV : IsCuspConstituent L (pinsAt L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)) ξ V) :
    FiniteDimensional ℂ (Ecut K L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂) NK tys V) :=
  AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent L c u d₁ d₂
    T hd hcov ξ _ (map_algebraMap_ne_bot K L hNK) tys V hV

end TierCompression

end

section GlobalUnit

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

private theorem aux_exists_mem_forall_mem_apply_eq_self (A : Submodule 𝕜 (Module.End 𝕜 E))
    (hmul : ∀ s ∈ A, ∀ t ∈ A, t * s ∈ A) (hloc : ∀ y : E, ∃ t ∈ A, t y = y) :
    ∀ (n : ℕ) (W : Submodule 𝕜 E), Module.finrank 𝕜 W = n → ∃ t ∈ A, ∀ y ∈ W, t y = y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hW
    by_cases hbot : W = ⊥
    · refine ⟨0, A.zero_mem, fun y hy => ?_⟩
      have hy0 : y = 0 := (Submodule.mem_bot 𝕜).mp (hbot ▸ hy)
      rw [hy0, LinearMap.zero_apply]
    · obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨t₁, ht₁, ht₁w⟩ := hloc w
      have hrank := LinearMap.finrank_range_add_finrank_ker ((1 - t₁ : Module.End 𝕜 E).domRestrict W)
      rw [LinearMap.range_domRestrict] at hrank
      have hker : 0 < Module.finrank 𝕜 (LinearMap.ker ((1 - t₁ : Module.End 𝕜 E).domRestrict W)) := by
        rw [Module.finrank_pos_iff_exists_ne_zero]
        refine ⟨⟨⟨w, hwW⟩, ?_⟩, ?_⟩
        · rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.sub_apply, Module.End.one_apply, ht₁w,
            sub_self]
        · intro h
          apply hw0
          simpa using congrArg (fun v : LinearMap.ker ((1 - t₁ : Module.End 𝕜 E).domRestrict W) => ((v : W) : E)) h
      have hlt : Module.finrank 𝕜 (W.map (1 - t₁ : Module.End 𝕜 E)) < n := by omega
      obtain ⟨t₂, ht₂, ht₂W₁⟩ := ih _ hlt (W.map (1 - t₁ : Module.End 𝕜 E)) rfl
      refine ⟨t₁ + t₂ - t₂ * t₁, A.sub_mem (A.add_mem ht₁ ht₂) (hmul t₁ ht₁ t₂ ht₂), fun y hy => ?_⟩
      have hz := ht₂W₁ _ (Submodule.mem_map_of_mem (f := (1 - t₁ : Module.End 𝕜 E)) hy)
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub] at hz
      rw [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, add_sub_assoc, hz]
      abel

private theorem aux_exists_mem_forall_apply_eq_self (A : Submodule 𝕜 (Module.End 𝕜 E))
    (hmul : ∀ s ∈ A, ∀ t ∈ A, t * s ∈ A) (hloc : ∀ y : E, ∃ t ∈ A, t y = y) :
    ∃ t ∈ A, ∀ y : E, t y = y := by
  obtain ⟨t, ht, hty⟩ := aux_exists_mem_forall_mem_apply_eq_self A hmul hloc _ ⊤ rfl
  exact ⟨t, ht, fun y => hty y Submodule.mem_top⟩

end GlobalUnit

open NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent

private theorem aux_isCuspSubrep_inf (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (h₁ : IsCuspSubrep F pins ξ V₁) (h₂ : IsCuspSubrep F pins ξ V₂) :
    IsCuspSubrep F pins ξ (V₁ ⊓ V₂) where
  le := inf_le_left.trans h₁.le
  rightTranslate_fin_mem g hg φ hφ :=
    Submodule.mem_inf.mpr
      ⟨h₁.rightTranslate_fin_mem g hg φ (Submodule.mem_inf.mp hφ).1,
        h₂.rightTranslate_fin_mem g hg φ (Submodule.mem_inf.mp hφ).2⟩
  rightTranslate_arch_mem w k φ hφ :=
    Submodule.mem_inf.mpr
      ⟨h₁.rightTranslate_arch_mem w k φ (Submodule.mem_inf.mp hφ).1,
        h₂.rightTranslate_arch_mem w k φ (Submodule.mem_inf.mp hφ).2⟩
  rightConv_mem f tys hf hbf φ hφ :=
    Submodule.mem_inf.mpr
      ⟨h₁.rightConv_mem f tys hf hbf φ (Submodule.mem_inf.mp hφ).1,
        h₂.rightConv_mem f tys hf hbf φ (Submodule.mem_inf.mp hφ).2⟩

private theorem aux_eq_of_isCuspConstituent_of_inf_ne_bot (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ξ : pins.Z →* ℂˣ) {V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (h₁ : IsCuspConstituent F pins ξ V₁) (h₂ : IsCuspConstituent F pins ξ V₂) (hne : V₁ ⊓ V₂ ≠ ⊥) :
    V₁ = V₂ := by
  obtain ⟨h₁s, -, h₁min⟩ := h₁
  obtain ⟨h₂s, -, h₂min⟩ := h₂
  have hW : IsCuspSubrep F pins ξ (V₁ ⊓ V₂) := aux_isCuspSubrep_inf F pins ξ h₁s h₂s
  rcases h₁min (V₁ ⊓ V₂) hW inf_le_left with hbot | hV₁
  · exact absurd hbot hne
  rcases h₂min (V₁ ⊓ V₂) hW inf_le_right with hbot | hV₂
  · exact absurd hbot hne
  exact hV₁.symm.trans hV₂

private theorem aux_eq_of_isCuspConstituent_of_mem_of_mem (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ξ : pins.Z →* ℂˣ) {V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (h₁ : IsCuspConstituent F pins ξ V₁) (h₂ : IsCuspConstituent F pins ξ V₂)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ₁ : φ ∈ V₁) (hφ₂ : φ ∈ V₂) (hφ0 : φ ≠ 0) :
    V₁ = V₂ :=
  aux_eq_of_isCuspConstituent_of_inf_ne_bot F pins ξ h₁ h₂
    ((Submodule.ne_bot_iff (V₁ ⊓ V₂)).mpr ⟨φ, Submodule.mem_inf.mpr ⟨hφ₁, hφ₂⟩, hφ0⟩)

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent

section JoinOfFamilies

variable (F : Type) [Field F]

private def aux_archTypeFamilyJoin (t₁ t₂ : ArchTypeFamily F) : ArchTypeFamily F where
  card := fun w => t₁.card w + t₂.card w
  rep := fun w => Fin.append (t₁.rep w) (t₂.rep w)

private theorem aux_isContainedIn_join_left (t₁ t₂ : ArchTypeFamily F) :
    ArchTypeFamily.IsContainedIn F t₁ (aux_archTypeFamilyJoin F t₁ t₂) :=
  fun w i => ⟨Fin.castAdd (t₂.card w) i, Fin.append_left (t₁.rep w) (t₂.rep w) i⟩

private theorem aux_isContainedIn_join_right (t₁ t₂ : ArchTypeFamily F) :
    ArchTypeFamily.IsContainedIn F t₂ (aux_archTypeFamilyJoin F t₁ t₂) :=
  fun w i => ⟨Fin.natAdd (t₁.card w) i, Fin.append_right (t₁.rep w) (t₂.rep w) i⟩

private theorem aux_map_algebraMap_self (N : Ideal (𝓞 F)) :
    Ideal.map (@algebraMap (𝓞 F) (𝓞 F) _ _ (NumberField.inst_ringOfIntegersAlgebra F F)) N = N :=
  Ideal.map_id N

end JoinOfFamilies

noncomputable section

variable (F : Type) [Field F] [NumberField F]

private theorem aux_exists_archTypeFamily_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F)
    (ξ : pins.Z →* ℂˣ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) :
    ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys := by
  refine Submodule.span_induction
    (p := fun φ _ => ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨-, -, tys, htys⟩
    exact ⟨tys, htys⟩
  · exact ⟨⟨fun _ => 0, fun _ i => Fin.elim0 i⟩, (archCutSubmodule F _).zero_mem⟩
  · rintro u v _ _ ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    exact ⟨aux_archTypeFamilyJoin F t₁ t₂,
      (archCutSubmodule F _).add_mem (archCutSubmodule_mono F (aux_isContainedIn_join_left F t₁ t₂) h₁)
        (archCutSubmodule_mono F (aux_isContainedIn_join_right F t₁ t₂) h₂)⟩
  · rintro c u _ ⟨t, ht⟩
    exact ⟨t, (archCutSubmodule F t).smul_mem c ht⟩

private theorem aux_exists_finset_forall_dvd (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    ∃ SK : Finset (HeightOneSpectrum (𝓞 F)), ∀ p : HeightOneSpectrum (𝓞 F), p.asIdeal ∣ N → p ∈ SK :=
  ⟨(Ideal.finite_factors (I := N) (by simpa using hN)).toFinset,
    fun _ hp => (Ideal.finite_factors (I := N) (by simpa using hN)).mem_toFinset.mpr hp⟩

private abbrev pinsAt (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

private theorem aux_exists_testFn_rightConv_ne_zero (D : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pinsAt F D).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφK : φ ∈ cuspKFiniteSubmodule F (pinsAt F D) ξ)
    (h : IsIsotypicCuspFormAt F (pinsAt F D) ξ N S Ψ φ) (hφ0 : φ ≠ 0) :
    ∃ (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ),
      IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
        (∀ k ∈ (pinsAt F D).U N, ∀ y, f (k * y) = f y) ∧ rightConv F φ f ≠ 0 := by
  obtain ⟨tys, htys⟩ :=
    aux_exists_archTypeFamily_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule F (pinsAt F D) ξ hφK
  obtain ⟨SK, hSK⟩ := aux_exists_finset_forall_dvd F N hN
  obtain ⟨fs, hfs, htend⟩ :=
    exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule F F N SK hSK tys φ
      h.continuous
      (by
        intro g k hk
        rw [aux_map_algebraMap_self F N] at hk
        exact h.level_invariant g k hk)
      htys
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hφ0
  obtain ⟨n, hn⟩ := ((htend g₀).eventually_ne hg₀).exists
  refine ⟨tys, fs n, ?_, (hfs n).isArchBiFinite, ?_, fun hzero => hn (congrFun hzero g₀)⟩
  · obtain ⟨φa, φf, φS, h₁, h₂, -, -, -, h₆⟩ := (hfs n).1.2
    exact ⟨φa, φf, h₁, h₂, h₆⟩
  · intro k hk y
    have hk' : k ∈ levelOne (𝓞 F) F
        (Ideal.map (@algebraMap (𝓞 F) (𝓞 F) _ _ (NumberField.inst_ringOfIntegersAlgebra F F)) N) ⊓
          finiteAdelicGL2Subgroup F := by
      rw [aux_map_algebraMap_self F N]
      exact hk
    exact ((hfs n).1.1 k hk' y).1

end

section

noncomputable section

namespace ConvEng

open AutomorphicForm

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem exists_out_mul_eq (ι : H →* G) (x : G) :
    ∃ k : H, (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range x
  obtain ⟨k, hk⟩ := h.2
  exact ⟨k⁻¹, by rw [map_inv, hh, ← hk, mul_inv_cancel_right]⟩

private noncomputable def cosetCoord (ι : H →* G) (x : G) : H :=
  (exists_out_mul_eq ι x).choose

private theorem out_mul_cosetCoord (ι : H →* G) (x : G) :
    (QuotientGroup.mk x : G ⧸ ι.range).out * ι (cosetCoord ι x) = x :=
  (exists_out_mul_eq ι x).choose_spec

private theorem cosetCoord_unique {ι : H →* G} (hι : Function.Injective ι) {x : G} {k : H}
    (hk : (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x) : k = cosetCoord ι x :=
  hι (mul_left_cancel (hk.trans (out_mul_cosetCoord ι x).symm))

private theorem cosetCoord_mul {ι : H →* G} (hι : Function.Injective ι) (x : G) (k : H) :
    cosetCoord ι (x * ι k) = cosetCoord ι x * k := by
  symm
  apply cosetCoord_unique hι
  have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  rw [hmk, map_mul, ← mul_assoc, out_mul_cosetCoord]

private theorem mem_typeSubmodule_of_isRightEquivariantOn {ι : H →* G} (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ (k : H), ∀ v ∈ P, ρ k v ∈ P)
    (S : P →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : P) (x : G), S ⟨ρ k v, hP k v v.2⟩ x = S v (x * ι k)) (v : P) :
    S v ∈ AutomorphicForm.typeSubmodule ι ρ := by
  classical

  let ℓ : G ⧸ ι.range → (P →ₗ[ℂ] ℂ) := fun c =>
    { toFun := fun p => S p c.out
      map_add' := fun p q => by rw [map_add]; rfl
      map_smul' := fun a p => by rw [map_smul]; rfl }
  have hext : ∀ c, ∃ g : W →ₗ[ℂ] ℂ, g.comp P.subtype = ℓ c := fun c => LinearMap.exists_extend (ℓ c)
  let ℓ' : G ⧸ ι.range → (W →ₗ[ℂ] ℂ) := fun c => (hext c).choose
  have hℓ' : ∀ c (p : P), ℓ' c (p : W) = S p c.out := fun c p => by
    have := LinearMap.congr_fun (hext c).choose_spec p
    simpa [ℓ] using this

  let T : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) w)
      map_add' := fun w₁ w₂ => funext fun x => by simp only [map_add, Pi.add_apply]
      map_smul' := fun a w => funext fun x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hT : AutomorphicForm.IsRightEquivariant ι ρ T := by
    intro k w x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (ρ k w)) =
      ℓ' (QuotientGroup.mk (x * ι k)) (ρ (cosetCoord ι (x * ι k)) w)
    have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
      rw [QuotientGroup.eq]
      exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
    rw [hmk, cosetCoord_mul hι, map_mul]
    rfl
  have hTS : T (v : W) = S v := by
    funext x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (v : W)) = S v x
    have hmem : ρ (cosetCoord ι x) (v : W) ∈ P := hP _ _ v.2
    have h1 := hℓ' (QuotientGroup.mk x) ⟨_, hmem⟩
    simp only at h1
    rw [h1, hS (cosetCoord ι x) v, out_mul_cosetCoord]
  rw [← hTS]
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hT _

end TypePiece

section PiRep

variable {H : Type*} [Group H]
variable {A : Type*} {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]

private def piRep (ρ : ∀ a, Representation ℂ H (W a)) : Representation ℂ H (∀ a, W a) where
  toFun k := LinearMap.pi fun a => (ρ a k).comp (LinearMap.proj a)
  map_one' := by
    ext v a
    simp
  map_mul' k₁ k₂ := by
    ext v a
    simp

private theorem piRep_apply (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    piRep ρ k v a = ρ a k (v a) :=
  rfl

private theorem piRep_single [DecidableEq A] (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (a : A)
    (v : W a) : piRep ρ k (Pi.single a v) = Pi.single a (ρ a k v) := by
  funext b
  rw [piRep_apply]
  by_cases hb : b = a
  · subst hb
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hb, map_zero]

end PiRep

section Transport

variable {H G : Type*} [Group H] [Group G]

private theorem typeSubmodule_piRep_le {A : Type*} [Fintype A] [DecidableEq A] {W : A → Type*}
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] (ι : H →* G)
    (ρ : ∀ a, Representation ℂ H (W a)) :
    typeSubmodule ι (piRep ρ) ≤ ⨆ a, typeSubmodule ι (ρ a) := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, v, rfl⟩
  show T v ∈ ⨆ a, typeSubmodule ι (ρ a)
  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ?_
  have hTa : IsRightEquivariant ι (ρ a) (T.comp (LinearMap.single ℂ W a)) := by
    intro k w x
    show T (Pi.single a (ρ a k w)) x = T (Pi.single a w) (x * ι k)
    rw [← piRep_single]
    exact hT k (Pi.single a w) x
  exact mem_typeSubmodule_of_isRightEquivariant hTa (v a)

private theorem mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi {A : Type*} [Fintype A] [DecidableEq A]
    {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] {ι : H →* G}
    (hι : Function.Injective ι) (ρ : ∀ a, Representation ℂ H (W a)) (Q : Submodule ℂ (∀ a, W a))
    (hQ : ∀ (k : H), ∀ v ∈ Q, piRep ρ k v ∈ Q) (S : Q →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : Q) (x : G), S ⟨piRep ρ k v, hQ k v v.2⟩ x = S v (x * ι k)) (v : Q) :
    S v ∈ ⨆ a, typeSubmodule ι (ρ a) :=
  typeSubmodule_piRep_le ι ρ (mem_typeSubmodule_of_isRightEquivariantOn hι (piRep ρ) Q hQ S hS v)

private theorem exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) {θ : G → ℂ} (hθ : θ ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ θ ∈ LinearMap.range Φ := by
  classical
  have h1 : θ ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hθ
  obtain ⟨t, ht, hθt⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hgen : ∀ f : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (f : G → ℂ) ∈ LinearMap.range T := fun f => by
    have hf := ht f.2
    rw [Set.mem_iUnion] at hf
    obtain ⟨j, T, hT, hfT⟩ := hf
    exact ⟨j, T, hT, hfT⟩
  choose i T hT hfT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · refine (Submodule.span_le.mpr ?_) hθt
    intro f hf
    obtain ⟨v, hv⟩ := hfT ⟨f, hf⟩
    refine ⟨Pi.single (⟨f, hf⟩ : t) v, ?_⟩
    rw [hΦ, Finset.sum_eq_single (⟨f, hf⟩ : t)]
    · rw [Pi.single_eq_same]
      exact hv
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem mem_iSup_typeSubmodule_of_intertwines {G' : Type*} [Group G'] {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G) {ι' : H →* G'}
    (hι' : Function.Injective ι') (ρ : ∀ j, Representation ℂ H (W j)) (P₀ : Submodule ℂ (G → ℂ))
    (hP₀ : ∀ (k : H), ∀ θ ∈ P₀, (fun x => θ (x * ι k)) ∈ P₀) (A : P₀ →ₗ[ℂ] (G' → ℂ))
    (hA : ∀ (k : H) (θ : P₀) (y : G'), A ⟨fun x => (θ : G → ℂ) (x * ι k), hP₀ k θ θ.2⟩ y =
      A θ (y * ι' k))
    (θ : P₀) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    A θ ∈ ⨆ j, typeSubmodule ι' (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, v, hv⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule ι ρ hθ
  have hQ : ∀ (k : H), ∀ w ∈ P₀.comap Φ, piRep (fun a => ρ (i a)) k w ∈ P₀.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι k) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hP₀ k _ hw
  let ΦQ : P₀.comap Φ →ₗ[ℂ] P₀ :=
    LinearMap.codRestrict P₀ (Φ.comp (P₀.comap Φ).subtype) fun w => w.2
  have hΦQ : ∀ w : P₀.comap Φ, ((ΦQ w : P₀) : G → ℂ) = Φ (w : ∀ a : t, W (i a)) := fun _ => rfl
  let S : P₀.comap Φ →ₗ[ℂ] (G' → ℂ) := A.comp ΦQ
  have hS : ∀ (k : H) (w : P₀.comap Φ) (y : G'),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ y = S w (y * ι' k) := by
    intro k w y
    have h1 : ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ =
        ⟨fun x => ((ΦQ w : P₀) : G → ℂ) (x * ι k), hP₀ k _ (ΦQ w).2⟩ := by
      apply Subtype.ext
      funext x
      exact hΦ k w x
    show A (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩) y = A (ΦQ w) (y * ι' k)
    rw [h1]
    exact hA k (ΦQ w) y
  have hv' : v ∈ P₀.comap Φ := by
    rw [Submodule.mem_comap, hv]
    exact θ.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hι' (fun a => ρ (i a)) (P₀.comap Φ)
    hQ S hS ⟨v, hv'⟩
  have hSv : S ⟨v, hv'⟩ = A θ := by
    show A (ΦQ ⟨v, hv'⟩) = A θ
    congr 1
    exact Subtype.ext hv
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule ι' (ρ j)) (i a)) hmem

end Transport

section ConvTransport

open MeasureTheory

variable {H G : Type*} [Group H] [Group G]

private theorem conv_integrand_eq (u θ : G → ℂ) (k y x : G) :
    u (y * k * (k⁻¹ * x)) * θ (k⁻¹ * x)⁻¹ = u (y * x) * θ (x⁻¹ * k) := by
  rw [mul_assoc, mul_inv_cancel_left, mul_inv_rev, inv_inv]

variable [MeasurableSpace G] (μ : Measure G) (u : G → ℂ)

private def convDomain : Submodule ℂ (G → ℂ) where
  carrier := {θ | ∀ y : G, Integrable (fun x => u (y * x) * θ x⁻¹) μ}
  zero_mem' := by
    intro y
    simp
  add_mem' := by
    intro θ₁ θ₂ h₁ h₂ y
    have e : (fun x => u (y * x) * (θ₁ + θ₂) x⁻¹) =
        fun x => u (y * x) * θ₁ x⁻¹ + u (y * x) * θ₂ x⁻¹ :=
      funext fun x => by simp only [Pi.add_apply, mul_add]
    rw [e]
    exact (h₁ y).add (h₂ y)
  smul_mem' := by
    intro c θ h y
    have e : (fun x => u (y * x) * (c • θ) x⁻¹) = fun x => c * (u (y * x) * θ x⁻¹) :=
      funext fun x => by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [e]
    exact (h y).const_mul c

private theorem mem_convDomain_iff (θ : G → ℂ) :
    θ ∈ convDomain μ u ↔ ∀ y : G, Integrable (fun x => u (y * x) * θ x⁻¹) μ :=
  Iff.rfl

private def convOpOn : convDomain μ u →ₗ[ℂ] (G → ℂ) where
  toFun θ := fun y => ∫ x, u (y * x) * (θ : G → ℂ) x⁻¹ ∂μ
  map_add' θ₁ θ₂ := funext fun y => by
    have h₁ := (mem_convDomain_iff μ u _).mp θ₁.2 y
    have h₂ := (mem_convDomain_iff μ u _).mp θ₂.2 y
    show (∫ x, u (y * x) * ((θ₁ : G → ℂ) + (θ₂ : G → ℂ)) x⁻¹ ∂μ) =
      (∫ x, u (y * x) * (θ₁ : G → ℂ) x⁻¹ ∂μ) + ∫ x, u (y * x) * (θ₂ : G → ℂ) x⁻¹ ∂μ
    rw [← integral_add h₁ h₂]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply, mul_add])
  map_smul' c θ := funext fun y => by
    show (∫ x, u (y * x) * (c • (θ : G → ℂ)) x⁻¹ ∂μ) = c * ∫ x, u (y * x) * (θ : G → ℂ) x⁻¹ ∂μ
    have e : (∫ x, u (y * x) * (c • (θ : G → ℂ)) x⁻¹ ∂μ) = ∫ x, c * (u (y * x) * (θ : G → ℂ) x⁻¹) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm])
    rw [e]
    exact integral_const_mul c _

private theorem convOpOn_apply (θ : convDomain μ u) (y : G) :
    convOpOn μ u θ y = ∫ x, u (y * x) * (θ : G → ℂ) x⁻¹ ∂μ :=
  rfl

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

private theorem comp_mul_mem_convDomain {θ : G → ℂ} (hθ : θ ∈ convDomain μ u) (k : G) :
    (fun x => θ (x * k)) ∈ convDomain μ u := by
  rw [mem_convDomain_iff] at hθ ⊢
  intro y
  refine ((hθ (y * k)).comp_mul_left k⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
  exact conv_integrand_eq u θ k y x

private theorem convOpOn_comp_mul (θ : convDomain μ u) (k : G)
    (hk : (fun x => (θ : G → ℂ) (x * k)) ∈ convDomain μ u) (y : G) :
    convOpOn μ u ⟨fun x => (θ : G → ℂ) (x * k), hk⟩ y = convOpOn μ u θ (y * k) := by
  simp only [convOpOn_apply]
  rw [← integral_mul_left_eq_self (fun x => u (y * k * x) * (θ : G → ℂ) x⁻¹) k⁻¹]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (conv_integrand_eq u (θ : G → ℂ) k y x).symm)

private theorem convOpOn_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] {ι : H →* G} (hι : Function.Injective ι) (ρ : ∀ j, Representation ℂ H (W j))
    (θ : convDomain μ u) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    convOpOn μ u θ ∈ ⨆ j, typeSubmodule ι (ρ j) :=
  mem_iSup_typeSubmodule_of_intertwines ι hι ρ (convDomain μ u)
    (fun k _ hθ' => comp_mul_mem_convDomain μ u hθ' (ι k)) (convOpOn μ u)
    (fun k θ' y => convOpOn_comp_mul μ u θ' (ι k) _ y) θ hθ

end ConvTransport

end ConvEng

end

end

section

open NumberField NumberField.AdelicLevel AutomorphicForm

namespace RowIsos

variable (F : Type) [Field F]

private theorem archComponent_archRowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (archRowIsometryInclAt₀ F w k) = (k : GL (Fin 2) w.Completion) :=
  archComponent_archGLIncl_self F w (k : GL (Fin 2) w.Completion)

private theorem archRowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (archRowIsometryInclAt₀ F w) := fun a b h => by
  have ha := archComponent_archRowIsometryInclAt₀ F w a
  have hb := archComponent_archRowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

variable [NumberField F]

private theorem archComponent_glArch_rowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w k))
      = (k : GL (Fin 2) w.Completion) := by
  rw [glArch_rowIsometryInclAt₀]
  exact archComponent_archRowIsometryInclAt₀ F w k

private theorem rowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := fun a b h => by
  have ha := archComponent_glArch_rowIsometryInclAt₀ F w a
  have hb := archComponent_glArch_rowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

private theorem forall_rowIsometryInclAt₀_injective :
    ∀ w : InfinitePlace F, Function.Injective (rowIsometryInclAt₀ F w) :=
  rowIsometryInclAt₀_injective F

end RowIsos

end

section

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

private theorem aux_rightConv_mem_archCutSubmodule {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hfact : IsFactorizableTestFn F f) (hleft : (fun x => f x⁻¹) ∈ archCutSubmodule F tys)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : Continuous u) : rightConv F u f ∈ archCutSubmodule F tys := by
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hfact
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hdom : (fun x => f x⁻¹) ∈ ConvEng.convDomain (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) u := by
    rw [ConvEng.mem_convDomain_iff]
    intro y
    simp only [inv_inv]
    exact ((hu.comp (continuous_const.mul continuous_id)).mul hfc).integrable_of_hasCompactSupport
      hfs.mul_left
  have hconv : ConvEng.convOpOn (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) u ⟨fun x => f x⁻¹, hdom⟩
      = rightConv F u f := by
    funext y
    rw [ConvEng.convOpOn_apply]
    show (∫ x, u (y * x) * (fun x => f x⁻¹) x⁻¹ ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
      ∫ x, u (y * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    simp only [inv_inv]
  rw [mem_archCutSubmodule_iff]
  intro w
  rw [← hconv]
  exact ConvEng.convOpOn_mem_iSup_typeSubmodule _ u (RowIsos.forall_rowIsometryInclAt₀_injective F w)
    (fun i => (tys.rep w i).ρ) _ ((mem_archCutSubmodule_iff F tys _).mp hleft w)

private theorem aux_continuous_and_rightConv_finset_sum_smul {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (u : ι → AdelicGL2 (𝓞 F) F → ℂ) (hu : ∀ i, Continuous (u i)) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (∑ i ∈ s, c i • u i) ∧
      rightConv F (∑ i ∈ s, c i • u i) f = ∑ i ∈ s, c i • rightConv F (u i) f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact ⟨continuous_zero, rightConv_zero_left F f⟩
  · intro a t hat ih
    obtain ⟨ihc, ihe⟩ := ih
    simp only [Finset.sum_insert hat]
    have hca : Continuous (c a • u a) := (hu a).const_smul (c a)
    refine ⟨hca.add ihc, ?_⟩
    rw [rightConv_add_left F hca ihc hf hfc, ihe]
    congr 1
    exact convOp_smul F f (c a) (u a)

private theorem aux_rightConv_finset_sum_smul {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (u : ι → AdelicGL2 (𝓞 F) F → ℂ) (hu : ∀ i, Continuous (u i)) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    rightConv F (∑ i ∈ s, c i • u i) f = ∑ i ∈ s, c i • rightConv F (u i) f :=
  (aux_continuous_and_rightConv_finset_sum_smul F s c u hu hf hfc).2

end

open TierCompression in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (hNK : NK ≠ ⊥) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent L
      (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ V) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
      ∀ y ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys,
        ∑ φ ∈ s, a φ • convOp L φ y = y := by
  classical
  have hc : Ctx L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂) ξ tys V :=
    ⟨hV, fun g hg hleft w hw => aux_rightConv_mem_archCutSubmodule L hg hleft hw⟩
  haveI : FiniteDimensional ℂ (Ecut K L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂) NK tys V) :=
    aux_finiteDimensional_E K L c u d₁ d₂ T hd hcov ξ hNK tys hV
  obtain ⟨t, ht, hty⟩ := aux_exists_mem_forall_apply_eq_self (opAlg hc NK SK)
    (fun _ hs _ ht => aux_mul_mem_alg hc hs ht) (fun y => aux_exists_mem_alg_apply_eq hc hNS y)
  unfold opAlg at ht
  obtain ⟨n, f, gs, hsum⟩ := Submodule.mem_span_set'.mp ht
  have hgs : ∀ i, ∃ gt : {g : AdelicGL2 (𝓞 L) L → ℂ // tierFn K L NK SK tys g}, opOf hc gt.2 = (gs i).1 :=
    fun i => (gs i).2
  choose gt hgt using hgs
  refine ⟨Finset.univ.image fun i => (gt i).1,
    fun g => ∑ i ∈ Finset.univ.filter (fun i => (gt i).1 = g), f i, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hgc, hgcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L _
      (tier_isFactorizableTestFn K L (gt i).2)
    exact ⟨(gt i).2, hgc, hgcs⟩
  · intro y hy
    have hyE : y ∈ Ecut K L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂) NK tys V := hy
    have h1 : (t ⟨y, hyE⟩).1 = y := congrArg Subtype.val (hty ⟨y, hyE⟩)
    rw [← hsum] at h1
    simp only [← hgt, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
      opOf_apply_coe] at h1
    rw [Finset.sum_image' (fun i => f i • convOp L (gt i).1 y) (fun i _ => ?_)]
    · exact h1
    · rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun j hj => by beta_reduce; rw [(Finset.mem_filter.mp hj).2]

end S_AutomorphicForm_exists_finset_sum_convOp_eq_self_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_sum_convOp_eq_self_of_isCuspConstituent (solution)
