-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d213a9e8-3f15-5c01-8dd2-9d1f2f7cca4b

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsIsotypicCuspFormAt productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsSmoothCuspAutomorphicFnAt SmoothCusp.heckeCosetSum HeckeEigensystem CuspidalSpectrum.isClosedCuspSubrep_orthogonal CuspidalSpectrum.exists_isLift_rightTranslate CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule"
namespace Meets
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

private theorem proj_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : Submodule ℂ E) (S : E →L[ℂ] E)
    (hSM : M.map (S : E →ₗ[ℂ] E) ≤ M) (hSM' : Mᗮ.map (S : E →ₗ[ℂ] E) ≤ Mᗮ)
    {x y : E} (hy : y ∈ M) (hxy : x - y ∈ Mᗮ) (a : ℂ) (hx : S x = a • x) : S y = a • y := by

  have h1 : S y - a • y ∈ M := M.sub_mem (hSM ⟨y, hy, rfl⟩) (M.smul_mem a hy)
  have h2 : S y - a • y ∈ Mᗮ := by
    have : S y - a • y = a • (x - y) - S (x - y) := by
      rw [map_sub, hx, smul_sub]; abel
    rw [this]
    exact Mᗮ.sub_mem (Mᗮ.smul_mem a hxy) (hSM' ⟨x - y, hxy, rfl⟩)
  have h0 : S y - a • y = 0 := by
    have hmem : S y - a • y ∈ M ⊓ Mᗮ := ⟨h1, h2⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp h0

private theorem eq_of_toCuspSubcarrier_eq {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (ψ₁ ψ₂ : AdelicGL2 (𝓞 F) F → ℂ) (h₁ : ψ₁ ∈ cuspMemberSubmodule F Φ₀ ξ) (h₂ : ψ₂ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (h : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ₁, h₁⟩ = toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ₂, h₂⟩) : ψ₁ = ψ₂ := by
  have hc : toCarrier F hΦ₀ σ ξ ⟨ψ₁, h₁.1.1.1⟩ = toCarrier F hΦ₀ σ ξ ⟨ψ₂, h₂.1.1.1⟩ := by
    have := congrArg Subtype.val h
    rwa [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe] at this
  have h12 : ψ₁ - ψ₂ ∈ cuspMemberSubmodule F Φ₀ ξ := Submodule.sub_mem _ h₁ h₂
  have hcont : ψ₁ - ψ₂ ∈ contMemberSubmodule F Φ₀ ξ := ⟨h12.1.1.1, h12.2⟩
  have h0 : toCarrier F hΦ₀ σ ξ ⟨ψ₁ - ψ₂, hcont.1⟩ = 0 := by
    have hsub := (toCarrier F hΦ₀ σ ξ).map_sub ⟨ψ₁, h₁.1.1.1⟩ ⟨ψ₂, h₂.1.1.1⟩
    rw [hc, sub_self] at hsub
    exact hsub
  exact sub_eq_zero.mp (AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ (ψ₁ - ψ₂) hcont h0)

private theorem exists_cuspLift_rightTranslate {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)
          = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F g φ, rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g φ hφ⟩ := by
  obtain ⟨T, -, hT, -, -, -⟩ := AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ g

  set S₀ : Submodule ℂ (Carrier F Φ₀ σ) := Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hS₀
  have hcl : (cuspSubcarrier F hΦ₀ σ ξ : Set (Carrier F Φ₀ σ)) = closure (S₀ : Set (Carrier F Φ₀ σ)) :=
    Submodule.topologicalClosure_coe S₀

  have hmap₀ : Set.MapsTo T (S₀ : Set (Carrier F Φ₀ σ)) (S₀ : Set (Carrier F Φ₀ σ)) := by
    rintro _ ⟨⟨φ, hφm⟩, hφc, rfl⟩
    have hφc' : φ ∈ cuspMemberSubmodule F Φ₀ ξ := hφc
    have hcont : φ ∈ contMemberSubmodule F Φ₀ ξ := ⟨hφc'.1.1.1, hφc'.2⟩
    have hR := AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g φ hφc'
    refine ⟨⟨rightTranslate F g φ, hR.1.1.1⟩, hR, ?_⟩
    show toCarrier F hΦ₀ σ ξ ⟨rightTranslate F g φ, hR.1.1.1⟩ = T (toCarrier F hΦ₀ σ ξ ⟨φ, hφm⟩)
    rw [hT.comm φ hcont]

  have hmap : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), T v ∈ cuspSubcarrier F hΦ₀ σ ξ := by
    intro v
    have hv : (v : Carrier F Φ₀ σ) ∈ closure (S₀ : Set (Carrier F Φ₀ σ)) := by
      rw [← hcl]; exact v.2
    rw [← SetLike.mem_coe, hcl]
    exact map_mem_closure T.continuous hv hmap₀
  refine ⟨(T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) (fun v => hmap v), ?_⟩
  intro φ hφ
  apply Subtype.ext
  show T (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ : Carrier F Φ₀ σ)
    = (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F g φ, _⟩ : Carrier F Φ₀ σ)
  rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
  exact hT.comm φ ⟨hφ.1.1.1, hφ.2⟩

private theorem isCuspLift_of_forall {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (g : AdelicGL2 (𝓞 F) F)
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hS : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)
          = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F g φ, rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g φ hφ⟩) :
    IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S :=
  isCuspLift_of_forall_exists F hΦ₀ σ ξ (rightTranslate F g) S fun φ => ⟨rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g φ φ.2, hS φ φ.2⟩

private theorem heckeGen_mem_finiteAdelicGL2Subgroup (v : HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply]
  exact heckeGenAt_fst _ i j

private theorem mem_finiteAdelicGL2Subgroup_of_mem_doubleCoset {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    (hU : U ≤ finiteAdelicGL2Subgroup F) {g x : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F)
    (hx : x ∈ HeckePair.doubleCoset U g) : x ∈ finiteAdelicGL2Subgroup F := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hu) hg) (hU hu')

end AutomorphicForm.Meets

end

open AutomorphicForm.Meets in

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ)
    (hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψK : ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ)
    (hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hψM : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ M)
    (hperp : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ Mᗮ) :
    IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ψ := by
  classical
  set pins := (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) with hpins

  obtain ⟨hψc, hψsc⟩ :=
    AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
      F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) ξ ψ hψK
  have hψ1 : IsSmoothCuspAutomorphicFnAt F pins ξ ψ := by
    have h := hψsc 1
    have : rightTranslate F 1 ψ = ψ := funext fun x => by rw [rightTranslate_apply, mul_one]
    rwa [this] at h
  have hMperp : IsClosedCuspSubrep F hΦ₀ σ ξ Mᗮ :=
    AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal F hΦ₀ σ ξ hσ M hM

  have key : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ a : ℂ,
      rightTranslate F g φ = a • φ → rightTranslate F g ψ = a • ψ := by
    intro g hg a hφeq
    obtain ⟨S, hS⟩ := exists_cuspLift_rightTranslate hΦ₀ σ ξ hσ g
    have hSl : IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S := isCuspLift_of_forall hΦ₀ σ ξ g S hS
    have hSM := hM.map_le_of_rightTranslate_fin g hg S hSl
    have hSM' := hMperp.map_le_of_rightTranslate_fin g hg S hSl

    have hx : S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩) = a • toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ := by
      rw [hS φ hφm, ← map_smul]
      congr 1
      exact Subtype.ext hφeq
    have hy := proj_eq M S hSM hSM' hψM hperp a hx

    rw [hS ψ hψm, ← map_smul] at hy
    exact eq_of_toCuspSubcarrier_eq hΦ₀ σ ξ _ _ _ ((cuspMemberSubmodule F Φ₀ ξ).smul_mem a hψm) hy

  refine ⟨hψ1, hψc, ?_, ?_, ?_⟩
  ·
    intro g u hu
    have hu' : u ∈ finiteAdelicGL2Subgroup F := hu.2
    have hφu : rightTranslate F u φ = (1 : ℂ) • φ := by
      rw [one_smul]; funext x; exact hφI.level_invariant x u hu
    have := congrFun (key u hu' 1 hφu) g
    rwa [rightTranslate_apply, one_smul] at this
  ·
    intro v hv
    obtain ⟨reps, hsys, heq⟩ := hφI.hecke_eigen v hv
    refine ⟨reps, hsys, ?_⟩

    have hUfin : pins.U N ≤ finiteAdelicGL2Subgroup F := fun x hx => hx.2
    have hreps : ∀ i, reps i ∈ finiteAdelicGL2Subgroup F := fun i =>
      mem_finiteAdelicGL2Subgroup_of_mem_doubleCoset hUfin (heckeGen_mem_finiteAdelicGL2Subgroup v) (hsys.mem_doubleCoset i)

    choose Sf hSf using fun i => exists_cuspLift_rightTranslate hΦ₀ σ ξ hσ (reps i)
    have hSfM : ∀ i, ∀ m ∈ M, Sf i m ∈ M := fun i m hm =>
      hM.map_le_of_rightTranslate_fin (reps i) (hreps i) (Sf i) (isCuspLift_of_forall hΦ₀ σ ξ (reps i) (Sf i) (hSf i))
        ⟨m, hm, rfl⟩
    have hSfM' : ∀ i, ∀ m ∈ Mᗮ, Sf i m ∈ Mᗮ := fun i m hm =>
      hMperp.map_le_of_rightTranslate_fin (reps i) (hreps i) (Sf i) (isCuspLift_of_forall hΦ₀ σ ξ (reps i) (Sf i) (hSf i))
        ⟨m, hm, rfl⟩
    set S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := ∑ i, Sf i with hSdef
    have hSapp : ∀ m, S m = ∑ i, Sf i m := fun m => by
      rw [hSdef, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    have hSM : M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M := by
      rintro _ ⟨m, hm, rfl⟩
      show S m ∈ M
      rw [hSapp]
      exact M.sum_mem fun i _ => hSfM i m hm
    have hSM' : Mᗮ.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ Mᗮ := by
      rintro _ ⟨m, hm, rfl⟩
      show S m ∈ Mᗮ
      rw [hSapp]
      exact Mᗮ.sum_mem fun i _ => hSfM' i m hm

    have hsum_mem : ∀ (χ : AdelicGL2 (𝓞 F) F → ℂ), χ ∈ cuspMemberSubmodule F Φ₀ ξ →
        (∑ i, rightTranslate F (reps i) χ) ∈ cuspMemberSubmodule F Φ₀ ξ := fun χ hχ =>
      Submodule.sum_mem _ fun i _ => rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (reps i) χ hχ
    have hSclass : ∀ (χ : AdelicGL2 (𝓞 F) F → ℂ) (hχ : χ ∈ cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ ⟨χ, hχ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨∑ i, rightTranslate F (reps i) χ, hsum_mem χ hχ⟩ := by
      intro χ hχ
      rw [hSapp]
      simp_rw [hSf _ χ hχ]
      rw [← map_sum]
      congr 1
      apply Subtype.ext
      rw [Submodule.coe_sum]
    have hsum_fun : ∀ (χ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F),
        (∑ i, rightTranslate F (reps i) χ) x = SmoothCusp.heckeCosetSum F reps χ x := by
      intro χ x
      rw [Finset.sum_apply]
      rfl

    have hφsum : (∑ i, rightTranslate F (reps i) φ) = Ψ.a v • φ := by
      funext x
      rw [hsum_fun, heq x, Pi.smul_apply, smul_eq_mul]
    have hx : S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩) = Ψ.a v • toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ := by
      rw [hSclass φ hφm, ← map_smul]
      congr 1
      exact Subtype.ext hφsum
    have hy := proj_eq M S hSM hSM' hψM hperp (Ψ.a v) hx
    rw [hSclass ψ hψm, ← map_smul] at hy
    have hψsum := eq_of_toCuspSubcarrier_eq hΦ₀ σ ξ _ _ _ ((cuspMemberSubmodule F Φ₀ ξ).smul_mem (Ψ.a v) hψm) hy
    intro x
    rw [← hsum_fun, hψsum, Pi.smul_apply, smul_eq_mul]
  ·
    intro v hv g
    have hψls := ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ ψ).mp hψm.1.1.1).1
    have hφls := ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp hφm.1.1.1).1
    have hψz := hψls.central_transform ⟨Matrix.GeneralLinearGroup.det (pins.gen v), trivial⟩ g
    by_cases h0 : φ = 0
    ·
      have hφ0 : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ = 0 := by
        have : (⟨φ, hφm⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = 0 := Subtype.ext h0
        rw [this, map_zero]
      have hψ0 : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ = 0 := by
        have hmem : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ M ⊓ Mᗮ := by
          refine ⟨hψM, ?_⟩
          have := Mᗮ.neg_mem hperp
          rwa [hφ0, zero_sub, neg_neg] at this
        rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
      have hψzero : ψ = 0 := by
        refine eq_of_toCuspSubcarrier_eq hΦ₀ σ ξ ψ 0 hψm (Submodule.zero_mem _) ?_
        rw [hψ0]
        have : (⟨0, Submodule.zero_mem _⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = 0 := Subtype.ext rfl
        rw [this, map_zero]
      simp only [hψzero, Pi.zero_apply, mul_zero]
    · obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp h0
      have h1 := hφI.central_eigen v hv g₀
      have h2 := hφls.central_transform ⟨Matrix.GeneralLinearGroup.det (pins.gen v), trivial⟩ g₀
      have hb : Ψ.toRawCentral.b v
          = ((ξ ⟨Matrix.GeneralLinearGroup.det (pins.gen v), trivial⟩ : ℂˣ) : ℂ) :=
        mul_right_cancel₀ hg₀ (h1.symm.trans h2)
      rw [hb]
      exact hψz

#print axioms solution

end S_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal (solution)
