-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/546ac6a1-d29b-527e-a73b-8f09c120195f

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut
import Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"
open AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm
p2m_export "AutomorphicForm" "archDerivAtComplex_add archDerivAtComplex_smul archDerivAtComplex_comp_mul_right archCasimirAtComplex_comp_mul_right archCasimirBarAtComplex_comp_mul_right IsArchSmoothAtComplex isArchSmoothAtComplex_const ArchDirComplex archDerivAtComplex archDelAt archDelBarAt archCasimirAtComplex archCasimirBarAtComplex archDerivAtComplex_const archCasimirAtComplex_const archCasimirBarAtComplex_const ArchDir productionPinsOf AdelicGL2 finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent ArchTypeFamily archCutSubmodule finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rightConv rightConv_apply CuspidalConstituent.isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex"
namespace CasAux38
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K]

private theorem rightConv_smul_left (c : ℂ) (φ f : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K (c • φ) f = c • rightConv K φ f := by
  funext g
  rw [Pi.smul_apply, rightConv_apply, rightConv_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring

end AutomorphicForm.CasAux38

namespace E38CASC

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex)

theorem archDelAt_add' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ)
    (d : ArchDir) : archDelAt hw d (φ + ψ) = archDelAt hw d φ + archDelAt hw d ψ := by
  unfold AutomorphicForm.archDelAt
  rw [archDerivAtComplex_add hφ hψ, archDerivAtComplex_add hφ hψ]
  funext g; simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]; ring

theorem archDelAt_smul' (d : ArchDir) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelAt hw d (c • φ) = c • archDelAt hw d φ := by
  unfold AutomorphicForm.archDelAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_smul]
  funext g; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring

theorem archDelBarAt_add' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ)
    (d : ArchDir) : archDelBarAt hw d (φ + ψ) = archDelBarAt hw d φ + archDelBarAt hw d ψ := by
  unfold AutomorphicForm.archDelBarAt
  rw [archDerivAtComplex_add hφ hψ, archDerivAtComplex_add hφ hψ]
  funext g; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

theorem archDelBarAt_smul' (d : ArchDir) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelBarAt hw d (c • φ) = c • archDelBarAt hw d φ := by
  unfold AutomorphicForm.archDelBarAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_smul]
  funext g; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

theorem archCasimirAtComplex_add' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) :
    archCasimirAtComplex hw (φ + ψ) = archCasimirAtComplex hw φ + archCasimirAtComplex hw ψ := by
  unfold AutomorphicForm.archCasimirAtComplex
  rw [archDelAt_add' hw hφ hψ .H, archDelAt_add' hw (hφ.archDelAt .H) (hψ.archDelAt .H) .H,
    archDelAt_add' hw hφ hψ .Fm, archDelAt_add' hw (hφ.archDelAt .Fm) (hψ.archDelAt .Fm) .E]
  funext g; simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem archCasimirAtComplex_smul' (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    archCasimirAtComplex hw (c • φ) = c • archCasimirAtComplex hw φ := by
  unfold AutomorphicForm.archCasimirAtComplex
  rw [archDelAt_smul' hw .H, archDelAt_smul' hw .H, archDelAt_smul' hw .Fm, archDelAt_smul' hw .E]
  funext g; simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem archCasimirBarAtComplex_add' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) :
    archCasimirBarAtComplex hw (φ + ψ) = archCasimirBarAtComplex hw φ + archCasimirBarAtComplex hw ψ := by
  unfold AutomorphicForm.archCasimirBarAtComplex
  rw [archDelBarAt_add' hw hφ hψ .H, archDelBarAt_add' hw (hφ.archDelBarAt .H) (hψ.archDelBarAt .H) .H,
    archDelBarAt_add' hw hφ hψ .Fm, archDelBarAt_add' hw (hφ.archDelBarAt .Fm) (hψ.archDelBarAt .Fm) .E]
  funext g; simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem archCasimirBarAtComplex_smul' (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    archCasimirBarAtComplex hw (c • φ) = c • archCasimirBarAtComplex hw φ := by
  unfold AutomorphicForm.archCasimirBarAtComplex
  rw [archDelBarAt_smul' hw .H, archDelBarAt_smul' hw .H, archDelBarAt_smul' hw .Fm, archDelBarAt_smul' hw .E]
  funext g; simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

end E38CASC

open AutomorphicForm.CasAux38

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsComplex) :
    ∃ lam lam' : ℂ, ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x := by
  classical
  set X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys with hXdef
  haveI : FiniteDimensional ℂ X :=
    AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
      K c u d₁ d₂ T hd hcov ξ N hN tys V hV
  have hSMO := fun (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ X) =>
    AutomorphicForm.CuspidalConstituent.isArchSmoothAtComplex_and_continuous_archDerivAtComplex_and_archCasimirAtComplex_mem_of_mem_cut
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys w hw x hx
  haveI : Nontrivial X := Submodule.nontrivial_iff_ne_bot.2 hX
  have hcontV : ∀ x ∈ V, Continuous x := by
    intro x hx
    have hxK : x ∈ cuspKFiniteSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ := hV.1.le hx
    refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hxK
    · rintro φ ⟨-, hφc, -⟩; exact hφc
    · exact continuous_zero
    · intro u v _ _ hu hv; exact hu.add hv
    · intro r u _ hu; exact hu.const_smul r

  let ΩX : X →ₗ[ℂ] X :=
    { toFun := fun x => ⟨archCasimirAtComplex hw (x : AdelicGL2 (𝓞 K) K → ℂ), (hSMO x x.2).2.2.2.1⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show archCasimirAtComplex hw ((x : AdelicGL2 (𝓞 K) K → ℂ) + y) = archCasimirAtComplex hw x + archCasimirAtComplex hw y
        exact E38CASC.archCasimirAtComplex_add' hw (hSMO x x.2).1 (hSMO y y.2).1
      map_smul' := fun r x => by
        apply Subtype.ext
        show archCasimirAtComplex hw (r • (x : AdelicGL2 (𝓞 K) K → ℂ)) = r • archCasimirAtComplex hw x
        exact E38CASC.archCasimirAtComplex_smul' hw r x }
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue ΩX
  obtain ⟨x₀, hx₀⟩ := hlam.exists_hasEigenvector
  have hx₀eq : archCasimirAtComplex hw (x₀ : AdelicGL2 (𝓞 K) K → ℂ) = lam • (x₀ : AdelicGL2 (𝓞 K) K → ℂ) := by
    have h := hx₀.apply_eq_smul
    exact congrArg Subtype.val h
  have hx₀ne : (x₀ : AdelicGL2 (𝓞 K) K → ℂ) ≠ 0 := fun h => hx₀.2 (Subtype.ext h)

  let W₁ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    { carrier := {x | x ∈ V ∧ IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧ archCasimirAtComplex hw x = lam • x}
      zero_mem' := by
        refine ⟨V.zero_mem, isArchSmoothAtComplex_const hw 0, fun d => ?_, fun d d' => ?_, ?_⟩
        · rw [show (0 : AdelicGL2 (𝓞 K) K → ℂ) = fun _ => (0 : ℂ) from rfl, archDerivAtComplex_const]; exact continuous_const
        · rw [show (0 : AdelicGL2 (𝓞 K) K → ℂ) = fun _ => (0 : ℂ) from rfl, archDerivAtComplex_const,
            show (fun _ : AdelicGL2 (𝓞 K) K => (0 : ℂ)) = fun _ => (0 : ℂ) from rfl, archDerivAtComplex_const]
          exact continuous_const
        · rw [show (0 : AdelicGL2 (𝓞 K) K → ℂ) = fun _ => (0 : ℂ) from rfl, archCasimirAtComplex_const]
          funext g; simp
      add_mem' := by
        rintro a b ⟨haV, has, ha1, ha2, haΩ⟩ ⟨hbV, hbs, hb1, hb2, hbΩ⟩
        refine ⟨V.add_mem haV hbV, has.add hbs, ?_, ?_, ?_⟩
        · intro d; rw [archDerivAtComplex_add has hbs]; exact (ha1 d).add (hb1 d)
        · intro d d'
          rw [archDerivAtComplex_add has hbs, archDerivAtComplex_add (has.archDerivAtComplex d') (hbs.archDerivAtComplex d')]
          exact (ha2 d d').add (hb2 d d')
        · rw [E38CASC.archCasimirAtComplex_add' hw has hbs, haΩ, hbΩ, smul_add]
      smul_mem' := by
        rintro r a ⟨haV, has, ha1, ha2, haΩ⟩
        refine ⟨V.smul_mem r haV, has.smul r, ?_, ?_, ?_⟩
        · intro d; rw [archDerivAtComplex_smul]; exact (ha1 d).const_smul r
        · intro d d'; rw [archDerivAtComplex_smul, archDerivAtComplex_smul]; exact (ha2 d d').const_smul r
        · rw [E38CASC.archCasimirAtComplex_smul' hw, haΩ, smul_comm] }
  have hW₁le : W₁ ≤ V := fun x hx => hx.1
  have hW₁sub : IsCuspSubrep K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ W₁ :=
    { le := fun x hx => hV.1.le hx.1
      rightTranslate_fin_mem := by
        rintro g hg x ⟨hxV, hxs, hx1, hx2, hxΩ⟩
        have hk : glArch (𝓞 K) K g = 1 := (mem_finiteAdelicGL2Subgroup_iff K g).1 hg
        refine ⟨hV.1.rightTranslate_fin_mem g hg x hxV, hxs.comp_mul_right hk, ?_, ?_, ?_⟩
        · intro d
          show Continuous (archDerivAtComplex hw d (fun y => x (y * g)))
          rw [archDerivAtComplex_comp_mul_right hw d x hk]
          exact (hx1 d).comp (continuous_id.mul continuous_const)
        · intro d d'
          show Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (fun y => x (y * g))))
          rw [archDerivAtComplex_comp_mul_right hw d' x hk, archDerivAtComplex_comp_mul_right hw d (archDerivAtComplex hw d' x) hk]
          exact (hx2 d d').comp (continuous_id.mul continuous_const)
        · show archCasimirAtComplex hw (fun y => x (y * g)) = lam • (fun y => x (y * g))
          rw [archCasimirAtComplex_comp_mul_right hw x hk, hxΩ]; rfl
      rightTranslate_arch_mem := by
        rintro w' k x ⟨hxV, hxs, hx1, hx2, hxΩ⟩
        obtain ⟨h1, -⟩ := AutomorphicForm.archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex K w hw x
          (hcontV x hxV) hxs hx1 hx2
        obtain ⟨hs, hc1, hc2, hΩ, hΩb⟩ := h1 w' k
        refine ⟨hV.1.rightTranslate_arch_mem w' k x hxV, hs, hc1, hc2, ?_⟩
        rw [hΩ, hxΩ]; rfl
      rightConv_mem := by
        rintro f tys' hf hbf x ⟨hxV, hxs, hx1, hx2, hxΩ⟩
        obtain ⟨-, h2⟩ := AutomorphicForm.archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex K w hw x
          (hcontV x hxV) hxs hx1 hx2
        obtain ⟨hs, hc1, hc2, hΩ, hΩb⟩ := h2 f tys' hf hbf
        refine ⟨hV.1.rightConv_mem f tys' hf hbf x hxV, hs, hc1, hc2, ?_⟩
        rw [hΩ, hxΩ, rightConv_smul_left] }

  have hx₀W : (x₀ : AdelicGL2 (𝓞 K) K → ℂ) ∈ W₁ := by
    have hx₀X : (x₀ : AdelicGL2 (𝓞 K) K → ℂ) ∈ X := x₀.2
    obtain ⟨hs, hc1, hc2, -⟩ := hSMO _ hx₀X
    exact ⟨hx₀X.1.1, hs, hc1, hc2, hx₀eq⟩
  have hW₁ne : W₁ ≠ ⊥ := by
    intro h
    apply hx₀ne
    have : (x₀ : AdelicGL2 (𝓞 K) K → ℂ) ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) := h ▸ hx₀W
    exact (Submodule.mem_bot ℂ).1 this
  have hV₁ : W₁ = V := by
    rcases hV.2.2 W₁ hW₁sub hW₁le with h | h
    · exact absurd h hW₁ne
    · exact h

  let ΩbX : X →ₗ[ℂ] X :=
    { toFun := fun x => ⟨archCasimirBarAtComplex hw (x : AdelicGL2 (𝓞 K) K → ℂ), (hSMO x x.2).2.2.2.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show archCasimirBarAtComplex hw ((x : AdelicGL2 (𝓞 K) K → ℂ) + y) = archCasimirBarAtComplex hw x + archCasimirBarAtComplex hw y
        exact E38CASC.archCasimirBarAtComplex_add' hw (hSMO x x.2).1 (hSMO y y.2).1
      map_smul' := fun r x => by
        apply Subtype.ext
        show archCasimirBarAtComplex hw (r • (x : AdelicGL2 (𝓞 K) K → ℂ)) = r • archCasimirBarAtComplex hw x
        exact E38CASC.archCasimirBarAtComplex_smul' hw r x }
  obtain ⟨lam', hlam'⟩ := Module.End.exists_eigenvalue ΩbX
  obtain ⟨x₁, hx₁⟩ := hlam'.exists_hasEigenvector
  have hx₁eq : archCasimirBarAtComplex hw (x₁ : AdelicGL2 (𝓞 K) K → ℂ) = lam' • (x₁ : AdelicGL2 (𝓞 K) K → ℂ) := by
    have h := hx₁.apply_eq_smul
    exact congrArg Subtype.val h
  have hx₁ne : (x₁ : AdelicGL2 (𝓞 K) K → ℂ) ≠ 0 := fun h => hx₁.2 (Subtype.ext h)

  let W₂ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    { carrier := {x | x ∈ V ∧ IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧ archCasimirBarAtComplex hw x = lam' • x}
      zero_mem' := by
        refine ⟨V.zero_mem, isArchSmoothAtComplex_const hw 0, fun d => ?_, fun d d' => ?_, ?_⟩
        · rw [show (0 : AdelicGL2 (𝓞 K) K → ℂ) = fun _ => (0 : ℂ) from rfl, archDerivAtComplex_const]; exact continuous_const
        · rw [show (0 : AdelicGL2 (𝓞 K) K → ℂ) = fun _ => (0 : ℂ) from rfl, archDerivAtComplex_const,
            show (fun _ : AdelicGL2 (𝓞 K) K => (0 : ℂ)) = fun _ => (0 : ℂ) from rfl, archDerivAtComplex_const]
          exact continuous_const
        · rw [show (0 : AdelicGL2 (𝓞 K) K → ℂ) = fun _ => (0 : ℂ) from rfl, archCasimirBarAtComplex_const]
          funext g; simp
      add_mem' := by
        rintro a b ⟨haV, has, ha1, ha2, haΩ⟩ ⟨hbV, hbs, hb1, hb2, hbΩ⟩
        refine ⟨V.add_mem haV hbV, has.add hbs, ?_, ?_, ?_⟩
        · intro d; rw [archDerivAtComplex_add has hbs]; exact (ha1 d).add (hb1 d)
        · intro d d'
          rw [archDerivAtComplex_add has hbs, archDerivAtComplex_add (has.archDerivAtComplex d') (hbs.archDerivAtComplex d')]
          exact (ha2 d d').add (hb2 d d')
        · rw [E38CASC.archCasimirBarAtComplex_add' hw has hbs, haΩ, hbΩ, smul_add]
      smul_mem' := by
        rintro r a ⟨haV, has, ha1, ha2, haΩ⟩
        refine ⟨V.smul_mem r haV, has.smul r, ?_, ?_, ?_⟩
        · intro d; rw [archDerivAtComplex_smul]; exact (ha1 d).const_smul r
        · intro d d'; rw [archDerivAtComplex_smul, archDerivAtComplex_smul]; exact (ha2 d d').const_smul r
        · rw [E38CASC.archCasimirBarAtComplex_smul' hw, haΩ, smul_comm] }
  have hW₂le : W₂ ≤ V := fun x hx => hx.1
  have hW₂sub : IsCuspSubrep K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ W₂ :=
    { le := fun x hx => hV.1.le hx.1
      rightTranslate_fin_mem := by
        rintro g hg x ⟨hxV, hxs, hx1, hx2, hxΩ⟩
        have hk : glArch (𝓞 K) K g = 1 := (mem_finiteAdelicGL2Subgroup_iff K g).1 hg
        refine ⟨hV.1.rightTranslate_fin_mem g hg x hxV, hxs.comp_mul_right hk, ?_, ?_, ?_⟩
        · intro d
          show Continuous (archDerivAtComplex hw d (fun y => x (y * g)))
          rw [archDerivAtComplex_comp_mul_right hw d x hk]
          exact (hx1 d).comp (continuous_id.mul continuous_const)
        · intro d d'
          show Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (fun y => x (y * g))))
          rw [archDerivAtComplex_comp_mul_right hw d' x hk, archDerivAtComplex_comp_mul_right hw d (archDerivAtComplex hw d' x) hk]
          exact (hx2 d d').comp (continuous_id.mul continuous_const)
        · show archCasimirBarAtComplex hw (fun y => x (y * g)) = lam' • (fun y => x (y * g))
          rw [archCasimirBarAtComplex_comp_mul_right hw x hk, hxΩ]; rfl
      rightTranslate_arch_mem := by
        rintro w' k x ⟨hxV, hxs, hx1, hx2, hxΩ⟩
        obtain ⟨h1, -⟩ := AutomorphicForm.archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex K w hw x
          (hcontV x hxV) hxs hx1 hx2
        obtain ⟨hs, hc1, hc2, hΩ, hΩb⟩ := h1 w' k
        refine ⟨hV.1.rightTranslate_arch_mem w' k x hxV, hs, hc1, hc2, ?_⟩
        rw [hΩb, hxΩ]; rfl
      rightConv_mem := by
        rintro f tys' hf hbf x ⟨hxV, hxs, hx1, hx2, hxΩ⟩
        obtain ⟨-, h2⟩ := AutomorphicForm.archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex K w hw x
          (hcontV x hxV) hxs hx1 hx2
        obtain ⟨hs, hc1, hc2, hΩ, hΩb⟩ := h2 f tys' hf hbf
        refine ⟨hV.1.rightConv_mem f tys' hf hbf x hxV, hs, hc1, hc2, ?_⟩
        rw [hΩb, hxΩ, rightConv_smul_left] }

  have hx₁W : (x₁ : AdelicGL2 (𝓞 K) K → ℂ) ∈ W₂ := by
    have hx₁X : (x₁ : AdelicGL2 (𝓞 K) K → ℂ) ∈ X := x₁.2
    obtain ⟨hs, hc1, hc2, -⟩ := hSMO _ hx₁X
    exact ⟨hx₁X.1.1, hs, hc1, hc2, hx₁eq⟩
  have hW₂ne : W₂ ≠ ⊥ := by
    intro h
    apply hx₁ne
    have : (x₁ : AdelicGL2 (𝓞 K) K → ℂ) ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) := h ▸ hx₁W
    exact (Submodule.mem_bot ℂ).1 this
  have hV₂ : W₂ = V := by
    rcases hV.2.2 W₂ hW₂sub hW₂le with h | h
    · exact absurd h hW₂ne
    · exact h
  refine ⟨lam, lam', fun x hx => ?_⟩
  have hxW₁ : x ∈ W₁ := by rw [hV₁]; exact hx
  have hxW₂ : x ∈ W₂ := by rw [hV₂]; exact hx
  exact ⟨hxW₁.2.1, hxW₁.2.2.1, hxW₁.2.2.2.1, hxW₁.2.2.2.2, hxW₂.2.2.2.2⟩

end S_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAtComplex_and_archCasimirAtComplex_eq_smul_of_isCuspConstituent (solution)
