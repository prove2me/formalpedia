-- Prove2me | solution 1 for AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/95ca2611-2222-5032-ad95-5100f8620997

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half
import Theorems.Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_AutomorphicForm_convOp_residualProjection_of_residualProjection
import Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
import Theorems.Thm_AutomorphicForm_limUnder_nhdsNE_eq_convOp_axis_continuation_weylIntertwiningIntegral_of_meromorphicNFOn_of_eq_weylIntertwiningIntegral_convOp
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace P2Glue19

open AutomorphicForm

theorem analyticOnNhd_convOp
    (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (O : Set ℂ) (hO : IsOpen O) (E : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
    (hEan : ∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => E s g) O)
    (hEc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => E p.1 p.2) (O ×ˢ Set.univ))
    (x : AdelicGL2 (𝓞 K) K) :
    AnalyticOnNhd ℂ (fun s => convOp K f (E s) x) O := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
    NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hd : DifferentiableOn ℂ
      (fun z => ∫ a, E z (x * a) * f a ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) O := by
    refine Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
      (adelicGLHaar (Fin 2) (𝓞 K) K) hO hfc (fun z a => E z (x * a) * f a) ?_ ?_ ?_
    · have hmap : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ((p.1, x * p.2) : ℂ × AdelicGL2 (𝓞 K) K)) :=
        continuous_fst.prodMk (continuous_const.mul continuous_snd)
      have h1 : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => E p.1 (x * p.2)) (O ×ˢ Set.univ) := by
        refine hEc.comp hmap.continuousOn ?_
        intro p hp
        exact ⟨hp.1, Set.mem_univ _⟩
      exact h1.mul ((hf.comp continuous_snd).continuousOn)
    · intro z _ a ha
      show E z (x * a) * f a = 0
      rw [image_eq_zero_of_notMem_tsupport ha, mul_zero]
    · intro a
      exact ((hEan (x * a)).differentiableOn).mul_const (f a)
  have hFeq : (fun s => convOp K f (E s) x) =
      fun z => ∫ a, E z (x * a) * f a ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    funext z
    rfl
  rw [hFeq]
  exact hd.analyticOnNhd hO

end P2Glue19

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (c : ℝ≥0∞) (_hc0 : c ≠ 0) (_hcT : c ≠ ∞)
      (_hc : ∀ H : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable H →
        ∫⁻ g, H g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                H (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K))
      (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (φf ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK φ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hφrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (Oψ : ιP → Set ℂ) (Eψ Nψ : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ : ∀ i : ιP,
      IsOpen (Oψ i) ∧ IsPreconnected (Oψ i) ∧ {s : ℂ | s.re = 0} ⊆ (Oψ i) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (Oψ i) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ i s g) (Oψ i)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ i s g) (Oψ i)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ i s g = ψf i s g + ∑' ξ : K, ψf i s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ i s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf i s) g))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀
      (pφ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpφ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pφ)
      (_hpφc : ∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (pφ - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpφo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (AutomorphicForm.pseudoEisenstein K φ g - pφ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (pψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ)
      (_hpψc : ∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (pψ - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
,
    (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        AutomorphicForm.pseudoEisenstein K φ g * conj (convOp K f (AutomorphicForm.pseudoEisenstein K ψ) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        pφ g * conj (convOp K f pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
    ((c.toReal * ((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal * V.toReal ^ 2
        * Real.log (β / α) / (16 * Real.pi) : ℝ) : ℂ) *
    ∑ i : ιP, ∫ t : ℝ,
      ((∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by
  intro αm hαm c hc0 hcT hc D hDm hDF V hV0 hVT hV ιP _iF μP νP hμ hν hμic hνic hμc hμν rP hr hdist φf ψf hφf hψf hφjc hψjc
    hφhol hψhol hψK hψsm hψKu hνc hφdec hψdec φ ψ hφ hψ hφrep hψrep Oψ Eψ Nψ hEψ f hf hfc hfact hbi harch
    pφ hpφ hpφc hpφo pψ hpψ hpψc hpψo
  letI hMS : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  set μH := adelicGLHaar (Fin 2) (𝓞 K) K with hμH
  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ

  obtain ⟨-, -, -, hsub, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hopen : IsOpen {s : ℂ | (1 / 2 : ℝ) < s.re} := isOpen_lt continuous_const Complex.continuous_re

  obtain ⟨hψf', hψjc', hψhol', hψK', hψsm', hψKu', hψdec', -, -, hψ'prof, hψ'rep, hRθ⟩ :=
    AutomorphicForm.paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite
      K α β hα hαβ SK ξK hξc hξt N hN tysK hξu hαm ιP μP νP hμ hν hμic hνic hμc hνc hμν ψf hψf hψjc hψhol hψdec
      ψ hψ hψrep f hf hfc hfact hbi harch

  have hNan : ∀ (i : ιP) (g : AdelicGL2 (𝓞 K) K), AnalyticOnNhd ℂ (fun s => convOp K f (Nψ i s) g) (Oψ i) :=
    fun i g => P2Glue19.analyticOnNhd_convOp K f hf hfc (Oψ i) (hEψ i).1 (Nψ i) (hEψ i).2.2.2.2.2.1
      (hEψ i).2.2.2.2.2.2.2.1 g

  have hM : ∀ (i : ιP) (g : AdelicGL2 (𝓞 K) K), ∃ M' : ℂ → ℂ, MeromorphicOn M' Set.univ ∧
      ∀ s : ℂ, 1 / 2 < s.re → M' s =
        weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (convOp K f (ψf i s)) g :=
    fun i g => AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family K hαm (μP i) (νP i)
      (hμ i) (hν i) (hμic i) (hνic i) (fun s => convOp K f (ψf i s)) (hψf' i) (hψK' i) (hψsm' i) (hψjc' i) (hψhol' i) g
  choose M' hM'mer hM'eq using hM
  set Mc : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun i s g => toMeromorphicNFOn (M' i g) Set.univ s with hMcdef

  have hhalfeq : ∀ (i : ιP) (s : ℂ), 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
      weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (convOp K f (ψf i s)) g = convOp K f (Nψ i s) g := by
    intro i s hs g
    have hNfun : Nψ i s = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf i s) :=
      funext fun g' => (hEψ i).2.2.2.2.2.2.2.2.2 s hs g'
    rw [hNfun]
    exact AutomorphicForm.weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half
      K hαm (μP i) (νP i) (hμ i) (hν i) s hs (ψf i s) (hψf i s)
      ((hψjc i).comp (continuous_const.prodMk continuous_id)) f hf hfc g
  have hMc : ∀ (i : ιP) (g : AdelicGL2 (𝓞 K) K), MeromorphicNFOn (fun s : ℂ => Mc i s g) Set.univ ∧
      ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
        Mc i s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (convOp K f (ψf i s)) g := by
    intro i g
    refine ⟨meromorphicNFOn_toMeromorphicNFOn _ _, fun s hs => ?_⟩
    have hNs : AnalyticAt ℂ (fun z => convOp K f (Nψ i z) g) s := hNan i g s ((hEψ i).2.2.2.1 hs)
    have hev : (fun z => convOp K f (Nψ i z) g) =ᶠ[𝓝 s] M' i g := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      rw [hM'eq i g z hz, hhalfeq i z hz g]
    have hMa : AnalyticAt ℂ (M' i g) s := hNs.congr hev
    show toMeromorphicNFOn (M' i g) Set.univ s = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (hM'mer i g) (Set.mem_univ s),
      toMeromorphicNFAt_eq_self.2 hMa.meromorphicNFAt, hM'eq i g s hs]

  have hθψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
      (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK
      (AutomorphicForm.pseudoEisenstein K ψ) :=
    AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ Φ hsub hFD ξK ψ hψ
  obtain ⟨hTp, hTpc, hTpo⟩ := AutomorphicForm.convOp_residualProjection_of_residualProjection
    K α β hα hαβ ξK hξc hξt hξu f hf hfc (AutomorphicForm.pseudoEisenstein K ψ) pψ hθψ hpψ hpψc hpψo
  have hTpo' : ∀ h : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
        (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK h →
      h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
        (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z ξK →
      ∫ g in Φ, (AutomorphicForm.pseudoEisenstein K (convOp K f ψ) g - convOp K f pψ g) * conj (h g) ∂μH = 0 := by
    intro h hh hres
    have := hTpo h hh hres
    simpa only [hRθ] using this

  have hP := AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
    K hαm α β hα hαβ Φ hsub hFD c hc0 hcT hc D hDm hDF V hV0 hVT hV ξK ιP μP νP hμ hν hμic hνic hμc hμν rP hr hdist
    φf (fun i s => convOp K f (ψf i s)) hφf hψf' hφjc hψjc' hφhol hψhol' hψK' hψsm' hψKu' hνc hφdec hψdec'
    φ (convOp K f ψ) hφ hψ'prof hφrep hψ'rep Mc hMc pφ (convOp K f pψ) hpφ hTp hpφc hTpc hpφo hTpo'

  have hRN : ∀ (i : ιP) (t : ℝ) (g : AdelicGL2 (𝓞 K) K),
      Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I))) (fun s : ℂ => Mc i s g) =
        convOp K f (Nψ i (-((t : ℂ) * Complex.I))) g :=
    fun i => AutomorphicForm.limUnder_nhdsNE_eq_convOp_axis_continuation_weylIntertwiningIntegral_of_meromorphicNFOn_of_eq_weylIntertwiningIntegral_convOp
      K hαm (μP i) (νP i) (hμ i) (hν i) (ψf i) (hψf i) (hψjc i) (Oψ i) (Eψ i) (Nψ i) (hEψ i) f hf hfc (Mc i) (hMc i)

  have hLHS : ∫ g in Φ, AutomorphicForm.pseudoEisenstein K φ g *
        conj (convOp K f (AutomorphicForm.pseudoEisenstein K ψ) g) ∂μH =
      ∫ g in Φ, AutomorphicForm.pseudoEisenstein K φ g * conj (AutomorphicForm.pseudoEisenstein K (convOp K f ψ) g) ∂μH := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    dsimp only
    rw [hRθ g]
  rw [hLHS]
  have hP' : ∫ g in Φ, AutomorphicForm.pseudoEisenstein K φ g *
        conj (AutomorphicForm.pseudoEisenstein K (convOp K f ψ) g) ∂μH =
      (∫ g in Φ, pφ g * conj (convOp K f pψ g) ∂μH) + _ := hP
  rw [hP', add_sub_cancel_left]
  simp only [hRN]

end S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener (solution)
