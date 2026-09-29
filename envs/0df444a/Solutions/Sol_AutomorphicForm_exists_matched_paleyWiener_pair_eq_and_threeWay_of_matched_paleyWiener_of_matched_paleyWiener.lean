-- Prove2me | solution 1 for AutomorphicForm.exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5ff49471-3ed7-511e-9c5f-7cdb1e058663

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
import Definitions.Def_NumberField_NormPowChar

import Theorems.Thm_AutomorphicForm_exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_pseudoEisenstein_principalLevel_and_mem_archCutSubmodule_of_paleyWiener_principalLevel_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

namespace PKGskel

theorem ne_bot_of_forall_dvd_mem (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK) : N ≠ ⊥ := by
  intro hN0
  subst hN0
  have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ SK := fun v => hN v (dvd_zero _)
  haveI hfin : Finite (HeightOneSpectrum (𝓞 K)) :=
    Finite.of_injective (fun v => (⟨v, hall v⟩ : {v // v ∈ SK})) (fun a b h => congrArg Subtype.val h)

  have key : ∀ p : {p : ℕ // p.Prime}, ∃ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal.LiesOver (Ideal.span {((p : ℕ) : ℤ)}) := by
    intro p
    have hp : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
    have hp0 : ((p : ℕ) : ℤ) ≠ 0 := hp.ne_zero
    haveI hP : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp0).mpr hp
    have hPne : Ideal.span {((p : ℕ) : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := hP.isMaximal hPne
    obtain ⟨Q, hQmax, hQover⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
    have hQne : Q ≠ ⊥ := by
      intro hQ
      apply hPne
      rw [hQover.over, hQ, Ideal.under_bot]
    exact ⟨⟨Q, hQmax.isPrime, hQne⟩, hQover⟩
  choose f hf using key
  have finj : Function.Injective f := by
    intro p q hpq
    have h1 := (hf p).over
    have h2 := (hf q).over
    rw [hpq] at h1
    have h12 : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := h1.trans h2.symm
    rw [Ideal.span_singleton_eq_span_singleton] at h12
    have hd1 : (p : ℕ) ∣ (q : ℕ) := Int.natCast_dvd_natCast.mp h12.dvd
    have hd2 : (q : ℕ) ∣ (p : ℕ) := Int.natCast_dvd_natCast.mp h12.symm.dvd
    exact Subtype.ext (Nat.dvd_antisymm hd1 hd2)
  haveI : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOf_prime.to_subtype
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective f finj
  exact not_finite (HeightOneSpectrum (𝓞 K))

end PKGskel

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
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
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (ιP₁ : Type) [Fintype ιP₁]
      (μP₁ νP₁ : ιP₁ → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ₁ : ∀ e, IsUnitaryChar (𝓞 K) K (μP₁ e)) (_hν₁ : ∀ e, IsUnitaryChar (𝓞 K) K (νP₁ e))
      (_hμic₁ : ∀ e, IsIdeleClassChar (𝓞 K) K (μP₁ e)) (_hνic₁ : ∀ e, IsIdeleClassChar (𝓞 K) K (νP₁ e))
      (_hμc₁ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP₁ e x : ℂˣ) : ℂ))
      (_hμν₁ : ∀ (e : ιP₁)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP₁ e (z : (AdeleRing (𝓞 K) K)ˣ) * νP₁ e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP₁ : ιP₁ → ιP₁) (_hr₁ : ∀ e, μP₁ (rP₁ e) = νP₁ e ∧ νP₁ (rP₁ e) = μP₁ e)
      (_hdist₁ : ∀ e e' : ιP₁, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP₁ e x ≠ μP₁ e' x ∨ νP₁ e x ≠ νP₁ e' x)
      (ψf₁ : ιP₁ → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf₁ : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP₁ e) αm hαm s) (etaSnd (νP₁ e) αm hαm s) (ψf₁ e s))
      (_hψjc₁ : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf₁ e p.1 p.2))
      (_hψhol₁ : ∀ e g, Differentiable ℂ (fun s => ψf₁ e s g))
      (_hψK₁ : ∀ e s, IsArchKFinite K (ψf₁ e s)) (_hψsm₁ : ∀ e s, IsKfSmooth K (ψf₁ e s))
      (_hψKu₁ : ∀ (e : ιP₁) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf₁ e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc₁ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP₁ e x : ℂˣ) : ℂ))
      (_hψdec₁ : ∀ (e : ιP₁) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf₁ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₁ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ₁)
      (_hψrep₁ : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₁ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf₁ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em₁ : ιP₁ → ιE) (τ₁ : ιP₁ → ℝ)
      (_hem₁ : ∀ i : ιP₁, μP₁ i = μ (em₁ i) * NumberField.TateGlobal.normPowChar K (τ₁ i) ∧
        νP₁ i = ν (em₁ i) * (NumberField.TateGlobal.normPowChar K (τ₁ i))⁻¹)
      (_hψlev₁ : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf₁ i s (g * u) = ψf₁ i s g)
      (_hψty₁ : ∀ i (s : ℂ), ψf₁ i s ∈ archCutSubmodule K tysK)
      (pψ₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ₁)
      (_hpψc₁ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (pψ₁ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo₁ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (AutomorphicForm.pseudoEisenstein K ψ₁ g - pψ₁ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (ιP₂ : Type) [Fintype ιP₂]
      (μP₂ νP₂ : ιP₂ → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ₂ : ∀ e, IsUnitaryChar (𝓞 K) K (μP₂ e)) (_hν₂ : ∀ e, IsUnitaryChar (𝓞 K) K (νP₂ e))
      (_hμic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (μP₂ e)) (_hνic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (νP₂ e))
      (_hμc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP₂ e x : ℂˣ) : ℂ))
      (_hμν₂ : ∀ (e : ιP₂)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) * νP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP₂ : ιP₂ → ιP₂) (_hr₂ : ∀ e, μP₂ (rP₂ e) = νP₂ e ∧ νP₂ (rP₂ e) = μP₂ e)
      (_hdist₂ : ∀ e e' : ιP₂, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP₂ e x ≠ μP₂ e' x ∨ νP₂ e x ≠ νP₂ e' x)
      (ψf₂ : ιP₂ → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf₂ : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP₂ e) αm hαm s) (etaSnd (νP₂ e) αm hαm s) (ψf₂ e s))
      (_hψjc₂ : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf₂ e p.1 p.2))
      (_hψhol₂ : ∀ e g, Differentiable ℂ (fun s => ψf₂ e s g))
      (_hψK₂ : ∀ e s, IsArchKFinite K (ψf₂ e s)) (_hψsm₂ : ∀ e s, IsKfSmooth K (ψf₂ e s))
      (_hψKu₂ : ∀ (e : ιP₂) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf₂ e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP₂ e x : ℂˣ) : ℂ))
      (_hψdec₂ : ∀ (e : ιP₂) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₂ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ₂)
      (_hψrep₂ : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₂ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em₂ : ιP₂ → ιE) (τ₂ : ιP₂ → ℝ)
      (_hem₂ : ∀ i : ιP₂, μP₂ i = μ (em₂ i) * NumberField.TateGlobal.normPowChar K (τ₂ i) ∧
        νP₂ i = ν (em₂ i) * (NumberField.TateGlobal.normPowChar K (τ₂ i))⁻¹)
      (_hψlev₂ : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf₂ i s (g * u) = ψf₂ i s g)
      (_hψty₂ : ∀ i (s : ℂ), ψf₂ i s ∈ archCutSubmodule K tysK)
      (pψ₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ₂)
      (_hpψc₂ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (pψ₂ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo₂ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (AutomorphicForm.pseudoEisenstein K ψ₂ g - pψ₂ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0),
    ∃ (ιP : Type) (_instP : Fintype ιP)
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
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (uc₁ ur₁ ue₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₁) (_huc0₁ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₁ g = 0))
      (_hur₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₁)
      (_hurc₁ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₁ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₁)
      (_hueo₁ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₁ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₁ : AutomorphicForm.pseudoEisenstein K φ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₁ + ur₁ + ue₁)
      (uc₂ ur₂ ue₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₂) (_huc0₂ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₂ g = 0))
      (_hur₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₂)
      (_hurc₂ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₂ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₂)
      (_hueo₂ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₂ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₂ : AutomorphicForm.pseudoEisenstein K ψ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₂ + ur₂ + ue₂),
    φ = ψ₁ ∧ ψ = ψ₂ ∧
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ue₁ (g * u') = ue₁ g) ∧
    ue₁ ∈ archCutSubmodule K tysK ∧
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ue₂ (g * u') = ue₂ g) ∧
    ue₂ ∈ archCutSubmodule K tysK ∧
    ue₁ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))]
      (fun g => AutomorphicForm.pseudoEisenstein K ψ₁ g - pψ₁ g) ∧
    ue₂ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))]
      (fun g => AutomorphicForm.pseudoEisenstein K ψ₂ g - pψ₂ g) ∧
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K φ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K φ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ (2 : ℕ)) ∧
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ (2 : ℕ)) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE instE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP₁ instP₁ μP₁ νP₁ _hμ₁ _hν₁ _hμic₁ _hνic₁ _hμc₁ _hμν₁ rP₁ _hr₁ _hdist₁ ψf₁ _hψf₁ _hψjc₁ _hψhol₁ _hψK₁ _hψsm₁ _hψKu₁ _hνc₁ _hψdec₁ ψ₁ _hψ₁ _hψrep₁ em₁ τ₁ _hem₁ _hψlev₁ _hψty₁ pψ₁ _hpψ₁ _hpψc₁ _hpψo₁ ιP₂ instP₂ μP₂ νP₂ _hμ₂ _hν₂ _hμic₂ _hνic₂ _hμc₂ _hμν₂ rP₂ _hr₂ _hdist₂ ψf₂ _hψf₂ _hψjc₂ _hψhol₂ _hψK₂ _hψsm₂ _hψKu₂ _hνc₂ _hψdec₂ ψ₂ _hψ₂ _hψrep₂ em₂ τ₂ _hem₂ _hψlev₂ _hψty₂ pψ₂ _hpψ₂ _hpψc₂ _hpψo₂
  have hN0 : N ≠ ⊥ := PKGskel.ne_bot_of_forall_dvd_mem K SK N hN

  obtain ⟨ιP, instP, μP, νP, hμM, hνM, hμicM, hνicM, hμcM, hμνM, rP, hrM, hdistM, φf, ψf, hφfM, hψfM, hφjcM, hψjcM, hφholM, hψholM, hψKM, hψsmM, hψKuM, hνcM, hφdecM, hψdecM, hφKM, hφsmM, hφKuM, hφlevM, hφtyM, hψlevM, hψtyM, em, τ, hemM, hrep₁, hrep₂⟩ :=
    AutomorphicForm.exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP₁ μP₁ νP₁ _hμ₁ _hν₁ _hμic₁ _hνic₁ _hμc₁ _hμν₁ rP₁ _hr₁ _hdist₁ ψf₁ _hψf₁ _hψjc₁ _hψhol₁ _hψK₁ _hψsm₁ _hψKu₁ _hνc₁ _hψdec₁ ψ₁ _hψ₁ _hψrep₁ em₁ τ₁ _hem₁ _hψlev₁ _hψty₁ ιP₂ μP₂ νP₂ _hμ₂ _hν₂ _hμic₂ _hνic₂ _hμc₂ _hμν₂ rP₂ _hr₂ _hdist₂ ψf₂ _hψf₂ _hψjc₂ _hψhol₂ _hψK₂ _hψsm₂ _hψKu₂ _hνc₂ _hψdec₂ ψ₂ _hψ₂ _hψrep₂ em₂ τ₂ _hem₂ _hψlev₂ _hψty₂

  obtain ⟨hθN₁, hθt₁⟩ := AutomorphicForm.pseudoEisenstein_principalLevel_and_mem_archCutSubmodule_of_paleyWiener_principalLevel_archCutSubmodule K α β hα hαβ ξK hξc hξt hξu N hN0 tysK hαm ιP₁ μP₁ νP₁ _hμ₁ _hν₁ _hμic₁ _hνic₁ _hμc₁ _hμν₁ rP₁ _hr₁ _hdist₁ ψf₁ _hψf₁ _hψjc₁ _hψhol₁ _hψK₁ _hψsm₁ _hψKu₁ _hνc₁ _hψdec₁ ψ₁ _hψ₁ _hψrep₁ _hψlev₁ _hψty₁
  obtain ⟨hθN₂, hθt₂⟩ := AutomorphicForm.pseudoEisenstein_principalLevel_and_mem_archCutSubmodule_of_paleyWiener_principalLevel_archCutSubmodule K α β hα hαβ ξK hξc hξt hξu N hN0 tysK hαm ιP₂ μP₂ νP₂ _hμ₂ _hν₂ _hμic₂ _hνic₂ _hμc₂ _hμν₂ rP₂ _hr₂ _hdist₂ ψf₂ _hψf₂ _hψjc₂ _hψhol₂ _hψK₂ _hψsm₂ _hψKu₂ _hνc₂ _hψdec₂ ψ₂ _hψ₂ _hψrep₂ _hψlev₂ _hψty₂

  obtain ⟨uc₁, ur₁, ue₁, huc₁, huc0₁, hur₁, hurc₁, hue₁, hueo₁, hsum₁, hlev₁, hcut₁, hae₁⟩ :=
    AutomorphicForm.exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab K α β hα hαβ ξK hξc hξt hξu N hN0 tysK ψ₁ _hψ₁ hθN₁ hθt₁ pψ₁ _hpψ₁ _hpψc₁ _hpψo₁
  obtain ⟨uc₂, ur₂, ue₂, huc₂, huc0₂, hur₂, hurc₂, hue₂, hueo₂, hsum₂, hlev₂, hcut₂, hae₂⟩ :=
    AutomorphicForm.exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab K α β hα hαβ ξK hξc hξt hξu N hN0 tysK ψ₂ _hψ₂ hθN₂ hθt₂ pψ₂ _hpψ₂ _hpψc₂ _hpψo₂

  obtain ⟨hmem₁, hsumm₁⟩ := AutomorphicForm.memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP₁ μP₁ νP₁ _hμ₁ _hν₁ _hμic₁ _hνic₁ _hμc₁ _hμν₁ rP₁ _hr₁ _hdist₁ ψf₁ _hψf₁ _hψjc₁ _hψhol₁ _hνc₁ _hψdec₁ ψ₁ _hψ₁ _hψrep₁ em₁ τ₁ _hem₁
  obtain ⟨hmem₂, hsumm₂⟩ := AutomorphicForm.memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP₂ μP₂ νP₂ _hμ₂ _hν₂ _hμic₂ _hνic₂ _hμc₂ _hμν₂ rP₂ _hr₂ _hdist₂ ψf₂ _hψf₂ _hψjc₂ _hψhol₂ _hνc₂ _hψdec₂ ψ₂ _hψ₂ _hψrep₂ em₂ τ₂ _hem₂
  exact ⟨ιP, instP, μP, νP, hμM, hνM, hμicM, hνicM, hμcM, hμνM, rP, hrM, hdistM, φf, ψf, hφfM, hψfM, hφjcM, hψjcM, hφholM, hψholM, hψKM, hψsmM, hψKuM, hνcM, hφdecM, hψdecM,
    ψ₁, ψ₂, _hψ₁, _hψ₂, hrep₁, hrep₂, em, τ, hemM,
    uc₁, ur₁, ue₁, huc₁, huc0₁, hur₁, hurc₁, hue₁, hueo₁, hsum₁,
    uc₂, ur₂, ue₂, huc₂, huc0₂, hur₂, hurc₂, hue₂, hueo₂, hsum₂,
    rfl, rfl, hlev₁, hcut₁, hlev₂, hcut₂, hae₁, hae₂, hmem₁, hsumm₁, hmem₂, hsumm₂⟩

end S_AutomorphicForm_exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener (solution)
