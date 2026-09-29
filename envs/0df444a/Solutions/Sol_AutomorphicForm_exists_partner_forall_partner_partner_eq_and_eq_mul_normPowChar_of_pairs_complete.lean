-- Prove2me | solution 1 for AutomorphicForm.exists_partner_forall_partner_partner_eq_and_eq_mul_normPowChar_of_pairs_complete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4bdcc4ed-1dd4-5ec8-8fbf-cdfc9376450c

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
import Theorems.Thm_AutomorphicForm_orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_partner_forall_partner_partner_eq_and_eq_mul_normPowChar_of_pairs_complete
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm in
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
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g)),
    ∃ (prt : ιE → ιE) (σ : ιE → ℝ), ∀ e : ιE, 0 < nE e →
      prt (prt e) = e ∧
      μ (prt e) = ν e * NumberField.TateGlobal.normPowChar K (σ e) ∧
      ν (prt e) = μ e * (NumberField.TateGlobal.normPowChar K (σ e))⁻¹  := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE
  classical

  obtain ⟨Rel, hRel⟩ : ∃ Rel : ιE → ιE → Prop,
      Rel = fun e e' => ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e' z = ν e z ∧ ν e' z = μ e z := ⟨_, rfl⟩
  have hsymm : ∀ e e', Rel e e' → Rel e' e := by
    intro e e' h
    rw [hRel] at h ⊢
    intro z hz
    exact ⟨(h z hz).2.symm, (h z hz).1.symm⟩
  have huniq : ∀ e e₁ e₂, Rel e e₁ → Rel e e₂ → e₁ = e₂ := by
    intro e e₁ e₂ h1 h2
    by_contra hne
    obtain ⟨z, hz, hz'⟩ := _hdistE e₁ e₂ hne
    rw [hRel] at h1 h2
    rcases hz' with h | h
    · exact h ((h1 z hz).1.trans (h2 z hz).1.symm)
    · exact h ((h1 z hz).2.trans (h2 z hz).2.symm)
  let prt : ιE → ιE := fun e => if h : ∃ e', Rel e e' then h.choose else e
  have hprt : ∀ e e', Rel e e' → prt e = e' := by
    intro e e' h
    have hex : ∃ e', Rel e e' := ⟨e', h⟩
    simp only [prt, dif_pos hex]
    exact huniq e _ _ hex.choose_spec h

  have hexists : ∀ e, 0 < nE e → ∃ e', Rel e e' := by
    intro e he
    obtain ⟨hon, hadm⟩ :=
      AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
        K N tysK hαm (μ e) (ν e) (_hμE e) (_hνE e) (_hμicE e) (_hνicE e) (_hμcE e) (_hνcE e) (nE e) (φE e) (_hφE e)
        (_hφEK e) (_hφEf e) (_hφEjc e) (_hφEhol e) (_hφEKu e) (_hφEflat e) (_hφElev e) (_hφEty e) (_hφEon e)
        (OE e) (EE e) (NE e) (_hEE e) 0
    obtain ⟨hind, hcont, hKf, hlev, hty, -⟩ := hadm ⟨0, he⟩
    have e0 : (-(((0 : ℝ) : ℂ) * Complex.I)) = (((0 : ℝ) : ℂ) * Complex.I) := by simp
    rw [e0] at hind
    have hne : (fun g : AdelicGL2 (𝓞 K) K =>
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e ⟨0, he⟩ (((0 : ℝ) : ℂ) * Complex.I) g) ≠ 0 := by
      intro h0
      have h1 := hon ⟨0, he⟩ ⟨0, he⟩
      rw [if_pos rfl, h0] at h1
      simp at h1
    obtain ⟨e', he'⟩ := _hpairs (ν e) (μ e) (_hνE e) (_hμE e) (_hνicE e) (_hμicE e) (_hνcE e) (_hμcE e)
      (fun z => by rw [mul_comm]; exact _hμν e z) 0 _ hind hcont hKf hlev hty hne
    refine ⟨e', ?_⟩
    rw [hRel]
    exact he'

  have hcontU : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsUnitaryChar (𝓞 K) K χ →
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) → Continuous χ := by
    intro χ hu hc
    refine Units.continuous_iff.2 ⟨hc, ?_⟩
    have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z)⁻¹ : ℂˣ).val) = fun z => (((χ z : ℂˣ) : ℂ))⁻¹ := by
      funext z; rw [Units.val_inv_eq_inv_val]
    rw [this]
    exact hc.inv₀ fun z => Units.ne_zero _

  have hσex : ∀ e, 0 < nE e → ∃ σ : ℝ, μ (prt e) = ν e * NumberField.TateGlobal.normPowChar K σ := by
    intro e he
    obtain ⟨e', hee'⟩ := hexists e he
    rw [hprt e e' hee']
    have hc' : Continuous (μ e' * (ν e)⁻¹) := by
      have h1 := hcontU (μ e') (_hμE e') (_hμcE e')
      have h2 := hcontU (ν e) (_hνE e) (_hνcE e)
      have : ((μ e' * (ν e)⁻¹ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : (AdeleRing (𝓞 K) K)ˣ → ℂˣ) =
          fun z => μ e' z * (ν e z)⁻¹ := by
        funext z; rw [MonoidHom.mul_apply, MonoidHom.inv_apply]
      rw [this]
      exact h1.mul h2.inv
    have hu' : IsUnitaryChar (𝓞 K) K (μ e' * (ν e)⁻¹) := by
      intro z
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
        _hμE e' z, _hνE e z, inv_one, mul_one]
    have ht' : ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, (μ e' * (ν e)⁻¹) z = 1 := by
      intro z hz
      rw [hRel] at hee'
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, (hee' z hz).1, mul_inv_cancel]
    obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles K _ hc' hu' ht'
    refine ⟨σ, MonoidHom.ext fun z => ?_⟩
    have hz := DFunLike.congr_fun hσ z
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply] at hz
    rw [MonoidHom.mul_apply, ← hz, mul_comm, inv_mul_cancel_right]
  let σf : ιE → ℝ := fun e => if h : 0 < nE e then (hσex e h).choose else 0
  refine ⟨prt, σf, fun e he => ?_⟩
  obtain ⟨e', hee'⟩ := hexists e he
  have hpe : prt e = e' := hprt e e' hee'
  have hσ : μ (prt e) = ν e * NumberField.TateGlobal.normPowChar K (σf e) := by
    have : σf e = (hσex e he).choose := by simp only [σf, dif_pos he]
    rw [this]
    exact (hσex e he).choose_spec
  refine ⟨?_, hσ, ?_⟩
  · rw [hpe]
    exact hprt e' e (hsymm e e' hee')
  · refine MonoidHom.ext fun z => Units.ext ?_
    have h1 := congrArg Units.val (_hμν e z)
    have h2 := congrArg Units.val (_hμν (prt e) z)
    have h3 := congrArg Units.val (DFunLike.congr_fun hσ z)
    rw [Units.val_mul] at h1 h2
    rw [MonoidHom.mul_apply, Units.val_mul] at h3
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    have hν0 : ((ν e z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hn0 : ((NumberField.TateGlobal.normPowChar K (σf e) z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have key : ((ν e z : ℂˣ) : ℂ) * (NumberField.TateGlobal.normPowChar K (σf e) z : ℂ) * (ν (prt e) z : ℂ) =
        (μ e z : ℂ) * (ν e z : ℂ) := by rw [← h3, h2, h1]
    field_simp
    have key2 : (NumberField.TateGlobal.normPowChar K (σf e) z : ℂ) * (ν (prt e) z : ℂ) = (μ e z : ℂ) := by
      have := key
      have hcomm : ((ν e z : ℂˣ) : ℂ) * (NumberField.TateGlobal.normPowChar K (σf e) z : ℂ) * (ν (prt e) z : ℂ) =
          (ν e z : ℂ) * ((NumberField.TateGlobal.normPowChar K (σf e) z : ℂ) * (ν (prt e) z : ℂ)) := by ring
      rw [hcomm, mul_comm ((μ e z : ℂˣ) : ℂ)] at this
      exact mul_left_cancel₀ hν0 this
    linear_combination key2

end S_AutomorphicForm_exists_partner_forall_partner_partner_eq_and_eq_mul_normPowChar_of_pairs_complete
end P2MW
export P2MW.S_AutomorphicForm_exists_partner_forall_partner_partner_eq_and_eq_mul_normPowChar_of_pairs_complete (solution)
