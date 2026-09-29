-- Prove2me | solution 1 for AutomorphicForm.flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4e9ae86b-227a-5b06-b81b-89ab3b5fa6b8

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
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology ContDiff

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws48
namespace C1
open AutomorphicForm NumberField NumberField.AdelicLevel NumberField.AdelicHaar MeasureTheory

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem diagOne_mem_adelicBorel (τ : (AdeleRing R K)ˣ) :
    (NumberField.AdelicLevel.diagOne τ : AdelicGL2 R K) ∈ adelicBorel R K := by
  show ((NumberField.AdelicLevel.diagOne τ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  simp

theorem apply_centralScalar_mul_diagOne_mul {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ} {φ : AdelicGL2 R K → ℂ}
    (hφ : IsInducedSection R K χ₁ χ₂ φ) (z τ : (AdeleRing R K)ˣ) (g : AdelicGL2 R K) :
    φ (centralScalar R K z * NumberField.AdelicLevel.diagOne τ * g) =
      ((χ₁ z : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) * ((χ₁ τ : ℂˣ) : ℂ) * φ g := by
  rw [mul_assoc, isInducedSection_centralScalar_mul hφ,
    hφ (NumberField.AdelicLevel.diagOne τ) (diagOne_mem_adelicBorel τ) g]
  have h1 : borelDiagFst (⟨NumberField.AdelicLevel.diagOne τ, diagOne_mem_adelicBorel τ⟩ : ↥(adelicBorel R K)) = τ := by
    refine Units.ext ?_
    rw [borelDiagFst_apply_val]
    show ((NumberField.AdelicLevel.diagOne τ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0 = τ
    rw [NumberField.AdelicLevel.diagOne_coe_apply]; simp
  have h2 : borelDiagSnd (⟨NumberField.AdelicLevel.diagOne τ, diagOne_mem_adelicBorel τ⟩ : ↥(adelicBorel R K)) = 1 := by
    refine Units.ext ?_
    rw [borelDiagSnd_apply_val]
    show ((NumberField.AdelicLevel.diagOne τ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1 = (1 : (AdeleRing R K)ˣ)
    rw [NumberField.AdelicLevel.diagOne_coe_apply]; simp
  rw [h1, h2, map_one, Units.val_one, mul_one]
  ring

theorem apply_mul_eq_of_mem_rationalTorusUnipotent (K : Type) [Field K] [NumberField K]
    {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ₁ : IsIdeleClassChar (𝓞 K) K χ₁) (hχ₂ : IsIdeleClassChar (𝓞 K) K χ₂)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) :
    ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, φ (x * g) = φ g := by

  let S : Subgroup (AdelicGL2 (𝓞 K) K) :=
    { carrier := {x | ∀ g : AdelicGL2 (𝓞 K) K, φ (x * g) = φ g}
      mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
      one_mem' := fun g => by rw [one_mul]
      inv_mem' := fun {a} ha g => by
        have := ha (a⁻¹ * g)
        rw [mul_inv_cancel_left] at this
        exact this.symm }

  have hglob : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (hγ : γ ∈ borelSubgroup K), globalPoints (𝓞 K) K γ ∈ S := by
    intro γ hγ g
    have hmem := globalPoints_mem_adelicBorel (𝓞 K) K hγ
    show φ (globalPoints (𝓞 K) K γ * g) = φ g
    rw [hφ _ hmem g, borelDiagFst_globalPoints (𝓞 K) K hγ hmem, borelDiagSnd_globalPoints (𝓞 K) K hγ hmem, hχ₁, hχ₂]
    simp
  have hS : rationalTorusUnipotent K ≤ S := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro x ⟨a, rfl⟩
      refine hglob _ ?_
      show ((Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 1 0 = 0
      simp
    · rintro x ⟨a, rfl⟩
      refine hglob _ ?_
      show ((NumberField.AdelicLevel.diagOne a : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
      rw [NumberField.AdelicLevel.diagOne_coe_apply]; simp
    · rintro x ⟨u, rfl⟩ g
      show φ (unipotentGL2Hom u * g) = φ g
      have hmem : (unipotentGL2Hom u : AdelicGL2 (𝓞 K) K) ∈ adelicBorel (𝓞 K) K := unipotentGL2_mem_borelSubgroup _
      rw [hφ _ hmem g]
      have e1 : borelDiagFst (⟨(unipotentGL2Hom u : AdelicGL2 (𝓞 K) K), hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = 1 := borelDiagFst_unipotentGL2 _
      have e2 : borelDiagSnd (⟨(unipotentGL2Hom u : AdelicGL2 (𝓞 K) K), hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = 1 := borelDiagSnd_unipotentGL2 _
      rw [e1, e2, map_one, map_one, Units.val_one, one_mul, one_mul]
  intro x hx g
  exact hS hx g

end Ws48.C1

theorem Ws48.C1.isPrincipalTrivial_modulus (K : Type) [Field K] [NumberField K] :
    AutomorphicForm.IsPrincipalTrivial (R := 𝓞 K) (K := K)
      (((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) := by
  intro u
  refine Units.ext ?_
  rw [MonoidHom.coe_toHomUnits, Units.val_one, MonoidHom.comp_apply]
  have h := @NumberField.AdeleRing.distribHaarChar_algebraMap K _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 K) K)
    (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K) u
  rw [show (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom u from rfl, h]
  simp

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
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
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
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK),
    ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ) (z y : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) =
          ((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) * ((μ (em i) y : ℂˣ) : ℂ) *
            ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) ^ (((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2) *
            φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K) ∧
      ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) =
          ((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) * ((ν (em i) y : ℂˣ) : ℂ) *
            ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) ^ (-((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2) *
            (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∧
      (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K,
        φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (x * g) = φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g ∧
          NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (x * g) = NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g)  := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP _ μP νP _hμ _hν _hμic _hνic _hμc _hμνP rP _hr _hdist ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνc _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty i j t z y k
  have hzα : ((((αm z : ℝˣ) : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (hαm z).ne'
  have hIy : ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) = (((αm y : ℝˣ) : ℝ) : ℂ) := rfl
  have hvol : ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos K).ne' (adelicAddHaar_adelicBox_lt_top K).ne).ne'

  have hind := ((AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
      K N tysK hαm (μ (em i)) (ν (em i)) (_hμE _) (_hνE _) (_hμicE _) (_hνicE _) (_hμcE _) (_hνcE _) (nE (em i)) (φE (em i))
      (_hφE (em i)) (_hφEK (em i)) (_hφEf (em i)) (_hφEjc (em i)) (_hφEhol (em i)) (_hφEKu (em i)) (_hφEflat (em i))
      (_hφElev (em i)) (_hφEty (em i)) (_hφEon (em i)) (OE (em i)) (EE (em i)) (NE (em i)) (_hEE (em i)) (t + τ i)).2 j).1

  have hprin : IsPrincipalTrivial (R := 𝓞 K) (K := K) αm := Ws48.C1.isPrincipalTrivial_modulus K
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [Ws48.C1.apply_centralScalar_mul_diagOne_mul (_hφE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) z y, _hφEflat (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) k,
      etaFst_apply, etaFst_apply, etaSnd_apply]
    simp only [Units.val_mul, cpowChar_apply_val]
    have hc : ((((αm z : ℝˣ) : ℝ) : ℂ)) ^ (((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2) * ((((αm z : ℝˣ) : ℝ) : ℂ)) ^ (-(((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2)) = 1 := by
      rw [← Complex.cpow_add _ _ hzα, add_neg_cancel, Complex.cpow_zero]
    rw [hIy]
    linear_combination (((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) * ((μ (em i) y : ℂˣ) : ℂ) *
      ((((αm y : ℝˣ) : ℝ) : ℂ)) ^ (((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2) * φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)) * hc
  ·
    have hb := Ws48.C1.apply_centralScalar_mul_diagOne_mul hind z y (k : AdelicGL2 (𝓞 K) K)
    beta_reduce at hb
    rw [hb, etaFst_apply, etaFst_apply, etaSnd_apply]
    simp only [Units.val_mul, cpowChar_apply_val]
    have hc : ((((αm z : ℝˣ) : ℝ) : ℂ)) ^ (-((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2) * ((((αm z : ℝˣ) : ℝ) : ℂ)) ^ (-(-((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2)) = 1 := by
      rw [← Complex.cpow_add _ _ hzα, add_neg_cancel, Complex.cpow_zero]
    rw [hIy]
    linear_combination (((ν (em i) z : ℂˣ) : ℂ) * ((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) y : ℂˣ) : ℂ) *
      ((((αm y : ℝˣ) : ℝ) : ℂ)) ^ (-((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2) *
      (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) * hc
  ·
    intro x hx g
    have h1 := Ws48.C1.apply_mul_eq_of_mem_rationalTorusUnipotent K
      (etaFst_isIdeleClassChar (_hμicE (em i)) hprin ((((t + τ i : ℝ) : ℂ)) * Complex.I)) (etaSnd_isIdeleClassChar (_hνicE (em i)) hprin ((((t + τ i : ℝ) : ℂ)) * Complex.I))
      (_hφE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x hx g
    have h2 := Ws48.C1.apply_mul_eq_of_mem_rationalTorusUnipotent K
      (etaFst_isIdeleClassChar (_hνicE (em i)) hprin (-((((t + τ i : ℝ) : ℂ)) * Complex.I))) (etaSnd_isIdeleClassChar (_hμicE (em i)) hprin (-((((t + τ i : ℝ) : ℂ)) * Complex.I)))
      hind x hx g
    beta_reduce at h2
    exact ⟨h1, mul_left_cancel₀ (inv_ne_zero hvol) h2⟩

end S_AutomorphicForm_flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener (solution)
