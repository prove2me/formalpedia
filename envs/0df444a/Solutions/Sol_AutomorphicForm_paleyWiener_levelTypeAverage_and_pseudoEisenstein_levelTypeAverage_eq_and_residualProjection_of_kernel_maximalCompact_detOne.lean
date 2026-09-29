-- Prove2me | solution 1 for AutomorphicForm.paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a00b1777-cb19-55e8-9d32-ae4cdcdefe9f

import Theorems.Thm_AutomorphicForm_paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne
import Theorems.Thm_AutomorphicForm_isSlabProfile_levelTypeAverage_and_eq_sum_integral_of_kernel_maximalCompact
import Theorems.Thm_AutomorphicForm_levelTypeAverage_pseudoEisenstein_eq_pseudoEisenstein_levelTypeAverage_of_isSlabProfile
import Theorems.Thm_AutomorphicForm_ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Definitions.Def_AutomorphicForm_AdelicLsXi
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec"

set_option autoImplicit false

section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne.AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne ArchTypeFamily archCutSubmodule CarrierPins productionPinsOf AdelicGL2 IsIdeleClassChar IsUnitaryChar IsLsXiFunction finiteAdelicGL2Subgroup IsKfSmooth lsXiMemberAt_iff IsAutomorphicFnAt canonicalTruncationDomain IsInducedSection etaFst etaSnd IsSlabProfile pseudoEisenstein adelicMaximalCompact maximalCompactHaar archRowIsometrySubgroup IsArchKFinite residualSpan isSlabProfile_levelTypeAverage_and_eq_sum_integral_of_kernel_maximalCompact levelTypeAverage_pseudoEisenstein_eq_pseudoEisenstein_levelTypeAverage_of_isSlabProfile ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact isAutomorphicFnAt_pseudoEisenstein_slab canonicalTruncationData_isTruncationDatum"
namespace LsXiAvgPW
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private abbrev pins (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private theorem isLsXiFunction_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ u :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).1 hu).1

private theorem memLp_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).1 hu).2

private theorem isAutomorphicFnAt_of_isLsXiFunction_of_memLp (Φ : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ) (h1 : IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ u)
    (h2 : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) : IsAutomorphicFnAt F (pins F Φ) ξ u :=
  (lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).2 ⟨h1, h2⟩

section Alg
variable (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)

private theorem isAutomorphicFnAt_add (v w : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v)
    (hw : IsAutomorphicFnAt F (pins F Φ) ξ w) : IsAutomorphicFnAt F (pins F Φ) ξ (v + w) := by
  have hvL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ v hv
  have hwL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ w hw
  refine isAutomorphicFnAt_of_isLsXiFunction_of_memLp F Φ ξ _ ⟨fun γ g => ?_, fun z g => ?_⟩
    ((memLp_of_isAutomorphicFnAt F Φ ξ v hv).add (memLp_of_isAutomorphicFnAt F Φ ξ w hw))
  · simp only [Pi.add_apply, hvL.left_invariant, hwL.left_invariant]
  · simp only [Pi.add_apply, hvL.central_transform, hwL.central_transform, mul_add]

private theorem isAutomorphicFnAt_smul (c : ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v) :
    IsAutomorphicFnAt F (pins F Φ) ξ (c • v) := by
  have hvL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ v hv
  refine isAutomorphicFnAt_of_isLsXiFunction_of_memLp F Φ ξ _ ⟨fun γ g => ?_, fun z g => ?_⟩
    ((memLp_of_isAutomorphicFnAt F Φ ξ v hv).const_smul c)
  · simp only [Pi.smul_apply, hvL.left_invariant]
  · simp only [Pi.smul_apply, hvL.central_transform, smul_eq_mul]
    ring

private theorem isAutomorphicFnAt_sub (v w : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v)
    (hw : IsAutomorphicFnAt F (pins F Φ) ξ w) : IsAutomorphicFnAt F (pins F Φ) ξ (v - w) := by
  have h := isAutomorphicFnAt_add F Φ ξ v ((-1 : ℂ) • w) hv (isAutomorphicFnAt_smul F Φ ξ (-1) w hw)
  have heq : v + (-1 : ℂ) • w = v - w := by
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [heq] at h
  exact h

end Alg

end AutomorphicForm.LsXiAvgPW

end

end

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne.AutomorphicForm"

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
      (_hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
        P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      (_hPrange : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        Continuous (P φ) ∧ IsArchKFinite K (P φ) ∧ (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, (P φ) (g * u) = (P φ) g) ∧ P φ ∈ archCutSubmodule K tysK)
      (_hPcomm : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (k : ↥(adelicMaximalCompact K)),
        (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
        ∀ g : AdelicGL2 (𝓞 K) K, P (fun x => φ (x * (k : AdelicGL2 (𝓞 K) K))) g = P φ (g * (k : AdelicGL2 (𝓞 K) K)))
      (_hPaut : ∀ φ ψ : AdelicGL2 (𝓞 K) K → ℂ,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ → IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ψ →
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (P φ) ∧
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, P φ g * conj (ψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, φ g * conj (P ψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
      (_hPres : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        P h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK)
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
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g),
    (∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (P (ψf e s))) ∧
    (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => P (ψf e p.1) p.2)) ∧
    (∀ e g, Differentiable ℂ (fun s => P (ψf e s) g)) ∧
    (∀ e s, IsArchKFinite K (P (ψf e s))) ∧
    (∀ e s, IsKfSmooth K (P (ψf e s))) ∧
    (∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => P (ψf e s) (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
    (∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖P (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g‖ ≤ m t) ∧
    (AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK (P ψ)) ∧
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        P ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, P (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g) ∧
    (∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, P (ψf i s) (g * u) = P (ψf i s) g) ∧
    (∀ i (s : ℂ), P (ψf i s) ∈ archCutSubmodule K tysK) ∧
    AutomorphicForm.pseudoEisenstein K (P ψ) = P (AutomorphicForm.pseudoEisenstein K ψ) ∧
    (∀ p : AdelicGL2 (𝓞 K) K → ℂ,
      (IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p ∧
        (∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (p - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) ∧
        (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (AutomorphicForm.pseudoEisenstein K ψ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)) →
      (IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (P p) ∧
        (∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm ((P p) - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) ∧
        (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (AutomorphicForm.pseudoEisenstein K (P ψ) g - (P p) g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0))) := by
  intro αm hαm κ hκ P hP hPrange hPcomm hPaut hPres ιP instP μP νP hμ hν hμic hνic hμc hμν rP hr hdist
    ψf hψf hψjc hψhol hψK hψsm hψKu hνc hψdec ψ hψ hψrep
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, alev, aty⟩ :=
    AutomorphicForm.paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne K N tysK hαm κ hκ P hP hPrange hPcomm ιP μP νP
      ψf hψf hψjc hψhol hψK hψsm hψKu hνc hψdec
  obtain ⟨bslab, brep⟩ :=
    AutomorphicForm.isSlabProfile_levelTypeAverage_and_eq_sum_integral_of_kernel_maximalCompact K α β hα hαβ ξK hξc hξt hξu N tysK hαm κ hκ P hP
      ιP μP νP hμ hν hμic hνic hμc hμν rP hr hdist ψf hψf hψjc hψhol hψK hψsm hψKu hνc hψdec ψ hψ hψrep
  have hC : AutomorphicForm.pseudoEisenstein K (P ψ) = P (AutomorphicForm.pseudoEisenstein K ψ) :=
    funext fun g => AutomorphicForm.levelTypeAverage_pseudoEisenstein_eq_pseudoEisenstein_levelTypeAverage_of_isSlabProfile K _ ξK (fun z => hξu z) κ hκ P hP ψ hψ g
  refine ⟨a1, a2, a3, a4, a5, a6, a7, bslab, brep, alev, aty, hC, ?_⟩
  rintro p ⟨hp, hpc, hpo⟩
  obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hθ : IsAutomorphicFnAt K (AutomorphicForm.LsXiAvgPW.pins K (AutomorphicForm.canonicalTruncationDomain K α β)) ξK
      (AutomorphicForm.pseudoEisenstein K ψ) :=
    AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ _ hΦs hΦ ξK ψ hψ
  have hPD := fun (φ₁ φ₂ : AdelicGL2 (𝓞 K) K → ℂ) (h₁ : IsAutomorphicFnAt K (AutomorphicForm.LsXiAvgPW.pins K (AutomorphicForm.canonicalTruncationDomain K α β)) ξK φ₁)
      (h₂ : IsAutomorphicFnAt K (AutomorphicForm.LsXiAvgPW.pins K (AutomorphicForm.canonicalTruncationDomain K α β)) ξK φ₂) =>
    AutomorphicForm.ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact K α β hα hαβ ξK hξc hξt hξu κ hκ P hP φ₁ φ₂ h₁ h₂
  refine ⟨(hPaut p p hp hp).1, ?_, ?_⟩
  ·
    intro ε hε
    set C : ℝ := ∫ k, ‖κ k‖ ∂(maximalCompactHaar K) with hCdef
    have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
    have hε' : 0 < ε / (C + 1) := div_pos hε (by linarith)
    obtain ⟨r, hr, hra, hlt⟩ := hpc (ε / (C + 1)) hε'
    refine ⟨P r, hPres r hra hr, (hPaut r r hra hra).1, ?_⟩
    have hsub := AutomorphicForm.LsXiAvgPW.isAutomorphicFnAt_sub K _ ξK p r hp hra
    obtain ⟨-, hlin, -⟩ := hPD p r hp hra
    obtain ⟨-, -, hbd⟩ := hPD (p - r) p hsub hp
    have hae : (P p - P r) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)]
        P (p - r) := by
      filter_upwards [hlin] with g hg
      rw [Pi.sub_apply, hg]
    rw [eLpNorm_congr_ae hae]
    refine lt_of_le_of_lt hbd ?_
    refine lt_of_le_of_lt (mul_le_mul_right hlt.le _) ?_
    rw [← ENNReal.ofReal_mul hC0, ENNReal.ofReal_lt_ofReal_iff hε]
    have h1 : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
    rw [h1]
    have h2 : C / (C + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    nlinarith
  ·
    intro h hh hres
    rw [hC]
    have hsub := AutomorphicForm.LsXiAvgPW.isAutomorphicFnAt_sub K _ ξK _ p hθ hp
    obtain ⟨-, hlin, -⟩ := hPD (AutomorphicForm.pseudoEisenstein K ψ) p hθ hp
    have hae : (fun g => (P (AutomorphicForm.pseudoEisenstein K ψ) g - P p g) * conj (h g))
        =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)]
        (fun g => P (AutomorphicForm.pseudoEisenstein K ψ - p) g * conj (h g)) := by
      filter_upwards [hlin] with g hg
      rw [hg]
    rw [integral_congr_ae hae, (hPaut _ h hsub hh).2]
    have := hpo (P h) (hPaut h h hh hh).1 (hPres h hh hres)
    simpa only [Pi.sub_apply] using this

end S_AutomorphicForm_paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne
end P2MW
export P2MW.S_AutomorphicForm_paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne (solution)
