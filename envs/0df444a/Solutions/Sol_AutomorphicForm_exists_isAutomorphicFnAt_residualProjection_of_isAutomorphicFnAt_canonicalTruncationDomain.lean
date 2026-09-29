-- Prove2me | solution 1 for AutomorphicForm.exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f4378a92-ca01-5c32-b89a-385af3284fce

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
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_AutomorphicForm_exists_isAutomorphicFnAt_ae_eq_of_tendsto_eLpNorm_and_ae_constantTerm_eq_zero_canonicalTruncationDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain.AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CarrierPins productionPinsOf AdelicGL2 IsLsXiFunction finiteAdelicGL2Subgroup lsXiMemberAt_iff IsAutomorphicFnAt isAutomorphicFnAt_zero unipotentGL2 constantTermIntegrand constantTerm canonicalTruncationDomain residualSpan exists_isAutomorphicFnAt_ae_eq_of_tendsto_eLpNorm_and_ae_constantTerm_eq_zero_canonicalTruncationDomain"
namespace LsXiResProj
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

section Hilbert

variable (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)

private def CuspAE (v : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v g = 0

private theorem cuspAE_congr {v w : AdelicGL2 (𝓞 F) F → ℂ} (h : v = w) (hv : CuspAE F Φ v) : CuspAE F Φ w :=
  h ▸ hv

private def HCTlin : Prop :=
  ∀ (v₁ v₂ : AdelicGL2 (𝓞 F) F → ℂ) (c₁ c₂ : ℂ), IsAutomorphicFnAt F (pins F Φ) ξ v₁ →
    IsAutomorphicFnAt F (pins F Φ) ξ v₂ → CuspAE F Φ v₁ → CuspAE F Φ v₂ →
    CuspAE F Φ (fun g => c₁ * v₁ g + c₂ * v₂ g)

private def HComplete : Prop :=
  ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
    (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) →
    MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) →
    Filter.Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
      Filter.atTop (nhds 0) →
    ∃ U, IsAutomorphicFnAt F (pins F Φ) ξ U ∧ U =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v

private def HClosed : Prop :=
  ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
    (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) → (∀ n, CuspAE F Φ (useq n)) →
    IsAutomorphicFnAt F (pins F Φ) ξ v →
    Filter.Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
      Filter.atTop (nhds 0) →
    CuspAE F Φ v

private theorem isAutomorphicFnAt_zero : IsAutomorphicFnAt F (pins F Φ) ξ 0 :=
  isAutomorphicFnAt_of_isLsXiFunction_of_memLp F Φ ξ 0
    ⟨fun _ _ => rfl, fun _ _ => by simp only [Pi.zero_apply, mul_zero]⟩ MemLp.zero'

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

private theorem inner_eq_setIntegral (φ ψ : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
    (v w : AdelicGL2 (𝓞 F) F → ℂ)
    (hv : (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v)
    (hw : (ψ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] w) :
    inner ℂ ψ φ = ∫ g in Φ, v g * (starRingEnd ℂ) (w g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hv, hw] with g hgv hgw
  rw [RCLike.inner_apply, hgv, hgw]

private def cuspSubmodule (hCTlin : HCTlin F Φ ξ) :
    Submodule ℂ (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) where
  carrier := {φ | ∃ v : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ v ∧ CuspAE F Φ v ∧
    (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v}
  zero_mem' := ⟨0, isAutomorphicFnAt_zero F Φ ξ,
    Filter.Eventually.of_forall fun g => by simp [constantTerm, constantTermIntegrand], Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro φ ψ ⟨v, hv, hvc, hφv⟩ ⟨w, hw, hwc, hψw⟩
    refine ⟨v + w, isAutomorphicFnAt_add F Φ ξ v w hv hw, ?_, (Lp.coeFn_add φ ψ).trans (hφv.add hψw)⟩
    have h := hCTlin v w 1 1 hv hw hvc hwc
    have heq : (fun g => (1 : ℂ) * v g + 1 * w g) = v + w := by funext g; simp only [one_mul, Pi.add_apply]
    rw [heq] at h
    exact h
  smul_mem' := by
    rintro c φ ⟨v, hv, hvc, hφv⟩
    refine ⟨c • v, isAutomorphicFnAt_smul F Φ ξ c v hv, ?_,
      (Lp.coeFn_smul c φ).trans (hφv.mono fun g hg => by simp only [Pi.smul_apply, hg])⟩
    have h := hCTlin v v c 0 hv hv hvc hvc
    have heq : (fun g => c * v g + 0 * v g) = c • v := by
      funext g; simp only [zero_mul, add_zero, Pi.smul_apply, smul_eq_mul]
    rw [heq] at h
    exact h

private theorem mem_cuspSubmodule_iff (hCTlin : HCTlin F Φ ξ)
    (φ : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) :
    φ ∈ cuspSubmodule F Φ ξ hCTlin ↔ ∃ v : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ v ∧
      CuspAE F Φ v ∧ (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v :=
  Iff.rfl

private theorem isClosed_cuspSubmodule
    (hcomplete : HComplete F Φ ξ) (hclosed : HClosed F Φ ξ) (hCTlin : HCTlin F Φ ξ) :
    IsClosed (cuspSubmodule F Φ ξ hCTlin : Set (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))) := by
  refine IsSeqClosed.isClosed ?_
  intro x xlim hx hconv
  have hx' : ∀ n, ∃ v : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ v ∧ CuspAE F Φ v ∧
      ((x n : Lp ℂ 2 _) : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v :=
    fun n => hx n
  choose v hv hvc hxv using hx'
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' x xlim).1 hconv
  have h2 : Filter.Tendsto (fun n => eLpNorm (v n - (xlim : AdelicGL2 (𝓞 F) F → ℂ)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) Filter.atTop (nhds 0) := by
    refine (Filter.tendsto_congr fun n => ?_).1 h1
    exact eLpNorm_congr_ae ((hxv n).sub Filter.EventuallyEq.rfl)
  obtain ⟨U, hU, hUx⟩ := hcomplete v xlim hv (Lp.memLp xlim) h2
  have h3 : Filter.Tendsto (fun n => eLpNorm (v n - U) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
      Filter.atTop (nhds 0) := by
    refine (Filter.tendsto_congr fun n => ?_).1 h2
    exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hUx.symm)
  exact ⟨U, hU, hclosed v U hv hvc hU h3, hUx.symm⟩

private def resSubmodule : Submodule ℂ (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) where
  carrier := {φ | ∃ r : AdelicGL2 (𝓞 F) F → ℂ, r ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ ∧
    IsAutomorphicFnAt F (pins F Φ) ξ r ∧
    (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] r}
  zero_mem' := ⟨0, Submodule.zero_mem _, isAutomorphicFnAt_zero F Φ ξ, Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro φ ψ ⟨r, hr, hra, hφr⟩ ⟨s, hs, hsa, hψs⟩
    exact ⟨r + s, Submodule.add_mem _ hr hs, isAutomorphicFnAt_add F Φ ξ r s hra hsa,
      (Lp.coeFn_add φ ψ).trans (hφr.add hψs)⟩
  smul_mem' := by
    rintro c φ ⟨r, hr, hra, hφr⟩
    exact ⟨c • r, Submodule.smul_mem _ c hr, isAutomorphicFnAt_smul F Φ ξ c r hra,
      (Lp.coeFn_smul c φ).trans (hφr.mono fun g hg => by simp only [Pi.smul_apply, hg])⟩

private theorem mem_resSubmodule_iff (φ : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) :
    φ ∈ resSubmodule F Φ ξ ↔ ∃ r : AdelicGL2 (𝓞 F) F → ℂ, r ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ ∧
      IsAutomorphicFnAt F (pins F Φ) ξ r ∧
      (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] r :=
  Iff.rfl

end Hilbert

theorem exists_resProj (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    (hcomplete : HComplete F Φ ξ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsAutomorphicFnAt F (pins F Φ) ξ f) :
    ∃ p : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ p ∧
      (∀ ε > (0:ℝ), ∃ r ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ,
        IsAutomorphicFnAt F (pins F Φ) ξ r ∧
          eLpNorm (p - r) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) < ENNReal.ofReal ε) ∧
      (∀ h : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ h →
        h ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ →
        ∫ g in Φ, (f g - p g) * (starRingEnd ℂ) (h g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0) := by
  let B := (resSubmodule F Φ ξ).topologicalClosure
  haveI : CompleteSpace B := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hfM := memLp_of_isAutomorphicFnAt F Φ ξ f hf
  let fL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := hfM.toLp f
  have hfL : (fL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] f := hfM.coeFn_toLp
  let b : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := ↑(B.orthogonalProjection fL)
  have hbB : b ∈ B := (B.orthogonalProjection fL).2
  have hbB' : fL - b ∈ Bᗮ := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := B) fL
    rwa [Submodule.starProjection_apply] at h
  have hbcl : b ∈ closure (resSubmodule F Φ ξ : Set (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))) := by
    rw [← Submodule.topologicalClosure_coe]; exact hbB
  obtain ⟨ψ, hψ, hψb⟩ := mem_closure_iff_seq_limit.1 hbcl
  have hψ' : ∀ n, ∃ r : AdelicGL2 (𝓞 F) F → ℂ, r ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ ∧
      IsAutomorphicFnAt F (pins F Φ) ξ r ∧
      ((ψ n : Lp ℂ 2 _) : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] r :=
    fun n => hψ n
  choose rseq hrs hra hψr using hψ'
  have hb1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' ψ b).1 hψb
  have hb2 : Filter.Tendsto (fun n => eLpNorm (rseq n - (b : AdelicGL2 (𝓞 F) F → ℂ)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) Filter.atTop (nhds 0) := by
    refine (Filter.tendsto_congr fun n => ?_).1 hb1
    exact eLpNorm_congr_ae ((hψr n).sub Filter.EventuallyEq.rfl)
  obtain ⟨p, hp, hbp⟩ := hcomplete rseq b hra (Lp.memLp b) hb2
  refine ⟨p, hp, ?_, ?_⟩
  · intro ε hε
    obtain ⟨φ, hφ, hdist⟩ := Metric.mem_closure_iff.1 hbcl ε hε
    obtain ⟨r, hr, hrauto, hφr⟩ := hφ
    refine ⟨r, hr, hrauto, ?_⟩
    have hne : eLpNorm ((b : AdelicGL2 (𝓞 F) F → ℂ) - (φ : AdelicGL2 (𝓞 F) F → ℂ)) 2
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) ≠ ⊤ := ((Lp.memLp b).sub (Lp.memLp φ)).eLpNorm_ne_top
    have heq : eLpNorm (p - r) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) =
        eLpNorm ((b : AdelicGL2 (𝓞 F) F → ℂ) - (φ : AdelicGL2 (𝓞 F) F → ℂ)) 2
          ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
      eLpNorm_congr_ae (hbp.sub hφr.symm)
    rw [heq, ENNReal.lt_ofReal_iff_toReal_lt hne, ← Lp.dist_def]
    exact hdist
  · intro h hh hres
    have hhM := memLp_of_isAutomorphicFnAt F Φ ξ h hh
    let hL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := hhM.toLp h
    have hhL : (hL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] h := hhM.coeFn_toLp
    have hfpL : ((fL - b : Lp ℂ 2 _) : AdelicGL2 (𝓞 F) F → ℂ)
        =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] (f - p) :=
      (Lp.coeFn_sub _ _).trans (hfL.sub hbp.symm)
    have key := inner_eq_setIntegral F Φ (fL - b) hL (f - p) h hfpL hhL
    simp only [Pi.sub_apply] at key
    rw [← key]
    have hhB : hL ∈ B := Submodule.le_topologicalClosure _ ⟨h, hres, hh, hhL⟩
    exact Submodule.inner_right_of_mem_orthogonal hhB hbB'

end AutomorphicForm.LsXiResProj

end

end

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain.AutomorphicForm"

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (_hf : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f) :
    letI := adeleBorel (𝓞 K) K
    ∃ (p : AdelicGL2 (𝓞 K) K → ℂ),
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
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
            (f g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) := by
  exact AutomorphicForm.LsXiResProj.exists_resProj K (AutomorphicForm.canonicalTruncationDomain K α β) ξK
    (AutomorphicForm.exists_isAutomorphicFnAt_ae_eq_of_tendsto_eLpNorm_and_ae_constantTerm_eq_zero_canonicalTruncationDomain
      K α β hα hαβ ξK hξc hξu).1 f _hf

end S_AutomorphicForm_exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain (solution)
