-- Prove2me | solution 1 for AutomorphicForm.levelTypeAverage_ae_eq_self_of_isAutomorphicFnAt_of_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/06c4fab3-170c-5755-9213-3a10df35561b

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
import Mathlib
import Theorems.Thm_AutomorphicForm_exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_levelTypeAverage_ae_eq_self_of_isAutomorphicFnAt_of_mem_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped ENNReal

noncomputable section

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    ∀ (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (_hfix : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ → (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tysK →
        (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          φ (g * centralScalar (𝓞 K) K z) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g) →
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = φ)
      (v : AdelicGL2 (𝓞 K) K → ℂ)
      (_hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v)
      (_hvN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g)
      (_hvt : v ∈ archCutSubmodule K tysK),
    (fun g => ∫ k, κ k * v (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] v := by
  intro κ hκ hfix v hv hvN hvt

  set μ0 : Measure (AdelicGL2 (𝓞 K) K) :=
    (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) with hμ0
  set P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
    fun φ g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hP
  set c : ℝ := ∫ k, ‖κ k‖ ∂(maximalCompactHaar K) with hc
  have hc0 : 0 ≤ c := integral_nonneg fun _ => norm_nonneg _
  have AVR := AutomorphicForm.isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact
    K α β hα hαβ ξK κ hκ

  have hPv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
      (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK (P v) :=
    (AVR v v hv hv).2.2.2.1
  have hv2 : MemLp v 2 μ0 := ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hv).2
  have hPv2 : MemLp (P v) 2 μ0 := ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hPv).2

  have key : ∀ ε : ℝ, 0 < ε → eLpNorm (P v - v) 2 μ0 ≤ ENNReal.ofReal ((c + 1) * ε) := by
    intro ε hε
    obtain ⟨w, hw, hwc, hwK, hwN, hwt, hvw⟩ :=
      AutomorphicForm.exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt
        K α β hα hαβ ξK hξc hξt hξu N hN tysK v hv hvN hvt ε hε
    have hwL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hw
    have hw2 : MemLp w 2 μ0 := hwL.2

    have hwz : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        w (g * centralScalar (𝓞 K) K z) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * w g := by
      intro z g
      rw [mul_centralScalar_comm]
      exact hwL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
    have hPw : P w = w := hfix w hwc hwK hwN hwt hwz

    have hvw_aut : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
        (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        ξK (v - w) := by
      refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hv2.sub hw2⟩
      · simp only [Pi.sub_apply, ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hv).1.left_invariant γ g, hwL.1.left_invariant γ g]
      · simp only [Pi.sub_apply, ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hv).1.central_transform z g,
          hwL.1.central_transform z g, mul_sub]
    have hlin : ∀ᵐ g ∂μ0, P (v - w) g = P v g - P w g := (AVR v w hv hw).2.2.1
    have hcontr : eLpNorm (P (v - w)) 2 μ0 ≤ ENNReal.ofReal c * eLpNorm (v - w) 2 μ0 :=
      (AVR (v - w) (v - w) hvw_aut hvw_aut).2.2.2.2
    have hPvw2 : MemLp (P (v - w)) 2 μ0 :=
      ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 (AVR (v - w) (v - w) hvw_aut hvw_aut).2.2.2.1).2

    have hdecomp : (P v - v) =ᵐ[μ0] (P (v - w)) + (w - v) := by
      filter_upwards [hlin] with g hg
      simp only [Pi.sub_apply, Pi.add_apply, hg, hPw]
      ring
    calc eLpNorm (P v - v) 2 μ0 = eLpNorm (P (v - w) + (w - v)) 2 μ0 := eLpNorm_congr_ae hdecomp
      _ ≤ eLpNorm (P (v - w)) 2 μ0 + eLpNorm (w - v) 2 μ0 :=
          eLpNorm_add_le hPvw2.1 (hw2.1.sub hv2.1) one_le_two
      _ ≤ ENNReal.ofReal c * eLpNorm (v - w) 2 μ0 + eLpNorm (v - w) 2 μ0 :=
          add_le_add hcontr (le_of_eq (eLpNorm_sub_comm _ _ _ _))
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal ε + ENNReal.ofReal ε :=
          add_le_add (mul_le_mul_right hvw.le _) hvw.le
      _ = ENNReal.ofReal ((c + 1) * ε) := by
          rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add (mul_nonneg hc0 hε.le) hε.le]
          congr 1; ring

  have h0 : eLpNorm (P v - v) 2 μ0 = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_) bot_le
    have hc1 : 0 < c + 1 := by linarith
    have := key ((δ : ℝ) / (c + 1)) (div_pos (NNReal.coe_pos.mpr hδ) hc1)
    have hδ' : (c + 1) * ((δ : ℝ) / (c + 1)) = (δ : ℝ) := by field_simp
    rw [hδ', ENNReal.ofReal_coe_nnreal] at this
    simpa using this
  have hae : (P v - v) =ᵐ[μ0] 0 :=
    (eLpNorm_eq_zero_iff (hPv2.1.sub hv2.1) two_ne_zero).mp h0
  filter_upwards [hae] with g hg
  simpa [sub_eq_zero] using hg

end
end S_AutomorphicForm_levelTypeAverage_ae_eq_self_of_isAutomorphicFnAt_of_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_levelTypeAverage_ae_eq_self_of_isAutomorphicFnAt_of_mem_archCutSubmodule (solution)
