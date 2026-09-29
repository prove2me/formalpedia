-- Prove2me | solution 1 for AutomorphicForm.apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ed589e38-d7fd-5b6a-892b-0fe11716cad0

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

namespace UnramTransport

theorem valued_eq_one_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) :
    Valued.v (t : v.adicCompletion K) = 1 ↔
      (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
        ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro h
    simp [h]
  · rintro ⟨h1, h2⟩
    have h0 : 0 < Valued.v (t : v.adicCompletion K) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr t.ne_zero)
    exact le_antisymm h1 ((inv_le_one₀ h0).mp h2)

end UnramTransport

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKN : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξK ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hvw : HeightOneSpectrum.under (𝓞 K) w = v)
    (he : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hur : ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξK ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (s : (w.adicCompletion L)ˣ) (hs : Valued.v (s : w.adicCompletion L) = 1) :
    ξL ⟨Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w s), Subgroup.mem_top _⟩ = 1 := by
  subst hvw
  let μK : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ξK.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ≃* (AdeleRing (𝓞 K) K)ˣ).symm.toMonoidHom
  let μL : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξL.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) ≃* (AdeleRing (𝓞 L) L)ˣ).symm.toMonoidHom
  have hcomp : μK.comp (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm = μL :=
    MonoidHom.ext fun z => hξKN z
  have hK : NumberField.TateGlobal.IsUnramifiedCharAt μK (HeightOneSpectrum.under (𝓞 K) w) := by
    intro t ht1 ht2
    exact hur t ((UnramTransport.valued_eq_one_iff _ t).mpr ⟨ht1, ht2⟩)
  have hL := (NumberField.TateGlobal.isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
      K L μK w he).mpr hK
  rw [hcomp] at hL
  obtain ⟨hs1, hs2⟩ := (UnramTransport.valued_eq_one_iff w s).mp hs
  exact hL s hs1 hs2

end S_AutomorphicForm_apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_AutomorphicForm_apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one (solution)
