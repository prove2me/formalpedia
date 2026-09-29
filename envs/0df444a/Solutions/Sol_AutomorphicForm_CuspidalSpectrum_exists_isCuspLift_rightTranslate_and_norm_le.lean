-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightTranslate_and_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4eaa4abe-f21e-5e23-bcdb-bee678694515

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ) (y : AdelicGL2 (𝓞 F) F) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F y) S ∧
        ‖S‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (σ / 2) := by
  obtain ⟨T, T', hT, -, -, hTn⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ y

  have hAmap : ∀ a ∈ Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)),
      T a ∈ Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) := by
    rintro _ ⟨φm, hφm, rfl⟩
    have hc : (φm : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨φm.2, hφm.2⟩
    have hRy : rightTranslate F y φm ∈ cuspMemberSubmodule F Φ₀ ξ :=
      AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ y φm hφm
    refine ⟨⟨rightTranslate F y φm, hRy.1.1.1⟩, hRy, ?_⟩
    exact (hT.comm φm hc).symm

  have hCmap : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ := by
    intro v hv
    have hv' : v ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) : Set (Carrier F Φ₀ σ))) := by
      rw [← Submodule.topologicalClosure_coe]; exact hv
    have hTv := map_mem_closure T.continuous hv' hAmap
    rw [← Submodule.topologicalClosure_coe] at hTv
    exact hTv
  refine ⟨(T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) (fun v => hCmap v v.2),
    fun φ h => ?_, ?_⟩
  · apply Subtype.ext
    show T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ)
      = (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F y φ, h⟩ : Carrier F Φ₀ σ)
    rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact hT.comm (φ : AdelicGL2 (𝓞 F) F → ℂ) ⟨φ.2.1.1.1, φ.2.2⟩
  · refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun v => ?_) hTn
    show ‖T (v : Carrier F Φ₀ σ)‖ ≤ ‖T‖ * ‖v‖
    exact (T.le_opNorm (v : Carrier F Φ₀ σ)).trans_eq (by rw [Submodule.coe_norm])

end S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le (solution)
