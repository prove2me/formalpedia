-- Prove2me | solution 1 for AutomorphicForm.exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/05489189-e4fd-59fe-b4a5-a7deb376324a

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_isNormConjugator_one_of_idempotent_orbit
import Theorems.Thm_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion
import Theorems.Thm_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : ¬ IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hdet : ∃ k : ℤ, Valued.v (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      ((Multiplicative.ofAdd ((Module.finrank K L : ℤ) * k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K), IsNormOf K L (v.adicCompletion K) σ γ δ := by
  rcases AutomorphicForm.exists_idempotent_orbit_or_isField_tensor_adicCompletion K L hdeg σ hσ v with
    ⟨e, he, horth, hsum⟩ | hA
  ·
    obtain ⟨δ, hδ⟩ :=
      AutomorphicForm.isNormConjugator_one_of_idempotent_orbit K L (v.adicCompletion K) σ e he horth hsum γ
    exact ⟨δ, 1, hδ⟩
  ·
    exact AutomorphicForm.exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
      K L hdeg σ hσ v hv hA γ hγ hdet

end S_AutomorphicForm_exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one (solution)
