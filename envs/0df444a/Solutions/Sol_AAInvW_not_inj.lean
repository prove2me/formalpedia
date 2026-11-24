-- Prove2me | solution 1 for AAInvW.not_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:48:29.434503+00:00
-- url     : https://prove2.me/submissions/c708e1d4-2e3e-492f-8aaa-b0e257d6d75c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
namespace AAInvW
theorem _root_.solution {α β : Type*} {c : α → β} (hc : ¬ Function.Injective c) :
    ∃ p q, p ≠ q ∧ c p = c q := by
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨p, q, h, hne⟩ := hc
  exact ⟨p, q, hne, h⟩
end AAInvW
