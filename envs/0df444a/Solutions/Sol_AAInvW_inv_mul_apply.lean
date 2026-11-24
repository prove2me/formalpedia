-- Prove2me | solution 1 for AAInvW.inv_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:28:22.29084+00:00
-- url     : https://prove2.me/submissions/f6f24412-d4a7-4e5f-afc6-a90bc23ee954

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine

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
theorem _root_.solution {N : ℕ} (g s : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) (c : Fin N) :
    ((g * s)⁻¹ *ᵥ v) c = ∑ d, s⁻¹ c d * (g⁻¹ *ᵥ v) d := by
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  rfl
end AAInvW
