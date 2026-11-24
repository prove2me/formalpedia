-- Prove2me | solution 1 for AAInvW.strictMono_val_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:59:58.68809+00:00
-- url     : https://prove2.me/submissions/2e35fa67-548b-49b2-8e8d-6c12f7da3b1d

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
theorem _root_.solution {m N : ℕ} (C : Fin m → Fin N) :
    StrictMono (fun l => (C l).val) ↔ StrictMono C :=
  ⟨fun h _ _ hab => h hab, fun h _ _ hab => h hab⟩
end AAInvW
