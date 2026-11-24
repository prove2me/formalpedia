-- Prove2me | solution 1 for AAInvW.eab_h_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:38:38.220857+00:00
-- url     : https://prove2.me/submissions/d8f3b561-8482-4245-9e5c-7886eb0dacf1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Theorems.Thm_AAInvW_ana_rdLocal
import Theorems.Thm_AAInvW_ana_hpartMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace AAInvW
theorem _root_.solution : EabHLocal := by
  unfold EabHLocal
  intro n H E _ _ f f' a b g hH hff hg
  unfold EabH
  rw [ana_rdLocal hH hff (ana_hpartMem hH _).1 hg, ana_rdLocal hH hff (ana_hpartMem hH _).2.1 hg]
end AAInvW
