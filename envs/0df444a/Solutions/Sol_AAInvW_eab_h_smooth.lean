-- Prove2me | solution 1 for AAInvW.eab_h_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:41:52.468307+00:00
-- url     : https://prove2.me/submissions/fef80c3c-a182-444c-a091-7b53d166068d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Theorems.Thm_P2M_AAInvW_smooth_linear__4ce59117e344
import Theorems.Thm_AAInvW_ana_rdSmooth
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
theorem _root_.solution : EabHSmooth := by
  unfold EabHSmooth
  intro n H E _ _ f a b hH hf
  unfold EabH
  exact smooth_linear' n H E _ _ Complex.I (ana_rdSmooth hH hf (ana_hpartMem hH _).1)
    (ana_rdSmooth hH hf (ana_hpartMem hH _).2.1)
end AAInvW
