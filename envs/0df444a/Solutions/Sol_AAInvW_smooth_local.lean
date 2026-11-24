-- Prove2me | solution 1 for AAInvW.smooth_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:54:02.912898+00:00
-- url     : https://prove2.me/submissions/1449d695-8fe5-441f-8931-7db5a7d4badf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear

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
theorem _root_.solution : SmoothLocal := by
  unfold SmoothLocal
  intro n H E _ _ f f' hff hf
  unfold SmoothOnH at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgH => (hff g hgH).symm.trans (hfF g hg hgH)⟩
end AAInvW
