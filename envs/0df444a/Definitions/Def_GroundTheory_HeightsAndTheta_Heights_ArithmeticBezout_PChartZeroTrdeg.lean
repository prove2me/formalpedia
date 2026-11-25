-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartZeroTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartZeroTrdeg
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:01:15.992471+00:00
-- url     : https://prove2.me/theorems/cb1fe3e5-629f-4652-a7a2-0673c596fc68
-- title:
--   PChart Zero Trdeg
-- statement:
--   Definitions and structural lemmas for PChart Zero Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartZeroTrdeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace ChartZeroTrdeg
variable {F : Type} [Field F] {n : ℕ}
def homogAt (p : MvPolynomial (Fin n) F) (j : Fin n) (N : ℕ) : MvPolynomial (Fin n) F :=
  ∑ α ∈ p.support, monomial α (coeff α p) * X j ^ (N - α.sum fun _ e => e)
end ChartZeroTrdeg
end
end GroundTheory.Heights₂.Heights


