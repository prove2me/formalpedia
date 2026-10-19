-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
-- name    : OAI_Analysis_CoulombTransport_Calibration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:38:48.101808+00:00
-- url     : https://prove2.me/theorems/ad4e8ae4-0807-40f5-b33c-08afde4c536b
-- title:
--   Shifting a signed potential to be nonnegative
-- statement:
--   For a real potential $u$ on $\mathbb{R}^3$ and a constant $M$, the shifted potential is
--   $$
--   x\mapsto(u(x)+M)^+\in[0,\infty] .
--   $$
--   If $u\ge-M$ it equals $u+M$.
--
--   Shifted potentials let a signed dual potential be used where nonnegative extended-real integrals are required.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/Calibration.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/Calibration.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A bounded-below signed potential is made nonnegative by a constant shift. -/
def shiftedPotential (u : E3 → ℝ) (M : ℝ) (x : E3) : ℝ≥0∞ :=
  ENNReal.ofReal (u x + M)

end Problem356

end

end OAI


