-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
-- name    : OAI_Analysis_CoulombTransport_GraphBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:33:37.583652+00:00
-- url     : https://prove2.me/theorems/b824c8d5-338e-4016-8822-8a323435617a
-- title:
--   Graph couplings of a pair of maps
-- statement:
--   For maps $T_2,T_3$ of $\mathbb{R}^3$ and a measure $\mu$:
--
--   1. the graph map is $x\mapsto(x,T_2x,T_3x)$;
--   2. the graph measure is the pushforward of $\mu$ under it,
--   $$
--   \gamma_{T_2,T_3}=(\mathrm{id},T_2,T_3)_\#\mu .
--   $$
--
--   If $T_2$ and $T_3$ preserve $\mu$, the graph measure is a three-coupling of $\mu$ whose cost is the Monge graph cost. This bridges the Monge and Kantorovich problems.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/GraphBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/GraphBridge.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

def graphMap (T2 T3 : E3 → E3) (x : E3) : Triple := (x, (T2 x, T3 x))

def graphMeasure (mu : Measure E3) (T2 T3 : E3 → E3) : Measure Triple :=
  Measure.map (graphMap T2 T3) mu

end Problem356

end

end OAI


