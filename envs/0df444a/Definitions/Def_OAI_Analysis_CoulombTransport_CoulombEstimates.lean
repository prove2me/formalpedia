-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
-- name    : OAI_Analysis_CoulombTransport_CoulombEstimates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:31:19.291402+00:00
-- url     : https://prove2.me/theorems/e4dad306-8db9-42ef-930e-9ad5045cf057
-- title:
--   The real Coulomb cost and separated triples
-- statement:
--   For points $x,y,z$ of a metric space:
--
--   1. the real-valued three-body Coulomb cost is
--   $$
--   c_{\mathbb{R}}(x,y,z)=\frac1{d(x,y)}+\frac1{d(x,z)}+\frac1{d(y,z)} ;
--   $$
--   2. a triple in $(\mathbb{R}^3)^3$ is $\eta$-separated if all three pairwise distances are at least $\eta$.
--
--   On $\eta$-separated triples the cost is bounded by $3/\eta$ and agrees with the extended-valued cost. This allows real-valued estimates away from collisions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CoulombEstimates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CoulombEstimates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

namespace OAI

universe uE uA

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.CoulombEstimates

/-- Real-valued three-particle Coulomb cost on an arbitrary metric space. -/
def realCost {E : Type uE} [PseudoMetricSpace E] (x y z : E) : ℝ :=
  (dist x y)⁻¹ + (dist x z)⁻¹ + (dist y z)⁻¹

/-- Pairwise separation of the coordinates of a triple. -/
def Separated (eta : ℝ) (t : Triple) : Prop :=
  eta ≤ dist t.1 t.2.1 ∧ eta ≤ dist t.1 t.2.2 ∧ eta ≤ dist t.2.1 t.2.2

end Problem356.CoulombEstimates

end

end OAI


