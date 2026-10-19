-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
-- name    : OAI_Analysis_CoulombTransport_SmoothPushforward
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:14:37.892987+00:00
-- url     : https://prove2.me/theorems/105e0f43-5b71-456c-b7c3-fa469b18dffb
-- title:
--   Transporting an amplitude through a local homeomorphism
-- statement:
--   For a local homeomorphism $e$ of $\mathbb{R}^3$, an amplitude $g$ and a factor $J$, the transported amplitude is
--   $$
--   y\mapsto\mathbf{1}_{\mathrm{target}(e)}(y)\,g\bigl(e^{-1}(y)\bigr)\,J(y) .
--   $$
--   With $J$ the square root of the Jacobian of $e^{-1}$, the square of the transported amplitude is the density of the pushforward of $g^2\,dx$.
--
--   Working with square roots of densities keeps the counterexample density smooth with a smooth square root.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SmoothPushforward.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SmoothPushforward.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Problem356

/-- Transport of a compactly supported amplitude through a local
homeomorphism, with a prescribed Jacobian square-root factor. -/
def localTransportAmplitude (e : OpenPartialHomeomorph E3 E3)
    (g J : E3 → ℝ) : E3 → ℝ :=
  e.target.indicator (fun y => g (e.symm y) * J y)

end Problem356

end

end OAI


