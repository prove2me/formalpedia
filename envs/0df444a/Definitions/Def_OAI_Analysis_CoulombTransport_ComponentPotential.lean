-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
-- name    : OAI_Analysis_CoulombTransport_ComponentPotential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:49:26.518347+00:00
-- url     : https://prove2.me/theorems/2f09357c-39a0-42bb-9f01-c849631b6148
-- title:
--   Gluing local potentials on disjoint components
-- statement:
--   For finitely many sets $U_i\subseteq\mathbb{R}^3$ and real functions $u_i$, the glued potential is
--   $$
--   u(x)=\sum_i\mathbf{1}_{U_i}(x)\,u_i(x) .
--   $$
--   On disjoint components it equals $u_i$ on $U_i$ and $0$ outside all components.
--
--   Local supporting potentials built near each component combine into one global potential.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/ComponentPotential.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/ComponentPotential.lean by skeleton subtraction
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

namespace OAI

universe uIndex

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.ComponentPotential

variable {ι : Type uIndex} [Fintype ι]

/-- Glue local potentials on disjoint components, with value zero outside them. -/
def glue (U : ι → Set E3) (u : ι → E3 → ℝ) (x : E3) : ℝ :=
  ∑ i, (U i).indicator (u i) x

end Problem356.ComponentPotential

end

end OAI


