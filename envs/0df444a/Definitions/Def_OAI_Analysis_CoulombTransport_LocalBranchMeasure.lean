-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
-- name    : OAI_Analysis_CoulombTransport_LocalBranchMeasure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:10:53.569963+00:00
-- url     : https://prove2.me/theorems/f0453740-8bfa-4b59-83dc-09377dbd98b5
-- title:
--   Extending a local branch by a constant
-- statement:
--   For a local homeomorphism $e$ between topological spaces and a point $z$, the extended branch is the total function
--   $$
--   \tilde e(x)=\begin{cases}e(x),&x\in\mathrm{source}(e),\\z,&\text{otherwise}.\end{cases}
--   $$
--   It agrees with $e$ on the source.
--
--   Extended branches are measurable total maps, so they can be used to push measures forward.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalBranchMeasure.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalBranchMeasure.lean by skeleton subtraction
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

namespace OAI

universe uAlpha uBeta

noncomputable section

open MeasureTheory Set

namespace Problem356
namespace LocalBranchMeasure

variable {α : Type uAlpha} {β : Type uBeta} [TopologicalSpace α] [TopologicalSpace β]
  [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β]

/-- A local branch extended by a fixed value outside its source. -/
def extendedBranch (e : OpenPartialHomeomorph α β) (z : β) : α → β := by
  classical
  exact e.source.piecewise e (fun _ => z)

omit [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β] in
@[simp] theorem extendedBranch_apply_of_mem
    (e : OpenPartialHomeomorph α β) (z : β) {x : α} (hx : x ∈ e.source) :
    extendedBranch e z x = e x := by
  classical
  simp [extendedBranch, hx]

end LocalBranchMeasure
end Problem356

end

end OAI


