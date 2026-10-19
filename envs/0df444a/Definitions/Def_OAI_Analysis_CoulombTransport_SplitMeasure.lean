-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
-- name    : OAI_Analysis_CoulombTransport_SplitMeasure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:42:19.353444+00:00
-- url     : https://prove2.me/theorems/f6b4a904-339e-47c9-90a6-b5b72c1ad4bd
-- title:
--   A central measure plus weighted branch pushforwards
-- statement:
--   For a measure $\nu$, a weight $a\ge0$, weights $b_i\ge0$ and maps $H_i$ indexed by a finite set, the split measure is
--   $$
--   a\,\nu+\sum_ib_i\,H_{i\#}\nu .
--   $$
--
--   The counterexample density is built this way from a central piece and its images under the branch maps.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SplitMeasure.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SplitMeasure.lean by skeleton subtraction
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

namespace OAI

universe uAlpha uIndex

/-! Measure identities for the five-component splitting construction. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356
namespace Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

variable [Fintype ι]

/-- The central measure together with finitely many weighted branch pushforwards. -/
def splitMeasure (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞)
    (H : ι → α → α) : Measure α :=
  a • ν + ∑ i, b i • Measure.map (H i) ν

end Splitting
end Problem356

end

end OAI


