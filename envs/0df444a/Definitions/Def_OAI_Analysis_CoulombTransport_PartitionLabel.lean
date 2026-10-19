-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
-- name    : OAI_Analysis_CoulombTransport_PartitionLabel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:44:12.913152+00:00
-- url     : https://prove2.me/theorems/e5a7fa49-d58c-4a9e-b506-9c66dd5d1f99
-- title:
--   The label of a point in a family of cells
-- statement:
--   For a family of sets $(A_i)_{i\in\iota}$ in $X$, the label of $x$ is
--   $$
--   \mathrm{label}(x)=\begin{cases}\text{some }i\text{ with }x\in A_i,&\text{if one exists},\\\text{none},&\text{otherwise}.\end{cases}
--   $$
--   For a disjoint family the label is the unique cell containing $x$.
--
--   Points outside all cells are labelled none instead of being assigned an arbitrary cell. This labelling defines maps cell by cell.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/PartitionLabel.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/PartitionLabel.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uX uIndex

noncomputable section

open Set MeasureTheory

namespace Problem356.FiniteCells

/-- The exact label of a point in a disjoint family; points outside all cells
are assigned `none`, without choosing an arbitrary distinguished cell. -/
def cellLabel {X : Type uX} {ι : Type uIndex} (A : ι → Set X) (x : X) : Option ι :=
  by
    classical
    exact if h : ∃ i, x ∈ A i then some (Classical.choose h) else none

end Problem356.FiniteCells

end

end OAI


