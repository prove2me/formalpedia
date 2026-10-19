-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
-- name    : OAI_Analysis_CoulombTransport_GluedCertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:17:23.622515+00:00
-- url     : https://prove2.me/theorems/1afc5a38-6ee7-49d7-b7a5-f90d8fff0c3c
-- title:
--   Contact triples on a union of components
-- statement:
--   Let $(U_i)_{i\in\iota}$ be sets in $\mathbb{R}^3$, $\mathrm{Good}$ a predicate on ordered label triples, and $\mathrm{Contact}$ a family of contact predicates on triples, one for each label triple. A triple $t=(x,y,z)$ is a component contact if there is a label triple $(i,j,k)$ with
--   $$
--   x\in U_i,\ y\in U_j,\ z\in U_k,\qquad\mathrm{Good}(i,j,k),\qquad\mathrm{Contact}_{(i,j,k)}(t) .
--   $$
--
--   This describes where a glued certificate is attained: only on good component types, and there only on the local contact sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/GluedCertificate.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/GluedCertificate.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward

namespace OAI

universe uIndex

noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- A contact triple on a finite union, with its ordered component labels. -/
def componentContact {ι : Type uIndex} (U : ι → Set E3)
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop) (t : Triple) : Prop :=
  ∃ a, t.1 ∈ U a.1 ∧ t.2.1 ∈ U a.2.1 ∧ t.2.2 ∈ U a.2.2 ∧
    Good a ∧ Contact a t

end Problem356

end

end OAI


