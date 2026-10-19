-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
-- name    : OAI_Analysis_CoulombTransport_CommonBranches
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:45:59.925121+00:00
-- url     : https://prove2.me/theorems/dbbb95e5-9049-496e-890a-01c0184e4fd8
-- title:
--   Reparametrizing local branches by the central coordinate
-- statement:
--   Let $X,Z$ be local homeomorphisms of a space $E$ on a parameter domain. The outer branch reparametrized by the central coordinate is
--   $$
--   \mathrm{outer}(X,Z)=Z\circ X^{-1} .
--   $$
--   For two families $(X_0,Z_0)$ and $(X_1,Z_1)$, the four outer branches are
--   $$
--   X_0^{-1},\quad Z_0\circ X_0^{-1},\quad X_1^{-1},\quad Z_1\circ X_1^{-1} .
--   $$
--
--   Their common source is open, contains the central base point, and inherits smoothness of the inverses. All four branches are thus functions of the same central point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CommonBranches.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CommonBranches.lean by skeleton subtraction
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

namespace OAI

universe uE uM uIndex uF

/-!
# Reparametrizing local branches by their common central component

For local homeomorphisms `X,Z` on the parameter component, the central
parametrizations are `X.symm` and `X.symm.trans Z`. Their common source is
open, contains the central base point, and inherits both smooth inverses.
-/

noncomputable section
open Set Metric

namespace Problem356.CommonBranches

variable {E : Type uE} [TopologicalSpace E]

/-- Reparametrization of the second outer branch by the central coordinate. -/
def outer (X Z : OpenPartialHomeomorph E E) : OpenPartialHomeomorph E E :=
  X.symm.trans Z

@[simp] theorem outer_apply (X Z : OpenPartialHomeomorph E E) (x : E) :
    outer X Z x = Z (X.symm x) := rfl

/-- The four ordered outer branches associated with two local families. -/
def four (X Z : Fin 2 → OpenPartialHomeomorph E E) :
    Fin 4 → OpenPartialHomeomorph E E :=
  ![(X 0).symm, outer (X 0) (Z 0), (X 1).symm, outer (X 1) (Z 1)]

section Metric

variable {M : Type uM} [PseudoMetricSpace M]

end Metric

section Smooth

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

end Smooth
end Problem356.CommonBranches

end

end OAI


