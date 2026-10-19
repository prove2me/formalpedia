-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
-- name    : OAI_Analysis_CoulombTransport_StateDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:26:07.489719+00:00
-- url     : https://prove2.me/theorems/8c7de282-948a-48db-aacd-76b35724cb2c
-- title:
--   The pairing of a state vector with a state gradient
-- statement:
--   For real inner product spaces $E$ and $F$, the state dual is the continuous bilinear map on $E\times F$
--   $$
--   \bigl((u_1,u_2),(v_1,v_2)\bigr)\mapsto\langle u_1,v_1\rangle+\langle u_2,v_2\rangle .
--   $$
--
--   No inner product structure on the product is needed. It turns the two components of a gradient into the corresponding Fréchet derivative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StateDual.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StateDual.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal

namespace OAI

universe uE uF uP

noncomputable section

open Set
open scoped InnerProductSpace

namespace Problem356

variable (E : Type uE) (F : Type uF) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The sum of the two component inner products, bundled for the usual
(max-norm) product. No inner-product-space instance on the product is used. -/
def stateDual : (E × F) →L[ℝ] ((E × F) →L[ℝ] ℝ) :=
  (((ContinuousLinearMap.compL ℝ (E × F) E ℝ).flip
      (ContinuousLinearMap.fst ℝ E F)).comp
    ((innerSL ℝ).comp (ContinuousLinearMap.fst ℝ E F))) +
  (((ContinuousLinearMap.compL ℝ (E × F) F ℝ).flip
      (ContinuousLinearMap.snd ℝ E F)).comp
    ((innerSL ℝ).comp (ContinuousLinearMap.snd ℝ E F)))

@[simp] theorem stateDual_apply (u v : E × F) :
    stateDual E F u v = ⟪u.1, v.1⟫_ℝ + ⟪u.2, v.2⟫_ℝ := by
  rfl

end Problem356

end

end OAI


