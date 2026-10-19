-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_CenterAxis
-- name    : OAI_Analysis_CoulombTransport_CenterAxis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:33:45.409858+00:00
-- url     : https://prove2.me/theorems/cc48e519-7af6-4855-af33-869d5768da58
-- title:
--   The five centers in terms of the axis vectors
-- statement:
--   Let $e_0=(1,0,0)$ and $e_1=(0,1,0)$ denote the first two axis vectors of $\mathbb{R}^3$. The five centers of the construction satisfy
--   $$
--   P_0=0,\quad P_1=e_0,\quad P_2=-e_0,\quad P_3=e_1,\quad P_4=-e_1 .
--   $$
--
--   The finite center certificate and the analytic branch construction therefore use the same points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CenterAxis.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CenterAxis.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry

namespace OAI

noncomputable section

namespace Problem356.CenterAxis

open CenterCertificate CoulombCalculus

/-- The finite certificate and the analytic construction use the same central point. -/
@[simp] theorem point_zero : point 0 = (0 : E3) := by
  simp [point]

/-- The first positive component is the first analytic axis. -/
@[simp] theorem point_one : point 1 = axisVector 0 := by
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- The first negative component is opposite to the first analytic axis. -/
@[simp] theorem point_two : point 2 = -axisVector 0 := by
  change (!₂[-1, 0, 0] : E3) = -axisVector 0
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- The second positive component is the second analytic axis. -/
@[simp] theorem point_three : point 3 = axisVector 1 := by
  change (!₂[0, 1, 0] : E3) = axisVector 1
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- The second negative component is opposite to the second analytic axis. -/
@[simp] theorem point_four : point 4 = -axisVector 1 := by
  change (!₂[0, -1, 0] : E3) = -axisVector 1
  ext i
  fin_cases i <;> norm_num [point, axisVector]

end Problem356.CenterAxis

end

end OAI


