-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
-- name    : OAI_Analysis_CoulombTransport_CoulombSupportExistence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:29:53.975739+00:00
-- url     : https://prove2.me/theorems/f7095e9e-6608-435f-850c-c52350f3a7c6
-- title:
--   The state derivative as a linear form
-- statement:
--   For an axis vector $a$, a parameter $y$ and a state $s=(s_1,s_2)$ in $\mathbb{R}^3\times\mathbb{R}^3$, let $G_a$ be the stationarity map of the regularized local problem with $K=20$. The linear form $D(a,y,s)$ is
--   $$
--   D(a,y,s)(u,v)=\langle G_a(y,s)_1,u\rangle+\langle G_a(y,s)_2,v\rangle .
--   $$
--
--   This is the Fréchet derivative of the local potential in the state variables. Its vanishing is the stationarity condition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CoulombSupportExistence.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CoulombSupportExistence.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem356.CoulombSupportExistence

open CoulombCalculus GeometryJets LocalGeometry

 def D (a y : E3) (s : E3 × E3) : (E3 × E3) →L[ℝ] ℝ :=
  stateDual E3 E3 (stationaryEquation 20 a (y, s))

end Problem356.CoulombSupportExistence

end

end OAI


