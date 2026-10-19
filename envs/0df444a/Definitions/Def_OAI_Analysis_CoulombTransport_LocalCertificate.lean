-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
-- name    : OAI_Analysis_CoulombTransport_LocalCertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:06:04.945385+00:00
-- url     : https://prove2.me/theorems/1f265a5b-25c8-4949-ae3b-27a67bd6aad8
-- title:
--   Local supporting charts with exact contact
-- statement:
--   Let $E$ be a real normed space, $F:E\times(E\times E)\to\mathbb{R}$ a potential and $G$ its stationarity map, with a base parameter $p$ and base state $s$. Local supporting charts consist of:
--
--   1. analytic stationary charts $y\mapsto(\mathrm{central}(y),\mathrm{opposite}(y))$ for $G$ at $(p,s)$, with parameter domain the ball $B(p,r)$ and state domain the ball $B(s,R)$, where $r,R>0$;
--   2. an analytic value function $V(y)=F(y,(\mathrm{central}(y),\mathrm{opposite}(y)))$ with $V(p)=F(p,s)$, such that for all $y\in B(p,r)$ and $z\in B(s,R)$
--   $$
--   V(y)\le F(y,z),\qquad F(y,z)=V(y)\iff z=(\mathrm{central}(y),\mathrm{opposite}(y)).
--   $$
--
--   So for each parameter the stationary branch point is the unique minimizer in the state ball. The minimum value then serves as a supporting potential.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalCertificate.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalCertificate.lean by skeleton subtraction
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

namespace OAI

universe uE

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Problem356.LocalGeometry

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local exact supporting certificate, with the stationary branches retained
as analytic local diffeomorphisms and both domains shrunk to metric balls. -/
structure LocalSupportingCharts (F : E × (E × E) → ℝ)
    (G : E × (E × E) → E × E) (p : E) (s : E × E) where
  charts : LocalImplicit.AnalyticStationaryCharts G p s
  parameterRadius : ℝ
  parameterRadius_pos : 0 < parameterRadius
  source_ball : charts.central.source = Metric.ball p parameterRadius
  stateRadius : ℝ
  stateRadius_pos : 0 < stateRadius
  state_ball : charts.stateDomain = Metric.ball s stateRadius
  value : E → ℝ
  value_analytic : ContDiffOn ℝ ω value charts.central.source
  value_eq : ∀ y, value y = F (y, (charts.central y, charts.opposite y))
  value_base : value p = F (p, s)
  supporting : ∀ y ∈ charts.central.source, ∀ z ∈ charts.stateDomain,
    value y ≤ F (y, z)
  contact : ∀ y ∈ charts.central.source, ∀ z ∈ charts.stateDomain,
    F (y, z) = value y ↔ z = (charts.central y, charts.opposite y)

end Problem356.LocalGeometry

end

end OAI


