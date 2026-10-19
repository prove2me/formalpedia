-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
-- name    : OAI_Analysis_CoulombTransport_LocalImplicit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:51:23.704634+00:00
-- url     : https://prove2.me/theorems/eb7709d0-26df-4cc9-8772-39240c4ca743
-- title:
--   Analytic stationary charts from the implicit function theorem
-- statement:
--   Let $P,S$ be real Banach spaces and $G:P\times(S\times S)\to S\times S$.
--
--   1. The implicit derivative at $(p,s)$ is
--   $$
--   -\bigl(D_sG(p,s)\bigr)^{-1}\circ D_pG(p,s) .
--   $$
--   2. Analytic stationary charts at $(p,s)$ are two local homeomorphisms $\mathrm{central},\mathrm{opposite}:P\to S$ with a common open source containing $p$, taking the values $s_1,s_2$ at $p$. On a state domain around $s$, $G(y,z)=0$ holds exactly for $z=(\mathrm{central}(y),\mathrm{opposite}(y))$, and both charts and their inverses are analytic.
--   3. Such charts can be restricted to any smaller open neighborhood of $p$.
--
--   These charts describe the two smooth branches of solutions of the stationarity equation near a nondegenerate center.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean by skeleton subtraction
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

namespace OAI

universe uP uS

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace Problem356.LocalImplicit

variable {P : Type uP} {S : Type uS}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/-- The derivative supplied by the implicit-function theorem, with parameter first. -/
def implicitDerivative (G : P × (S × S) → S × S) (p : P) (s : S × S) :
    P →L[ℝ] S × S :=
  -(fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P (S × S)).inverse ∘L
    (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inl ℝ P (S × S))

/-- Two separately invertible coordinates of one local stationary branch. -/
structure AnalyticStationaryCharts (G : P × (S × S) → S × S) (p : P) (s : S × S) where
  central : OpenPartialHomeomorph P S
  opposite : OpenPartialHomeomorph P S
  source_eq : central.source = opposite.source
  point_mem : p ∈ central.source
  central_value : central p = s.1
  opposite_value : opposite p = s.2
  stateDomain : Set (S × S)
  stateDomain_open : IsOpen stateDomain
  state_mem : s ∈ stateDomain
  mapsTo_state : MapsTo (fun y => (central y, opposite y)) central.source stateDomain
  stationary : ∀ y ∈ central.source, G (y, (central y, opposite y)) = 0
  unique_zero : ∀ y ∈ central.source, ∀ z ∈ stateDomain,
    G (y, z) = 0 ↔ (central y, opposite y) = z
  central_analytic : ContDiffOn ℝ ω central central.source
  central_inverse_analytic : ContDiffOn ℝ ω central.symm central.target
  opposite_analytic : ContDiffOn ℝ ω opposite opposite.source
  opposite_inverse_analytic : ContDiffOn ℝ ω opposite.symm opposite.target

namespace AnalyticStationaryCharts

variable {G : P × (S × S) → S × S} {p : P} {s : S × S}

omit [CompleteSpace P] [CompleteSpace S]

/-- Restrict both parameter charts to the same additional open neighborhood. -/
def restrictSource (c : AnalyticStationaryCharts G p s)
    (U : Set P) (hU : IsOpen U) (hp : p ∈ U) : AnalyticStationaryCharts G p s where
  central := c.central.restrOpen U hU
  opposite := c.opposite.restrOpen U hU
  source_eq := by
    change c.central.source ∩ U = c.opposite.source ∩ U
    rw [c.source_eq]
  point_mem := ⟨c.point_mem, hp⟩
  central_value := c.central_value
  opposite_value := c.opposite_value
  stateDomain := c.stateDomain
  stateDomain_open := c.stateDomain_open
  state_mem := c.state_mem
  mapsTo_state := fun _ hy => c.mapsTo_state hy.1
  stationary := fun y hy => c.stationary y hy.1
  unique_zero := fun y hy z hz => c.unique_zero y hy.1 z hz
  central_analytic := c.central_analytic.mono (fun _ h => h.1)
  central_inverse_analytic := c.central_inverse_analytic.mono (fun _ h => h.1)
  opposite_analytic := c.opposite_analytic.mono (fun _ h => h.1)
  opposite_inverse_analytic := c.opposite_inverse_analytic.mono (fun _ h => h.1)

@[simp] theorem restrictSource_central_coe
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hp : p ∈ U) :
    ((c.restrictSource U hU hp).central : P → S) = c.central := rfl

@[simp] theorem restrictSource_opposite_coe
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hp : p ∈ U) :
    ((c.restrictSource U hU hp).opposite : P → S) = c.opposite := rfl

@[simp] theorem restrictSource_source
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hp : p ∈ U) :
    (c.restrictSource U hU hp).central.source = c.central.source ∩ U := rfl

end AnalyticStationaryCharts

end Problem356.LocalImplicit

end

end OAI


