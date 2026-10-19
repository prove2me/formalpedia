-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
-- name    : OAI_Analysis_CoulombTransport_SmoothBranchMarginal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:25:03.749309+00:00
-- url     : https://prove2.me/theorems/98490235-ec1b-4a3b-82ce-1d704aad749d
-- title:
--   Smooth densities assembled from a central amplitude and four branches
-- statement:
--   The construction uses five components: a central one with weight $\frac13$ and four branch components with weight $\frac16$ each.
--
--   1. Given a central amplitude $g$ and branch amplitudes $q_0,\dots,q_3$, the marginal density is
--   $$
--   \rho=\tfrac13g^2+\tfrac16\sum_{i<4}q_i^2 ,
--   $$
--      and the component regions are a central set $B$ and its images under the four branches.
--   2. An amplitude is normalized if it is nonnegative, smooth, compactly supported and $\int g^2=1$.
--   3. Smooth branch data on $B$ consist of a smooth compactly supported probability density $\rho$ and a probability measure $\nu$ carried by a compact core $\subseteq B$. They also include measurable branch maps, injective on $B$ and continuous on the core, with pairwise disjoint components $B,H_0(B),\dots,H_3(B)$, and
--   $$
--   \mu_\rho=\tfrac13\nu+\tfrac16\sum_{i<4}H_{i\#}\nu .
--   $$
--
--   These data are what the measure-level arguments (attainment, nonattainment by maps, and approximation) require.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SmoothBranchMarginal.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SmoothBranchMarginal.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.SmoothBranchMarginal

/-- The five component weights are fixed by the counterexample construction. -/
def componentWeight : Option (Fin 4) → ℝ
  | none => 1 / 3
  | some _ => 1 / 6

def componentAmplitude (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ) :
    Option (Fin 4) → E3 → ℝ
  | none => g
  | some i => q i

def componentRegion (B : Set E3) (e : Fin 4 → OpenPartialHomeomorph E3 E3) :
    Option (Fin 4) → Set E3
  | none => B
  | some i => e i '' B

def marginalDensity (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ) (x : E3) : ℝ :=
  ∑ i : Option (Fin 4), componentWeight i * componentAmplitude g q i x ^ 2

def NormalizedAmplitude (g : E3 → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧
  ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g ∧
  HasCompactSupport g ∧ (∫ x : E3, g x ^ 2) = 1

/-- The construction data expected by the measure-level nonattainment and
separated-support approximation arguments. -/
structure SmoothBranchData (B : Set E3) where
  rho : E3 → ℝ
  nu : Measure E3
  branch : Fin 4 → E3 → E3
  compactCore : Set E3
  density_smooth : IsSmoothCompactProbabilityDensity rho
  probability : IsProbabilityMeasure nu
  measurable_central : MeasurableSet B
  core_compact : IsCompact compactCore
  core_subset : compactCore ⊆ B
  core_full : ∀ᵐ x ∂nu, x ∈ compactCore
  branch_measurable : ∀ i, Measurable (branch i)
  branch_injective : ∀ i, Set.InjOn (branch i) B
  branch_image_measurable : ∀ i S, MeasurableSet S → S ⊆ B →
    MeasurableSet (branch i '' S)
  branch_continuous : ∀ i, ContinuousOn (branch i) compactCore
  component_disjoint : Pairwise (fun i j : Option (Fin 4) =>
    Disjoint (i.elim B (fun k => branch k '' B)) (j.elim B (fun k => branch k '' B)))
  density_eq : densityMeasure rho =
    (1 / 3 : ℝ≥0∞) • nu + ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) • Measure.map (branch i) nu

end Problem356.SmoothBranchMarginal

end

end OAI


