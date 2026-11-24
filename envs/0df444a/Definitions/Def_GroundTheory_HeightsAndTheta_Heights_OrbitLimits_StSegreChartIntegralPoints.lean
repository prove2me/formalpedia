-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegralPoints
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegralPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:38.527442+00:00
-- url     : https://prove2.me/theorems/f2e4aa45-c6d5-4cf5-ab27-1853996d2308
-- title:
--   St Segre Chart Integral Points
-- statement:
--   Definitions and structural lemmas for St Segre Chart Integral Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StSegreChartIntegralPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar ptsIntegral pot segre PBlk)
open GroundTheory.Heights₂.Heights (varInt IsDegZeroSmooth segreChartSet segreChartComponents chartLift)
def SegreChartIntegralPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin 0 → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin 0 → (Fin m → ℂ) → ℝ),
    IsArithVar P 1 → IsDegZeroSmooth g → 0 < δ →
    (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    (∀ x ∈ segreChartSet P σ i, G =ᶠ[𝓝 x] g ∘ chartLift σ i) →
      ptsIntegral P (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J 0 G Φ
end GroundTheory.Heights₂.Heights.Targets


