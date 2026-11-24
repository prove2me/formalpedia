-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegral
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:30.823363+00:00
-- url     : https://prove2.me/theorems/d8093ea4-4af7-4684-9dc3-892332515bae
-- title:
--   St Segre Chart Integral
-- statement:
--   Definitions and structural lemmas for St Segre Chart Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StSegreChartIntegral.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_oneLine

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
namespace GroundTheory.Heights₂.Heights
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre PBlk oneLine
  isSmoothHerm_oneLine)
def SegreChartIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin (e + 1) → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin (e + 1) → (Fin m → ℂ) → ℝ),
    IsArithVar P (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g → 0 < δ →
    ((∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) ∨
      ∀ z, ‖segre z i‖ < δ * ‖segre z‖ → pot L 0 z = 0) →
    (∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) →
      ptsIntegral P (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ
end GroundTheory.Heights₂.Heights


