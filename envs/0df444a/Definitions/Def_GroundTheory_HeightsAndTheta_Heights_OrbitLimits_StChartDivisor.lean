-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisor
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:12:10.841635+00:00
-- url     : https://prove2.me/theorems/a4503bbe-b878-4f7f-94a6-8622f304f795
-- title:
--   St Chart Divisor
-- statement:
--   Definitions and structural lemmas for St Chart Divisor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartDivisor.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongChartLimit
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
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre divSupp IsHorizontal
  multAt PBlk oneLine fsLine Xc)
open GroundTheory.Heights₂.Heights (varInt localMult IsDegZeroSmooth segreChartSet segreChartComponents chartLift planeBump)
def ChartDivisorCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin n → (Fin m → ℂ) → ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSectionOn P A s →
    IsDegZeroSmooth g → 0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    (∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) →
      ∑ J ∈ segreChartComponents P σ i,
          ∑ᶠ (W : Ideal (MvPolynomial (Fin m) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {chartSection σ i s}) W : ℝ) * varInt W n G Φ =
        ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g
end GroundTheory.Heights₂.Heights.Targets


