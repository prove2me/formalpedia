-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisorLength
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisorLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:24.308593+00:00
-- url     : https://prove2.me/theorems/c1518c32-fc25-40d7-925c-502e4447d947
-- title:
--   St Chart Divisor Length
-- statement:
--   Definitions and structural lemmas for St Chart Divisor Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartDivisorLength.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal multAt PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartComponents localMult)
open Classical in

def ChartDivisorLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        ∑ J ∈ (segreChartComponents P σ i).filter (fun J => J ≤ W'),
            localMult (J ⊔ Ideal.span {chartSection σ i s}) W' =
          multAt (P ⊔ Ideal.span {s}) W
end GroundTheory.Heights₂.Heights.Targets


