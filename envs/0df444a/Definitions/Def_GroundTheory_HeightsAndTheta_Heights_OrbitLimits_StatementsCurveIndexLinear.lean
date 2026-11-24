-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:35.645686+00:00
-- url     : https://prove2.me/theorems/0bd09450-1ef1-47ec-b0e3-720274eea339
-- title:
--   Statements Curve Index Linear
-- statement:
--   Definitions and structural lemmas for Statements Curve Index Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsCurveIndexLinear.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def CurveIndexLinear.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k),
    IsArithVar (mCoordIdeal y) 1 → (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (∀ a a' : K → ℤ, chartIndexLog y c (a + a') 1 = chartIndexLog y c a 1 + chartIndexLog y c a' 1) ∧
      ∀ (a : K → ℤ) (τ : ℕ), chartIndexLog y c a τ = τ * chartIndexLog y c a 1
namespace CurveIndexLinear
end CurveIndexLinear
end GroundTheory.Heights₂.Heights.Targets


