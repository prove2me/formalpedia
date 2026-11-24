-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:21.091701+00:00
-- url     : https://prove2.me/theorems/91f2ee55-b185-4217-9707-08c0e8bab98b
-- title:
--   Eval Cone Chart Monomial Ne Zero
-- statement:
--   Definitions and structural lemmas for Eval Cone Chart Monomial Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace BoundedMonomials
def chartNorm (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (e : MvPolynomial (Coord n) ℤ) (z : Cone n ℂ) : ℝ :=
  ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z)
def unitChart (c : (k : ι) → Fin (n k + 1)) : Set (Cone n ℂ) :=
  {z | (∀ k, z k (c k) = 1) ∧ ∀ k i, ‖z k i‖ ≤ 1}
end BoundedMonomials
end
end GroundTheory.Heights₂.Heights


