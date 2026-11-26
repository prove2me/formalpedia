-- Prove2me | Definitions.Def_B1s_fried_crossing_9_03
-- name    : B1s_fried_crossing_9_03
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:37:27.720086+00:00
-- url     : https://prove2.me/theorems/01bb0fba-de9d-49b9-892f-38c8e00ad587
-- title:
--   fried crossing 9 03
-- statement:
--   Definitions and structural lemmas for fried crossing 9 03, from Ben Lawton (blawton/fried-conj-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Resonance-cluster conditional reduction for a proposed counterexample to Fried's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean

import Definitions.Def_B1s_fried_statement_defs_9_14
set_option autoImplicit true
set_option linter.style.header false
namespace FriedCrossing
open Filter Topology Matrix
namespace TorsionCore
variable {K : Type*} [Field K]
end TorsionCore
namespace OrderCount
variable {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup V₃] [Module K V₃]
end OrderCount
namespace Crossing
end Crossing
namespace RateRatio
def LinearArrival (f : ℝ → ℝ) (c σ : ℝ) : Prop :=
  Tendsto (fun τ => f τ / (τ - σ)) (𝓝[≠] σ) (𝓝 c)
end RateRatio
namespace Capstone
open TorsionCore OrderCount Crossing RateRatio
end Capstone
end FriedCrossing


