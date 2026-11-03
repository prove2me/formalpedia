-- Prove2me | Definitions.Def_levy_foundations_arrival
-- name    : levy_foundations_arrival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:39:40.944006+00:00
-- url     : https://prove2.me/theorems/6e44c998-baed-4c09-a5d4-119500900b48
-- title:
--   Cumulative interarrival time
-- statement:
--   Cumulative interarrival time.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L75

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
namespace LevyFoundations
/-- The n-th jump time is the sum of the first n+1 interarrivals. -/
def arrival {Ω : Type*} (τ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), τ i ω
end LevyFoundations


