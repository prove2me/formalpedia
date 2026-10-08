-- Prove2me | Definitions.Def_prefixRevenueRebuild
-- name    : prefixRevenueRebuild
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-07T19:48:35.15655+00:00
-- url     : https://prove2.me/theorems/29a9542e-b89d-4343-8f62-1ffd4f5be351
-- title:
--   prefixRevenueRebuild
-- statement:
--   Automatically extracted helper definition prefixRevenueRebuild from oversized parent candidate 59ffb1bb8675d25e48599cc53041274ab0775a9f9692cf9cf3e88f765f8bfe17.
-- source:
--   candidate-decomposition:4204a6a5-95d4-4ce8-a739-2e52d3e9523a:59ffb1bb8675d25e48599cc53041274ab0775a9f9692cf9cf3e88f765f8bfe17

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

def prefixRevenueRebuild (k : ℕ) :
    ℝ × (Finset.Icc 1 k → ℝ) → ℕ → ℝ := fun z j =>
  if hj : j ∈ Finset.Icc 1 k then z.2 ⟨j, hj⟩
  else if j = k + 1 then z.1 else 0


