-- Prove2me | Definitions.Def_extendFinitePrefix
-- name    : extendFinitePrefix
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T04:53:29.431985+00:00
-- url     : https://prove2.me/theorems/178bcd5c-42de-4e8d-b9d9-fd7a8ddd9fc9
-- title:
--   extendFinitePrefix
-- statement:
--   Automatically extracted helper definition extendFinitePrefix from oversized parent candidate b2fb5cabfd16d9c2958d593389ef6b90929528470bf9810b5ec761f9c29808fe.
-- source:
--   candidate-decomposition:05585a65-c923-41b0-9456-1fb483784d2c:b2fb5cabfd16d9c2958d593389ef6b90929528470bf9810b5ec761f9c29808fe

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

def extendFinitePrefix (S : Finset ℕ) (z : S → ℝ) (i : ℕ) : ℝ :=
  if hi : i ∈ S then z ⟨i, hi⟩ else 0


