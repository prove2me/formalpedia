-- Prove2me | Definitions.Def_QPSpinParisi_MSet
-- name    : QPSpinParisi_MSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:36.956691+00:00
-- url     : https://prove2.me/theorems/0be50919-76bd-4ce0-9af5-103119abba51
-- title:
--   The class $\mathcal M$ of distribution functions, (3.15)
-- statement:
--   The positive-temperature order parameters:
--   $$\mathcal M=\{\alpha:[0,1]\to[0,1]:\ \alpha\text{ nondecreasing and right-continuous},\ \alpha(1)=1\}.$$
--   These are the cumulative distribution functions on $[0,1]$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.15), p.17 (PDF p.17)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The class `M = {α : [0,1] → [0,1] : α nondecreasing and right-continuous, α(1) = 1}` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.15), p.17, PDF p.17). -/
def MSet : Set (Icc (0 : ℝ) 1 → ℝ) :=
  {α | Monotone α ∧ (∀ t, α t ∈ Icc (0 : ℝ) 1) ∧ (∀ t, ContinuousWithinAt α (Ioi t) t) ∧
    α (1 : Icc (0 : ℝ) 1) = 1}

end QPSpinParisi


