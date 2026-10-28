-- Prove2me | Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
-- name    : D1Bound5_FiniteHomogeneousRatio_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:05:46.154111+00:00
-- url     : https://prove2.me/theorems/600b6354-c1e6-4927-8ec4-02988d40d64c
-- title:
--   Finite Homogeneous Ratio
-- statement:
--   Exact reciprocal q for the five unbounded first-pair regions. The named objects in this bundle include `finiteHomogeneousRatioWeight`, `fiveRegionAnchorRatio`.
-- source:
--   D1Bound5/FiniteHomogeneousRatio.lean, lines 7-8, SHA-256 15c96a58b594b4317eb87dac7d3be380eb2b464b0233e171dc57af6894fda59b; D1Bound5/FiniteHomogeneousRatio.lean, lines 34-35, SHA-256 15c96a58b594b4317eb87dac7d3be380eb2b464b0233e171dc57af6894fda59b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
noncomputable section

namespace D1Bound5

def finiteHomogeneousRatioWeight (n : ℕ) (v : Fin (n+1) → ℤ) (r : ℝ) : ℝ :=
  ∑ j, |(v j : ℝ)| *r^(j : ℕ)





/-- Exact reciprocal q for the five unbounded first-pair regions. -/
def fiveRegionAnchorRatio : Fin 5 → ℝ := ![1/8,3/8,7/12,2/3,17/18]





end D1Bound5
end


