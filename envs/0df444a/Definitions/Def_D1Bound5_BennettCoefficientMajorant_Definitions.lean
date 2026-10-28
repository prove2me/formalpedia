-- Prove2me | Definitions.Def_D1Bound5_BennettCoefficientMajorant_Definitions
-- name    : D1Bound5_BennettCoefficientMajorant_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:23:23.548982+00:00
-- url     : https://prove2.me/theorems/55442128-69be-4393-9378-f7d92e358cc4
-- title:
--   Bennett Coefficient Majorant
-- statement:
--   Positive numerator majorant for every local coefficient of order at most k. The named objects in this bundle include `bennettNumeratorMajorant`.
-- source:
--   D1Bound5/BennettCoefficientMajorant.lean, lines 61-63, SHA-256 52f2dc90c9817830bd21c1880dfcf0e6477a59dce71efbcde2deafd50273de8e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5







/-- Positive numerator majorant for every local coefficient of order at most k. -/
noncomputable def bennettNumeratorMajorant (U : ℝ) (k : ℕ) : PowerSeries ℝ :=
  PowerSeries.C U⁻¹ * (PowerSeries.C U + PowerSeries.X) ^ (k + 1)









end D1Bound5
end


