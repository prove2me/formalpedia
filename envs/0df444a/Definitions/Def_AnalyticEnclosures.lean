-- Prove2me | Definitions.Def_AnalyticEnclosures
-- name    : AnalyticEnclosures
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/d5fc858f-6a13-4f0c-a404-bd80052f71ab
-- title:
--   AnalyticEnclosures definitions
-- statement:
--   Rational Taylor certificates imply inequalities for the actual real logarithm and exponential. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/AnalyticEnclosures.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/AnalyticEnclosures.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
set_option autoImplicit true
namespace AnalyticEnclosures
open scoped BigOperators
def expPoly (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ)
def expUpper (x : ℚ) (n : ℕ) : ℚ :=
  expPoly x n + x ^ n * (n + 1) / ((n.factorial : ℚ) * n)
end AnalyticEnclosures


