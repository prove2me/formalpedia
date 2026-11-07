-- Prove2me | Definitions.Def_NoPerfectRandComp_expCost
-- name    : NoPerfectRandComp_expCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:17.038592+00:00
-- url     : https://prove2.me/theorems/9d4f1d98-9267-401d-9204-46ea934de3b1
-- title:
--   Expected cost $\mathrm{cost}(A,x)$ of a randomised algorithm
-- statement:
--   For a randomised algorithm $A$ (a distribution over deterministic decision trees $T$) and an input $x$, the **expected cost** is the expected number of queries made on $x$:
--   $$
--   \mathrm{cost}(A,x) = \sum_T A(T)\,\mathrm{queries}(T,x) \in [0,\infty].
--   $$
--   It enters the mission through the linearised complexity $\mathrm{LR}$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.1, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
open scoped ENNReal

namespace NoPerfectRandComp

/-- The expected cost `cost(A, x)` of a randomised algorithm on input `x` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.1, p.4):
the expected number of queries made on `x`, `∑_T A(T) · queries(T, x)`, valued in `ℝ≥0∞`. -/
noncomputable def expCost {ι α ω : Type} (A : QAlgorithms.RandDecisionTree ι α ω)
    (x : ι → α) : ℝ≥0∞ :=
  ∑' T, A T * (T.queries x : ℝ≥0∞)

end NoPerfectRandComp


