-- Prove2me | Definitions.Def_QWildMatch_Supplement_regimeCount
-- name    : QWildMatch_Supplement_regimeCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:19:47.645649+00:00
-- url     : https://prove2.me/theorems/bdf9e10a-4a91-46db-b627-e670b9976942
-- title:
--   Number of maximal constant-value regimes of a sequence
-- statement:
--   For a real sequence $D(0),\dots,D(U)$, the number of **consecutive maximal constant-value regimes** is
--   $$1+\#\{u\in\{0,\dots,U-1\}: D(u+1)\ne D(u)\},$$
--   the number of maximal runs of equal consecutive values. A sequence that returns to an earlier value starts a new regime, so this is not the number of distinct values.
--
--   It is the quantity bounded in Theorem 5.1.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…1f96), Theorem 5.1, p.7

import Mathlib

namespace QWildMatch.Supplement

/-- The number of consecutive maximal constant-value regimes of a sequence `D(0), …, D(U)` (Zhao, Chen, Li,
Kong, Peng, Yu, Yue, STOC 2027 submission (file sha256 9e87a9dd…), Theorem 5.1, p.7): one more than the
number of steps `u < U` with `D(u + 1) ≠ D(u)`. It counts maximal runs of equal consecutive values, not
distinct values. -/
noncomputable def regimeCount (D : ℕ → ℝ) (U : ℕ) : ℕ :=
  1 + ((Finset.range U).filter fun u => D (u + 1) ≠ D u).card

end QWildMatch.Supplement


