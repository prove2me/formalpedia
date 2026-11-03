-- Prove2me | Definitions.Def_SparseBatchBandit_maxArm
-- name    : SparseBatchBandit_maxArm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:00.837165+00:00
-- url     : https://prove2.me/theorems/9d20ffb6-8481-46a2-9599-bcface0fc009
-- title:
--   Maximum over the arms
-- statement:
--   For $f:[K]\to\mathbb R$ this is $\max_{a\in[K]}f(a)$. The arm set is nonempty by the instance `NeZero K`.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Definition 1, p.8; §4.2.3, p.18

import Mathlib

namespace SparseBatchBandit

/-- The maximum `max_{a ∈ [K]} f(a)` of a function of the arm, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Definition 1, p.8 (PDF 8) and
§4.2.3, p.18 (PDF 18). `NeZero K` makes the arm set nonempty. -/
def maxArm {K : ℕ} [NeZero K] (f : Fin K → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

end SparseBatchBandit


