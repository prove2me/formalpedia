-- Prove2me | Definitions.Def_GreedNorm_IsAlphaGreedyRun
-- name    : GreedNorm_IsAlphaGreedyRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:47.15219+00:00
-- url     : https://prove2.me/theorems/f84a3fb3-0993-497f-8705-729e2c23a3d3
-- title:
--   Run of $\alpha$-Greedy
-- statement:
--   A run of **$\alpha$-Greedy** is a sequence $e_1,\dots,e_r$ such that each $e_k$ is an $\alpha$-augmentation of $\{e_1,\dots,e_{k-1}\}$ (starting from $A=\emptyset$) and the final set $\{e_1,\dots,e_r\}$ is maximally feasible.
--
--   **Formalization Note** The run is a `List E`; the output is its set of elements.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 3.10, p.8 (PDF 10)

import Mathlib
import Definitions.Def_GreedNorm_IsAlphaAug

namespace GreedNorm

/-- **A run of `α`-Greedy**: the list `e_1, …, e_r` of added elements, where each `e_k` is an
`α`-augmentation of `{e_1, …, e_{k−1}}` (starting from `A = ∅`), and the final set is maximally
feasible (`F(A) = ∅`).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 3.10, p.8 (PDF 10): "start with A = ∅; then iteratively add to A an α-augmentation
of A until A is maximally feasible."

**Formalization Note** The run is a `List E`; the set after `k` steps is
`(es.take k).toFinset` and the output is `es.toFinset`. Every step adds an element outside the
current set, so the list has no repetitions. -/
def IsAlphaGreedyRun {E : Type} [Fintype E] [DecidableEq E] {p : ℕ} (α : ℝ)
    (h : Finset E → ℝ) (M : Fin p → Matroid E) (es : List E) : Prop :=
  (∀ (k : ℕ) (hk : k < es.length), IsAlphaAug α h M (es.take k).toFinset (es[k]'hk)) ∧
    Feasible M es.toFinset = ∅

end GreedNorm


