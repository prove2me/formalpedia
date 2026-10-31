-- Prove2me | Definitions.Def_TestScoreSubmod_repScore
-- name    : TestScoreSubmod_repScore
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:54.152992+00:00
-- url     : https://prove2.me/theorems/bbc33716-6f18-478c-b669-ef364eae4a0b
-- title:
--   Replication test score $a_i$, Definition 2
-- statement:
--   For an item $i$ with performance law $P_i$ and a number $r$ of replicas, let $X_i^{(1)},\dots,X_i^{(r)}$ be independent copies with law $P_i$. The **replication test score** with $r$ replicas is
--
--   $$
--   a_i^{(r)}=\mathbb E\bigl[g(X_i^{(1)},\dots,X_i^{(r)},\varphi,\dots,\varphi)\bigr],
--   $$
--
--   the expected value of a virtual group made of $r$ independent replicas of item $i$. The score of Definition 2 for the cardinality parameter $k$ is $a_i=a_i^{(k)}$; the proof of Lemma 4 also uses $a_i^{(k-1)}$.
--
--   A replication score depends only on $g$, $k$ and $P_i$, so it can be computed item by item.
--
--   **Formalization Note** $\varphi=0$. The paper's "distribution $F_i$" is $P_i$. For $r=0$ the score is $g(0)$. Every use has $r\le n$.
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Definition 2, eq. (7), p.17

import Mathlib
import Definitions.Def_TestScoreSubmod_pad

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **Replication test score** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Definition 2, eq. (7),
p.17: "aᵢ = E[g(Xᵢ⁽¹⁾, Xᵢ⁽²⁾, …, Xᵢ⁽ᵏ⁾, φ, …, φ)] where Xᵢ⁽¹⁾, …, Xᵢ⁽ᵏ⁾ are independent and
identically distributed random variables with distribution Fᵢ").

`repScore g P r i` is the expected value of `g` at `r` independent replicas of item `i`'s
performance, padded with `φ = 0` to `n` coordinates. The replication test score of
Definition 2 for cardinality parameter `k` is `repScore g P k i`; the proof of Lemma 4 also uses
`r = k − 1` replicas.

**Formalization Note** The typo "distribution Fᵢ" is read as `Pᵢ`, the law of item `i`.
`φ = 0`. The `r` replicas are the product measure `Measure.pi (fun _ : Fin r => P i)`; for
`r = 0` it is the Dirac mass at the empty vector and the score is `g 0`. Every use has
`r ≤ n`. -/
noncomputable def repScore {n : ℕ} (g : (Fin n → ℝ≥0) → ℝ) (P : Fin n → Measure ℝ≥0)
    (r : ℕ) (i : Fin n) : ℝ :=
  ∫ y, g (pad y) ∂(Measure.pi fun _ : Fin r => P i)

end TestScoreSubmod


