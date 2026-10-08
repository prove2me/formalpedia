-- Prove2me | Definitions.Def_GivenDegreeSeq_FixedPoint_ClassLn
-- name    : GivenDegreeSeq_FixedPoint_ClassLn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:50:57.439195+00:00
-- url     : https://prove2.me/theorems/c0132fee-5ac5-4b15-b9ad-af7ce3c28d54
-- title:
--   The $L^\infty$ operator norm $|A|_\infty=\max_i\sum_j|a_{ij}|$ and the matrix class $\mathcal L_n(\delta)$
-- statement:
--   For an $n\times n$ real matrix $A=(a_{ij})_{1\le i,j\le n}$, the **$L^\infty$ operator norm** is $|A|_\infty:=\max_{|x|_\infty\le1}|Ax|_\infty$, where $|x|_\infty=\max_i|x_i|$. It equals the maximal absolute row sum,
--   $$|A|_\infty=\max_{1\le i\le n}\sum_{j=1}^n|a_{ij}|,$$
--   and this row-sum expression is taken as the definition.
--
--   Given $\delta>0$, the matrix $A$ belongs to the **class $\mathcal L_n(\delta)$** if $|A|_\infty\le1$ and, for each $1\le i\ne j\le n$,
--   $$a_{ii}\ge\delta\qquad\text{and}\qquad a_{ij}\le-\frac{\delta}{n-1}.$$
--
--   These matrices are diagonally dominant with uniformly negative off-diagonal entries; the product of two of them is a strict contraction for the $L^\infty$ operator norm (Lemma 2.1), which drives the convergence of the fixed-point iteration for the $\beta$-model maximum likelihood estimate.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℝ` with indices $0,\dots,n-1$. The norm is the explicit row-sum supremum, which is $0$ when $n=0$. The diagonal condition is required for every index $i$; for $n\ge2$ (the only case used) every index lies in a pair $i\ne j$, so this is the paper's condition. The quantity $n-1$ is computed in $\mathbb R$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 11, §2 (definition of |A|∞ and of L_n(δ))

import Mathlib

namespace GivenDegreeSeq.FixedPoint

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5, p. 11 (§2): the L∞ operator norm of an `n × n` real matrix and the
class `L_n(δ)`. -/

/-- The L∞ operator norm `|A|∞ = max_{|x|∞ ≤ 1} |Ax|∞` of an `n × n` real matrix, written as
the maximal absolute row sum `max_i Σ_j |a_ij|` (the identity stated on p. 11). For `n = 0`
the supremum over the empty index set is `0`. -/
noncomputable def matNormInf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ i : Fin n, ∑ j : Fin n, |A i j|

/-- The class `L_n(δ)` (p. 11): `|A|∞ ≤ 1`, every diagonal entry is at least `δ`, and every
off-diagonal entry is at most `−δ/(n − 1)`. The paper quantifies over `1 ≤ i ≠ j ≤ n`;
for `n ≥ 2` every index lies in such a pair, so the diagonal condition is stated for every `i`. -/
def classLn (n : ℕ) (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  matNormInf A ≤ 1 ∧ (∀ i, δ ≤ A i i) ∧ (∀ i j, i ≠ j → A i j ≤ -δ / ((n : ℝ) - 1))

end GivenDegreeSeq.FixedPoint


