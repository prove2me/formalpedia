-- Prove2me | Definitions.Def_SparseHistComm_Lambda
-- name    : SparseHistComm_Lambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:07.985849+00:00
-- url     : https://prove2.me/theorems/71b647ca-791b-4bc7-8120-37daa9284f1b
-- title:
--   Homogeneous coefficient $\Lambda_{n,k,D}(\delta)$
-- statement:
--   The **homogeneous coefficient** is the value of the optimization
--   $$
--   \Lambda_{n,k,D}(\delta) := \min_{\mathcal L(R),\, p_R}\ n\, E_R\Big[\sum_{j=0}^k j\, p_{R,j}\Big] \quad \text{subject to} \quad E_R\Big[\Pr_{J_1,\dots,J_n \text{ i.i.d.} \sim p_R}\Big\{\sum_{i=1}^n J_i \ge nk - \lfloor nD\rfloor\Big\}\Big] \ge 1 - \delta ,
--   $$
--   over a public randomization $R$ and a conditional level law $p_R = (p_{R,0},\dots,p_{R,k})$: the smallest expected total covering level of a randomized covering scheme in which, given $R$, every user draws its level independently from the same law. It is the leading coefficient of the homogeneous communication complexity.
--
--   **Formalization Note** Objective and constraint depend on $(R, p_R)$ only through the law $\nu$ of $p_R$, a probability measure on the probability simplex of $\{0,\dots,k\}$; the minimum is written as an infimum over $\nu$ (the paper's Lemma 3 shows it is attained, so the value agrees). Both integrands are continuous on the compact simplex, hence integrable for every $\nu$. For $\delta \ge 0$ the feasible set is nonempty (a point mass at the level-$k$ law succeeds with probability one) and bounded below by $0$; for $\delta \ge 1$ the value is $0$. The restriction $\delta < 1$ is not built in, because Theorem 3 evaluates $\Lambda$ at a relaxed failure probability.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (12), p.7

import Mathlib
import Definitions.Def_SparseHistComm_levelSucc
import Definitions.Def_SparseHistComm_levelMean
open MeasureTheory

namespace SparseHistComm

/-- The **homogeneous coefficient** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (12), p.7):
`Λ_{n,k,D}(δ) := min_{L(R), p_R} n·E_R[∑_{j=0}^k j·p_{R,j}]` subject to
`E_R[Pr_{J₁,…,Jₙ i.i.d. ∼ p_R}{∑ᵢ Jᵢ ≥ nk − ⌊nD⌋}] ≥ 1 − δ`.

**Formalization Note** The objective and the constraint depend on the public randomness `R` and
the conditional level law `p_R` only through the law `ν` of `p_R`, a probability measure on the
probability simplex of `{0, …, k}` (Mathlib's `stdSimplex ℝ (Fin (k+1))`, with its Borel
structure). So the minimum over `(L(R), p_R)` is written as an infimum over `ν`; the paper's
Lemma 3 (p.10) shows it is attained, so the value is the same. Both integrands are continuous on
the compact simplex, hence integrable for every `ν`. For `δ ≥ 0` the feasible set is nonempty (the
point mass at the level-`k` law succeeds with probability one) and bounded below by `0`, so the
`sInf` is a genuine infimum; for `δ ≥ 1` it is `0` (the point mass at level `0`). `δ < 1` is not
built in: Theorem 3 evaluates `Λ` at a relaxed failure probability. -/
noncomputable def Lambda (n k : ℕ) (D δ : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ ν : Measure (stdSimplex ℝ (Fin (k + 1))), IsProbabilityMeasure ν ∧
    1 - δ ≤ ∫ p, levelSucc n k D p ∂ν ∧ c = n * ∫ p, levelMean k p ∂ν}

end SparseHistComm


