-- Prove2me | Definitions.Def_RoundRobinEq_SubmodularBluff_Alg3
-- name    : RoundRobinEq_SubmodularBluff_Alg3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:22.524734+00:00
-- url     : https://prove2.me/theorems/41d08ed7-9ca3-4faf-895a-87d2fd01ab07
-- title:
--   p. 11, Algorithm 3 — prefix and suffix sets $X^j_-$, $Y^j_+$ and the greedy renaming of the deviating agent's bundle
-- statement:
--   Let $x_1,\dots,x_k$ and $y_1,\dots,y_k$ be two listings of goods. Following p. 11, write
--   $$X^j_-=\{x_1,\dots,x_j\},\qquad Y^j_+=\{y_j,\dots,y_k\},$$
--   with $X^0_-=\emptyset$ and $Y^{k+1}_+=\emptyset$.
--
--   Algorithm 3 (p. 11) renames the goods of a set $Y$ given $X=\{x_1,\dots,x_k\}$ and a valuation $v_i$: starting with $Z=Y$, for $j=|Y|,\dots,1$ it sets
--   $$y_j\in\arg\min_{g\in Z} v_i(g\mid\{x_1,\dots,x_{j-1}\}),\qquad Z\leftarrow Z\setminus\{y_j\}.$$
--   Equivalently, for every $j$ the good $y_j$ has the smallest marginal value $v_i(\,\cdot\mid X^{j-1}_-)$ among $y_1,\dots,y_j$.
--
--   This ordering of the deviating agent's bundle is the one used in Lemma 3.5 and in the proof of Theorem 3.7.
--
--   **Formalization Note.** Listings are 0-based functions `Fin k → M`. `prefixSet x j` is $\{x_0,\dots,x_{j-1}\}$, i.e. the paper's $X^j_-$; `suffixSet y j` is $\{y_j,\dots,y_{k-1}\}$, i.e. the paper's $Y^{j+1}_+$. `IsAlg3Order w x y` is the relational form of Algorithm 3: for all positions $t\le j$, $w(y_j\mid \mathrm{prefixSet}\ x\ j)\le w(y_t\mid \mathrm{prefixSet}\ x\ j)$. It holds for exactly the outputs of Algorithm 3 under some tie-breaking rule.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 11, Algorithm 3 and the notation X^j_−, X^j_+, Y^j_−, Y^j_+

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting

namespace RoundRobinEq.SubmodularBluff

/-- `prefixSet x j = {x_0, …, x_{j-1}}` for a 0-based listing `x : Fin k → M`; in the paper's
1-based notation (p. 11) this is `X^j_- = {x_1, …, x_j}`, and `prefixSet x 0 = X^0_- = ∅`. -/
def prefixSet {M : Type*} [DecidableEq M] {k : ℕ} (x : Fin k → M) (j : ℕ) : Finset M :=
  (Finset.univ.filter (fun t : Fin k => t.val < j)).image x

/-- `suffixSet y j = {y_j, …, y_{k-1}}` for a 0-based listing `y : Fin k → M`; in the paper's
1-based notation (p. 11) `suffixSet y (j-1)` is `Y^j_+ = {y_j, …, y_k}`, and
`suffixSet y k = Y^{k+1}_+ = ∅`. -/
def suffixSet {M : Type*} [DecidableEq M] {k : ℕ} (y : Fin k → M) (j : ℕ) : Finset M :=
  (Finset.univ.filter (fun t : Fin k => j ≤ t.val)).image y

/-- `y` is an output order of Algorithm 3 (p. 11) relative to `x`, for some tie-breaking: for
every position `j` (0-based), `y j` minimizes `w(g | {x_0, …, x_{j-1}})` over the goods
`g ∈ {y 0, …, y j}` (the goods not yet renamed when Algorithm 3 fixes position `j`). -/
def IsAlg3Order {M : Type*} [DecidableEq M] {k : ℕ} (w : Finset M → ℝ) (x y : Fin k → M) :
    Prop :=
  ∀ j t : Fin k, t ≤ j →
    RoundRobinEq.CancelableBluff.marginal w {y j} (prefixSet x j) ≤ RoundRobinEq.CancelableBluff.marginal w {y t} (prefixSet x j)

end RoundRobinEq.SubmodularBluff


