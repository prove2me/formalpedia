-- Prove2me | Definitions.Def_SennottDP_MarkovCost_Costs
-- name    : SennottDP_MarkovCost_Costs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T13:41:42.179632+00:00
-- url     : https://prove2.me/theorems/f27bec93-890a-42db-933c-1adcca717c14
-- title:
--   Markov chains with costs: first passage costs $c_{iG}$, average costs $J^{(n)}_i$ and $J_R$, and $z$ standard chains
-- statement:
--   Attach to each state $i$ of a Markov chain $\Gamma$ on a countable set $S$ a finite nonnegative cost $C(i)$.
--
--   1. The expected cost per unit time over $[0, n-1]$ from $X_0 = i$ is
--   $$ J^{(n)}_i = \frac1n\, E\Big[\sum_{t=0}^{n-1} C(X_t) \,\Big|\, X_0 = i\Big] = \frac1n \sum_{t=0}^{n-1} \sum_j P^{(t)}_{ij} C(j), \qquad n \ge 1. $$
--   2. For a nonempty $G \subseteq S$ with $m_{iG} < \infty$, $c_{iG}$ is the expected cost of a first passage from $i$ to $G$, $E\big[\sum_{t=0}^{T_{iG}-1} C(X_t) \mid X_0 = i\big]$: the cost is incurred at times $0, \dots, T_{iG}-1$. For $G = \{j\}$ it is written $c_{ij}$.
--   3. For a positive recurrent class $R$ with steady state probabilities $\pi_j$, the average cost on $R$ is the finite or infinite constant
--   $$ J_R = \sum_{j \in R} \pi_j C(j). $$
--   4. The chain is **$z$ standard** if there is a distinguished state $z$ with $m_{iz} < \infty$ and $c_{iz} < \infty$ for all $i \in S$ (including $i = z$, the expected return time and return cost).
--
--   These quantities are the cost counterparts of first passage times and the hypotheses under which average cost optimality results are proved in the book.
--
--   **Formalization Note** All quantities are `ℝ≥0∞`-valued. $c_{iG}$ is computed over first passage paths $x_0 = i, x_1, \dots, x_t$ ($t\ge1$, $x_1,\dots,x_{t-1}\notin G$, $x_t \in G$), each weighted by its probability and charged $C(x_0)+\dots+C(x_{t-1})$; this is the expected first passage cost whenever $P(T_{iG}<\infty)=1$, in particular when $m_{iG}<\infty$, which is the only case in which the book (and every statement here) uses $c_{iG}$. For $n = 0$ the Lean value of $J^{(0)}_i$ is $0$; only $n \ge 1$ is meaningful.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 298, Section C.2 (C.11) and c_iG; p. 298, Proposition C.2.1(i) (J_R); p. 301, Definition C.2.5

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal

namespace SennottDP.MarkovCost

variable {S : Type} [Countable S]

open Classical in
/-- Sennott (1999), p. 298: `c_{iG}`, the expected cost of a first passage from `i` to `G`,
`E[∑_{t=0}^{T_{iG}-1} C(X_t) | X_0 = i]`, where each state `k` carries a finite nonnegative cost
`C(k)`. It is computed over the first passage paths `x_0 = i, x_1, …, x_t` (`t ≥ 1`,
`x_1, …, x_{t-1} ∉ G`, `x_t ∈ G`), each weighted by its probability and charged
`C(x_0) + ⋯ + C(x_{t-1})`. The book defines `c_{iG}` only when `m_{iG} < ∞` (then
`T_{iG} < ∞` with probability one and this is the expectation); every result of this development
uses `passageCost` only under that proviso. -/
noncomputable def passageCost (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' x : Fin (t + 1) → S,
    if t ≠ 0 ∧ x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → s.val < t → x s ∉ G) ∧
        x (Fin.last t) ∈ G
    then pathProb M x * ∑ s : Fin t, (C (x s.castSucc) : ℝ≥0∞) else 0

/-- Sennott (1999), (C.11), p. 298: `J^{(n)}_i = (1/n) E[∑_{t=0}^{n-1} C(X_t) | X_0 = i]
= ∑_j C(j) Q^{(n)}_{ij}`, the expected cost per unit time in `[0, n − 1]` from `i`, in `[0, ∞]`
(meaningful for `n ≥ 1`). -/
noncomputable def avgCostN (M : MC S) (C : S → ℝ≥0) (n : ℕ) (i : S) : ℝ≥0∞ :=
  (∑ t ∈ Finset.range n, ∑' j, nStep M t i j * (C j : ℝ≥0∞)) / (n : ℝ≥0∞)

/-- Sennott (1999), Proposition C.2.1(i), p. 298: the average cost on a positive recurrent class
`R`, `J_R = ∑_{j ∈ R} π_j C(j)`, a finite or infinite constant. -/
noncomputable def classAvgCost (M : MC S) (C : S → ℝ≥0) (R : Set S) : ℝ≥0∞ :=
  ∑' j : R, steadyState M j * (C j : ℝ≥0∞)

/-- Sennott (1999), Definition C.2.5, p. 301: the Markov chain with costs is `z` standard if
`m_{iz} < ∞` and `c_{iz} < ∞` for all `i ∈ S` (including `i = z`: the expected return time to `z`
and the expected cost of a return to `z` are finite). -/
def IsZStandard (M : MC S) (C : S → ℝ≥0) (z : S) : Prop :=
  ∀ i, meanPassage M {z} i < ⊤ ∧ passageCost M C {z} i < ⊤

end SennottDP.MarkovCost


