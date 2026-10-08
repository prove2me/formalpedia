-- Prove2me | Definitions.Def_PariMutuel_Consensus_Market
-- name    : PariMutuel_Consensus_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:45:49.575769+00:00
-- url     : https://prove2.me/theorems/98d613dc-e619-485d-b88e-e0a010b930b4
-- title:
--   Pari-mutuel market and its equilibrium probabilities and bets (1)–(3)
-- statement:
--   A **pari-mutuel market** consists of $m$ bettors $B_1,\dots,B_m$ and $n$ horses $H_1,\dots,H_n$, together with
--
--   1. an $m\times n$ **subjective probability matrix** $P=(p_{ij})$, where $p_{ij}$ is the probability, in the opinion of $B_i$, that $H_j$ wins the race; each row is a probability distribution, $p_{ij}\ge 0$ and $\sum_{j=1}^n p_{ij}=1$;
--   2. **budgets** $b_i>0$, normalized so that $\sum_{i=1}^m b_i=1$;
--   3. the assumption that each column of $P$ contains at least one positive entry.
--
--   Nonnegative numbers $\pi_j$ (track probabilities) and $\beta_{ij}$ (the amount $B_i$ bets on $H_j$) are **equilibrium probabilities and bets** when
--
--   $$
--   \text{(1)}\ \sum_{j=1}^n \beta_{ij}=b_i,\qquad \text{(2)}\ \sum_{i=1}^m \beta_{ij}=\pi_j,\qquad \text{(3)}\ \text{if } \mu_i=\max_s \frac{p_{is}}{\pi_s} \text{ and } \beta_{ij}>0, \text{ then } \mu_i=\frac{p_{ij}}{\pi_j}.
--   $$
--
--   Condition (1) is the budget relation, (2) the pari-mutuel condition, and (3) says each bettor bets only on horses of maximal subjective expectation $p_{ij}/\pi_j$.
--
--   This is the model of the whole paper; existence and uniqueness of equilibrium probabilities are stated for it.
--
--   **Formalization Note** Bettors and horses are indexed by `Fin m` and `Fin n` (from 0, not 1). All standing assumptions are fields of the structure `Market`. Condition (3) is written multiplied out: whenever $\beta_{ij}>0$, $p_{is}\pi_j\le p_{ij}\pi_s$ for every $s$. When every $\pi_s>0$ this is exactly (3); when some $\pi_s=0$ it is the page's reading $p_{is}/0=+\infty$ (a bettor with $p_{is}>0$ would then have infinite expectation on $H_s$ and could not bet elsewhere). Positivity of the $\pi_j$ is not part of the definition, as on the page ("Nonnegative numbers"). The lemma `univ_nonempty` records that there is at least one bettor, which follows from $\sum_i b_i=1$.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, pp. 165–166, model and conditions (1)–(3)

import Mathlib

namespace PariMutuel.Consensus

/-- A pari-mutuel market (Eisenberg–Gale 1959, pp. 165–166): `m` bettors `B_i` (indexed by `Fin m`)
and `n` horses `H_j` (indexed by `Fin n`; the paper indexes from 1, Lean from 0).
`P i j` is bettor `i`'s subjective probability that horse `j` wins, `b i` is bettor `i`'s budget.
Every standing assumption of the paper is a field: each row of `P` is a probability distribution
(p. 165, "subjective probability distribution"), each column of `P` has a positive entry (p. 166),
each budget is positive (p. 165), and the budgets sum to one (p. 166). -/
structure Market (m n : ℕ) where
  /-- The subjective probability matrix `P = (p_ij)`. -/
  P : Fin m → Fin n → ℝ
  /-- The budgets `b_i`. -/
  b : Fin m → ℝ
  P_nonneg : ∀ i j, 0 ≤ P i j
  P_row_sum : ∀ i, ∑ j, P i j = 1
  P_col_pos : ∀ j, ∃ i, 0 < P i j
  b_pos : ∀ i, 0 < b i
  b_sum : ∑ i, b i = 1

namespace Market

variable {m n : ℕ}

/-- There is at least one bettor, since the budgets sum to one. -/
theorem univ_nonempty (M : Market m n) : (Finset.univ : Finset (Fin m)).Nonempty := by
  rcases (Finset.univ : Finset (Fin m)).eq_empty_or_nonempty with h | h
  · have hs := M.b_sum
    rw [h, Finset.sum_empty] at hs
    norm_num at hs
  · exact h

/-- Equilibrium probabilities and bets (p. 166): nonnegative numbers `π j` and `β i j` satisfying
(1) the budget relation `∑_j β_ij = b_i`, (2) the pari-mutuel condition `∑_i β_ij = π_j`, and
(3) "if `μ_i = max_s p_is/π_s` and `β_ij > 0`, then `μ_i = p_ij/π_j`", written multiplied out:
whenever `β_ij > 0`, `p_is π_j ≤ p_ij π_s` for every horse `s`. This is the paper's (3) when all
`π_s > 0`, and its reading `p_is/0 = +∞` when some `π_s = 0`. Positivity of `π` is not assumed. -/
def IsEquilibrium (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ π j) ∧ (∀ i j, 0 ≤ β i j) ∧
  (∀ i, ∑ j, β i j = M.b i) ∧
  (∀ j, ∑ i, β i j = π j) ∧
  (∀ i j, 0 < β i j → ∀ s, M.P i s * π j ≤ M.P i j * π s)

end Market

end PariMutuel.Consensus


