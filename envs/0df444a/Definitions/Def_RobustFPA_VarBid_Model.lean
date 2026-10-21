-- Prove2me | Definitions.Def_RobustFPA_VarBid_Model
-- name    : RobustFPA_VarBid_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:01.163975+00:00
-- url     : https://prove2.me/theorems/0c14f547-1999-4eae-ac70-33543f45aa04
-- title:
--   First-price payoff with random tie-breaking, expected utility, loss $l(b,B\mid v_1)$, maximal loss and minimax loss bid (pp. 8–11)
-- statement:
--   This file sets up bidder 1's decision problem in a first-price sealed-bid auction, following §§3–4 of Kasberger & Schlag.
--
--   There are $n \ge 2$ bidders. Bidder 1 has value $v_1$ and bids $b_1$; the other $n-1$ bidders bid $b_{-1} = (b_2,\dots,b_n)$. The highest bid wins and pays its bid, and ties are broken uniformly at random. Hence bidder 1's payoff is
--   $$
--   u_1(b_1, b_{-1}) = \begin{cases} \dfrac{1}{m}(v_1 - b_1) & \text{if } b_1 = \max_j b_j \text{ and } |\{k : b_k = b_1\}| = m,\\[4pt] 0 & \text{if } b_1 < \max_j b_j, \end{cases}
--   $$
--   where $m$ counts bidder 1 herself.
--
--   A **bid distribution** (environment) $B$ is a joint law of the opponents' bids, with no independence assumed. The **expected utility** of a bid is $u_1(b_1, B) = \int u_1(b_1, b_{-1})\,dB(b_{-1})$. The **loss** of $b_1$ in the environment $B$ is the gap to the best attainable expected utility,
--   $$
--   l(b_1, B \mid v_1) = \sup_{\bar b_1 \ge 0} u_1(\bar b_1, B) - u_1(b_1, B).
--   $$
--   Given an **ambiguity set** $\mathcal B$ of conceivable environments, the **maximal loss** of $b_1$ is $\sup_{B \in \mathcal B} l(b_1, B \mid v_1)$, and $b_1^*$ is a **minimax loss bid** if $b_1^* \ge 0$ and $b_1^*$ minimizes the maximal loss over all bids $b_1 \ge 0$.
--
--   These objects are independent of how the ambiguity set is built; every statement of the mission about robust bidding is phrased through them.
--
--   **Formalization Note.** The opponents are indexed by `Fin m` (bidders $2,\dots,n$, with $m = n-1$ in the rest of the mission) and bids are real numbers. The payoff is written as one case: if every opponent bid is at most $b$, bidder 1 receives $(v-b)/(k+1)$ where $k$ is the number of opponents bidding exactly $b$; otherwise $0$. The expected utility is the Bochner integral of this bounded measurable payoff. Best utility and maximal loss are real suprema (`sSup`): over non-negative bids the expected utility of a probability measure is at most $\max(v_1,0)$, and losses are at most $\max(v_1,0) + |v_1 - b|$, so on a nonempty ambiguity set of probability measures these suprema are genuine least upper bounds, not junk values. The minimax loss bid is a predicate, not a chosen value.
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), pp. 8–11, §3 (payoff u₁, p. 9) and §4 (loss l, p. 10; minimax loss bid, p. 11)

import Mathlib

open MeasureTheory

namespace RobustFPA.VarBid

/-- Payoff of bidder 1 in a first-price sealed-bid auction (Kasberger–Schlag, §3, p. 9).
Bidder 1 has value `v` and bids `b`; the `m` opponents bid `o : Fin m → ℝ`.
Bidder 1 wins if her bid is a highest bid; ties are broken uniformly at random, so with
`k` opponents tied at `b` she receives `(v - b) / (k + 1)`. Otherwise her payoff is `0`. -/
noncomputable def payoff {m : ℕ} (v b : ℝ) (o : Fin m → ℝ) : ℝ :=
  if ∀ j, o j ≤ b then
    (v - b) / (((Finset.univ.filter (fun j => o j = b)).card : ℝ) + 1)
  else 0

/-- Expected utility `u₁(b, B) = ∫ u₁(b, b₋₁) dB(b₋₁)` of the bid `b` against the joint
distribution `B` of the opponents' bids (p. 9). -/
noncomputable def expUtil {m : ℕ} (v b : ℝ) (B : Measure (Fin m → ℝ)) : ℝ :=
  ∫ o, payoff v b o ∂B

/-- Best attainable expected utility `sup_{b̄ ≥ 0} u₁(b̄, B)` against `B` (bids are non-negative). -/
noncomputable def bestUtil {m : ℕ} (v : ℝ) (B : Measure (Fin m → ℝ)) : ℝ :=
  sSup ((fun b' => expUtil v b' B) '' Set.Ici 0)

/-- Loss `l(b, B | v) = sup_{b̄ ≥ 0} u₁(b̄, B) − u₁(b, B)` (p. 10). -/
noncomputable def loss {m : ℕ} (v b : ℝ) (B : Measure (Fin m → ℝ)) : ℝ :=
  bestUtil v B - expUtil v b B

/-- Maximal loss `sup_{B ∈ 𝓑} l(b, B | v)` of the bid `b` over an ambiguity set `𝓑` (p. 10). -/
noncomputable def maxLoss {m : ℕ} (v b : ℝ) (𝓑 : Set (Measure (Fin m → ℝ))) : ℝ :=
  sSup ((fun B => loss v b B) '' 𝓑)

/-- `b` is a minimax loss bid for the ambiguity set `𝓑` (p. 11): `b ≥ 0` and `b` minimizes the
maximal loss among all non-negative bids. -/
def IsMinimaxLossBid {m : ℕ} (v : ℝ) (𝓑 : Set (Measure (Fin m → ℝ))) (b : ℝ) : Prop :=
  0 ≤ b ∧ ∀ b' : ℝ, 0 ≤ b' → maxLoss v b 𝓑 ≤ maxLoss v b' 𝓑

end RobustFPA.VarBid


