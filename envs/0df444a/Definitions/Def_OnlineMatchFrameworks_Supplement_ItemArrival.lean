-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_ItemArrival
-- name    : OnlineMatchFrameworks_Supplement_ItemArrival
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:21:32.56377+00:00
-- url     : https://prove2.me/theorems/2e1605ee-3313-4584-a1b3-270b5fa067e8
-- title:
--   The star problem with item arrivals and its optimal expected reward
-- statement:
--   One customer waits for a known number $\theta\ge1$ of time steps. Each of the items $i$ has a weight $w_i\ge0$, a purchase probability $p_i$ and an arrival probability $q_i$. Initially no item is available. At each step every item that has not arrived becomes available with probability $q_i$, independently; then at most one available, never offered item may be offered. An offered item is bought with probability $p_i$, which earns $w_i$ and ends the process.
--
--   With $n$ steps left, $R$ the items not arrived and $B$ those available and never offered, the optimum is
--
--   $$
--   \mathrm{opt}_n(R,B)=\sum_{N\subseteq R}\Pr[N]\max\Bigl\{\mathrm{opt}_{n-1}(R',B'),\ \max_{i\in B'}\bigl(p_iw_i+(1-p_i)\mathrm{opt}_{n-1}(R',B'\setminus\{i\})\bigr)\Bigr\},
--   $$
--
--   where $\Pr[N]=\prod_{i\in N}q_i\prod_{i\in R\setminus N}(1-q_i)$, $R'=R\setminus N$, $B'=B\cup N$ and $\mathrm{opt}_0=0$. The optimal expected reward is $\mathrm{OPT}=\mathrm{opt}_\theta(U,\varnothing)$, the best over all adaptive policies.
--
--   **Formalization Note** The state is sufficient for optimal control, so the dynamic program equals the supremum over history-dependent randomized policies.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §5.3, pp.26–27

import Mathlib

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

/-- **The star problem with item arrivals.** arXiv:1907.03963v6, §5.3, pp.26–27. One customer has a known
deterministic patience `θ = patience`, counted in time steps. Item `i` has a weight `w i`, a purchase
probability `p i` and an arrival probability `q i`: at each step an item that is not yet available
becomes available with probability `q i`, independently. An available item may be offered once; at most
one item is offered per step. -/
structure ItemArrivalInstance (U : Type*) where
  /-- The weight `w_i`. -/
  w : U → ℝ
  /-- The matching probability `p_i`. -/
  p : U → ℝ
  /-- The arrival probability `q_i`. -/
  q : U → ℝ
  /-- The patience `θ`, a number of time steps. -/
  patience : ℕ
  w_nonneg : ∀ i, 0 ≤ w i
  p_nonneg : ∀ i, 0 ≤ p i
  p_le_one : ∀ i, p i ≤ 1
  q_nonneg : ∀ i, 0 ≤ q i
  q_le_one : ∀ i, q i ≤ 1
  one_le_patience : 1 ≤ patience

namespace ItemArrivalInstance

variable {U : Type*} [DecidableEq U]

/-- **Probability that exactly the items of `N` arrive in a step**, when `R` is the set of items that
have not arrived yet. arXiv:1907.03963v6, §5.3, p.27, "each item i becomes available independently
with probability q_i". -/
def arrivalProb (G : ItemArrivalInstance U) (R N : Finset U) : ℝ :=
  (∏ i ∈ N, G.q i) * ∏ i ∈ R \ N, (1 - G.q i)

/-- **The optimal expected reward from a state.** arXiv:1907.03963v6, §5.3, p.27. `optFrom n R B` is the
optimum with `n` steps left, when the items of `R` have not arrived and those of `B` have arrived and
were never offered. In a step the arrivals `N ⊆ R` are seen first; then nothing is offered, or one item
of `B ∪ N` is offered. An offer of `i` earns `w_i` and ends with probability `p_i`.

**Formalization Note.** This is the finite-horizon dynamic program. Its value is the supremum over
adaptive, possibly randomized, policies, because the state `(n, R, B)` is all that the future depends
on. -/
noncomputable def optFrom (G : ItemArrivalInstance U) : ℕ → Finset U → Finset U → ℝ
  | 0, _, _ => 0
  | n + 1, R, B =>
      ∑ N ∈ R.powerset, G.arrivalProb R N *
        (B ∪ N).fold max (G.optFrom n (R \ N) (B ∪ N))
          (fun i => G.p i * G.w i + (1 - G.p i) * G.optFrom n (R \ N) ((B ∪ N).erase i))

/-- **The optimal expected reward of the item-arrival problem.** arXiv:1907.03963v6, §5.3, p.27: `θ` steps,
and "immediately prior to time t = 1, no items are available". -/
noncomputable def OPT [Fintype U] (G : ItemArrivalInstance U) : ℝ :=
  G.optFrom G.patience Finset.univ ∅

end ItemArrivalInstance

end OnlineMatchFrameworks.Supplement


