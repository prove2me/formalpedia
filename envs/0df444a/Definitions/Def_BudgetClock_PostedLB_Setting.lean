-- Prove2me | Definitions.Def_BudgetClock_PostedLB_Setting
-- name    : BudgetClock_PostedLB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:23:48.911834+00:00
-- url     : https://prove2.me/theorems/d22f91c7-5024-41c2-9a83-6f579ad65372
-- title:
--   §2 and App. B, pp. 5, 24–25 — additive valuations, deterministic posted-price mechanisms, their run, payment and budget feasibility
-- statement:
--   This file sets up the procurement model of §2 and the posted-price mechanisms of Appendix B.
--
--   There are $n$ sellers $N=\{0,1,\dots,n-1\}$. Seller $i$ has a private cost $c_i\ge 0$, the auctioneer has a budget $B$, and a valuation $v:2^N\to\mathbb R_{\ge 0}$ gives the value of buying the services of a set $S\subseteq N$. A valuation is **additive** if there are nonnegative per-seller values $v_i\ge 0$ with
--   $$v(S)=\sum_{i\in S}v_i\qquad\text{for all } S\subseteq N.$$
--
--   A **deterministic posted-price mechanism** approaches the sellers one at a time and makes each a single take-it-or-leave-it offer. The order and the prices may be adaptive: the mechanism is a rule that, given the history of earlier offers (which seller, which price, accepted or not), names the next seller and the price to offer, or stops. The mechanism knows the public data $n$, $B$ and $v$, but not the costs. A seller offered price $p_i$ **accepts if $p_i\ge c_i$** and rejects otherwise. A seller is approached at most once; the run stops as soon as the rule stops or proposes a seller already approached. The **output** $M(I)$ is the set of sellers who accepted, and the **payment** is the sum of the prices of the accepted offers.
--
--   A mechanism $M$ for additive valuations is **budget feasible** for the budget $B$ if on every instance of the class, i.e. for every additive $v$ and every cost profile $c\ge 0$,
--   $$\sum_{i\text{ accepted}}p_i\le B .$$
--
--   These objects are the class over which Theorem 13 is a lower bound.
--
--   **Formalization Note** Sellers are `Fin n`. A mechanism is `M : (Finset (Fin n) → ℝ) → PostedPrice n`, so it may depend on the valuation (and, since `n` and `B` are fixed outside it, on those too) but never on `c`. `PostedPrice n` has one field `next : List (Fin n × ℝ × Bool) → Option (Fin n × ℝ)`, read on the history oldest offer first. Prices are arbitrary reals (a non-positive offer is simply rejected by every seller with positive cost). `run m c` performs at most `n` steps, which is never binding because the sellers of a history are distinct; proposing an already-approached seller stops the run, which is the only consistent reading of "a single price" for a deterministic rule (asking again would return the same proposal). Acceptance is `decide (c i ≤ p)`.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 5, §2 Preliminaries; p. 24, Appendix B (definition of posted-price mechanisms and their budget feasibility); p. 25, §B.1 (additive valuations)

import Mathlib

namespace BudgetClock.PostedLB

/-- §B.1, p. 25: a valuation `v : 2^N → ℝ≥0` on the sellers `N = Fin n` is *additive* if there are
per-seller values `vᵢ ≥ 0` with `v(S) = ∑_{i ∈ S} vᵢ` for every `S ⊆ N`. The weights are
nonnegative because §2 (p. 5) takes valuations with values in `ℝ≥0`. -/
def IsAdditive {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∃ w : Fin n → ℝ, (∀ i, 0 ≤ w i) ∧ ∀ S : Finset (Fin n), v S = ∑ i ∈ S, w i

/-- One entry of the history of a posted-price mechanism: the seller approached, the price
offered to it, and whether it accepted (`true`) or rejected (`false`). -/
abbrev Offer (n : ℕ) := Fin n × ℝ × Bool

/-- Appendix B, p. 24: a *deterministic posted-price mechanism* on the sellers `Fin n`. It
approaches sellers one at a time and makes each a take-it-or-leave-it offer. The order is
adaptive: `next h` is the seller to approach next and the price to offer it, as a function of the
history `h` of earlier offers and answers (oldest first), or `none` to stop. Being a function of
the history is what makes it deterministic; it never sees the sellers' private costs. -/
structure PostedPrice (n : ℕ) where
  next : List (Offer n) → Option (Fin n × ℝ)

/-- At most `k` further steps of the mechanism `m` against the private costs `c`, from the
history `h`. A step asks `m.next h`; it stops on `none`, and also when the proposed seller has
already been approached (a posted-price mechanism offers each seller a single price). Otherwise
the seller `i` offered price `p` accepts iff `c i ≤ p` (p. 24: "which i accepts if `p_i ≥ c_i`
and rejects otherwise"), and the offer is appended to the history. -/
noncomputable def runAux {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) :
    ℕ → List (Offer n) → List (Offer n)
  | 0, h => h
  | k + 1, h =>
    match m.next h with
    | none => h
    | some (i, p) =>
      if i ∈ h.map Prod.fst then h
      else runAux m c k (h ++ [(i, p, decide (c i ≤ p))])

/-- The complete history of the mechanism `m` on the cost profile `c`, oldest offer first, from
the empty history with `n` steps of fuel. The fuel is never binding: sellers in a history are
distinct, so after `n` offers every seller has been approached and any further proposal would be
a repeat, which stops the run anyway. -/
noncomputable def run {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) : List (Offer n) :=
  runAux m c n []

/-- The sellers who accepted their offer in the history `h`: the mechanism's output set `M(I)`. -/
def accepted {n : ℕ} (h : List (Offer n)) : Finset (Fin n) :=
  ((h.filter fun e => e.2.2).map Prod.fst).toFinset

/-- The total payment in the history `h`: the sum of the prices of the accepted offers. -/
def payment {n : ℕ} (h : List (Offer n)) : ℝ :=
  ((h.filter fun e => e.2.2).map fun e => e.2.1).sum

/-- Appendix B, p. 24: a posted-price mechanism `M` for additive valuations is *budget feasible*
for the budget `B` if, on every instance of the class (every additive valuation `v` and every
profile of nonnegative private costs `c`), the sum of the prices of the accepted offers does not
exceed `B`. The mechanism knows the public valuation `v` (and `n`, `B`), but not `c`. -/
def BudgetFeasible {n : ℕ} (B : ℝ) (M : (Finset (Fin n) → ℝ) → PostedPrice n) : Prop :=
  ∀ v : Finset (Fin n) → ℝ, IsAdditive v →
    ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → payment (run (M v) c) ≤ B

end BudgetClock.PostedLB


