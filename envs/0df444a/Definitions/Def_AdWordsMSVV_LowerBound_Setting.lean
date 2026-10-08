-- Prove2me | Definitions.Def_AdWordsMSVV_LowerBound_Setting
-- name    : AdWordsMSVV_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:55.646417+00:00
-- url     : https://prove2.me/theorems/ef061bd4-de57-47be-a830-3ab7243addf2
-- title:
--   §1.1, p. 2 and §7, p. 15 — online b-matching, deterministic and randomized online algorithms, revenue, offline revenue, and the permuted round instances
-- statement:
--   This file fixes the **online b-matching problem** of Kalyanasundaram and Pruhs as Mehta, Saberi, Vazirani and Vazirani describe it (§1.1, p. 2): a special case of the adwords problem in which every advertiser (bidder) has a daily budget of $b$ dollars and bids only $0$ or $1$ dollar on each query. It also fixes the hard input family of the proof of Theorem 9 (p. 15).
--
--   1. **Instances.** There are $N$ bidders and $M$ queries, arriving in a fixed order $t = 0, 1, \dots, M-1$. An instance is a map $I$ sending each query $t$ to the set $I(t)$ of bidders that bid $1$ on it; every other bidder bids $0$. Every bidder has the same integer budget $B$.
--
--   2. **Online algorithms.** At arrival $t$ an algorithm sees the *history* $h_t(I)$, which reveals the bid sets $I(0), \dots, I(t)$ and nothing about later queries. A **deterministic online algorithm** $a$ is a rule that, given $t$ and $h_t(I)$, either proposes a bidder for query $t$ or leaves the query unallocated. A proposal *succeeds* when the proposed bidder bids $1$ on query $t$ and has so far won fewer than $B$ queries; the query then goes to that bidder, who pays $1$. Otherwise the query is lost. No rule is required to be greedy.
--
--   3. **Loads, winners and revenue.** $L^a_t(r)$ is the number of queries bidder $r$ has won after the first $t$ arrivals, $w^a(t)$ is the bidder that wins query $t$ (if any), and the **revenue** of $a$ on $I$ is
--   $$\mathrm{ALG}_a(I) = \sum_{r} L^a_M(r).$$
--   The number of queries of round $i$ (1-based, see 6) won by bidder $r$ is written $W^a_i(r)$.
--
--   4. **Randomized online algorithms.** A randomized online algorithm $A$ is a probability distribution over deterministic online algorithms, fixed before the instance. Its expected revenue on $I$ is
--   $$\mathbb E_A[\mathrm{ALG}(I)] = \sum_{a} A(a)\,\mathrm{ALG}_a(I).$$
--
--   5. **Offline revenue.** For an arbitrary allocation $\tau$ assigning each query to a bidder or to nobody, each bidder pays $1$ for every assigned query it bids on, up to its budget:
--   $$\mathrm{rev}_B(I,\tau) = \sum_{r} \min\{B,\ |\{t : \tau(t) = r,\ r \in I(t)\}|\}.$$
--
--   6. **The permuted round instances (p. 15).** For a permutation $\pi$ of the bidders, the instance $I_\pi$ has $N$ rounds $Q_1, \dots, Q_N$ of $B$ queries each; bidders $\pi(i), \pi(i+1), \dots, \pi(N)$ bid $1$ on the queries of round $Q_i$ and the others bid $0$. The allocation $\tau_\pi$ gives every query of $Q_i$ to $\pi(i)$. The uniform average over all $N!$ permutations is written $\mathbb E_\pi[f(\pi)] = \frac{1}{N!}\sum_\pi f(\pi)$.
--
--   These objects carry the whole of §7: Theorem 9 and every milestone of its proof are statements about them.
--
--   **Formalization Note** The paper states the hard instance with budget $1$, bids $\epsilon$ and $1/\epsilon$ queries per round; here it is scaled by $B = 1/\epsilon$ to integer budgets $B$ and $0/1$ bids, which is the b-matching problem of p. 2 and the same instance. Bidders and query positions are zero-based (`Fin N`, `Fin M`); in Lean a query at position $t$ lies in round $\lfloor t/B\rfloor$ (zero-based), and bidder $r$ bids on that round iff its position $\pi^{-1}(r)$ (zero-based) is at least the round index, which is the paper's "bidders $\pi(i),\dots,\pi(N)$". `wonInRound` takes the paper's 1-based round index $i$. The distribution over deterministic rules represents all internal coin flips; since a deterministic rule can recompute its own earlier choices from the history, nothing is lost by not passing them explicitly.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 2, §1.1 (online b-matching); p. 15, proof of Theorem 9 (the distribution D)

import Mathlib

namespace AdWordsMSVV.LowerBound

open Finset

/-- A b-matching instance with `N` bidders and `M` queries: `I t` is the set of bidders bidding 1 on
the query at position `t` (zero-based); every other bidder bids 0 on it. -/
abbrev Instance (N M : ℕ) := Fin M → Finset (Fin N)

/-- What an online algorithm has seen at arrival `t`: the bid sets of the queries at positions `≤ t`
are revealed, later entries are `none`. -/
abbrev History (N M : ℕ) := Fin M → Option (Finset (Fin N))

/-- The history of instance `I` at arrival `t`: entries up to and including `t`, nothing later. -/
def reveal {N M : ℕ} (I : Instance N M) (t : Fin M) : History N M :=
  fun j => if j ≤ t then some (I j) else none

/-- A deterministic online algorithm: at arrival `t`, from the history alone, it proposes a bidder
for the current query or leaves the query unallocated (`none`). -/
abbrev DetAlg (N M : ℕ) := Fin M → History N M → Option (Fin N)

/-- Number of queries won by each bidder after the first `t` arrivals, when every bidder has budget
`B` and bids are 0/1. A proposal succeeds iff the proposed bidder bids 1 on the query and has won
fewer than `B` queries so far; otherwise the query is lost. -/
noncomputable def load {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) :
    ℕ → Fin N → ℕ
  | 0 => fun _ => 0
  | t + 1 =>
      let L := load B I a t
      if h : t < M then
        match a ⟨t, h⟩ (reveal I ⟨t, h⟩) with
        | none => L
        | some r => if r ∈ I ⟨t, h⟩ ∧ L r < B then Function.update L r (L r + 1) else L
      else L

/-- The bidder that wins the query at position `t` in the run of `a` on `I` (`none` if the query
is left unallocated or the proposal fails). -/
noncomputable def winner {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) (t : Fin M) :
    Option (Fin N) :=
  match a t (reveal I t) with
  | none => none
  | some r => if r ∈ I t ∧ load B I a t.val r < B then some r else none

/-- Revenue of the deterministic algorithm: the number of queries won (each pays 1). -/
noncomputable def revenue {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) : ℕ :=
  ∑ r, load B I a M r

/-- A randomized online algorithm: a probability distribution over deterministic online algorithms,
fixed before the instance. -/
abbrev RandAlg (N M : ℕ) := PMF (DetAlg N M)

/-- Expected revenue of a randomized online algorithm on a fixed instance. -/
noncomputable def expectedRevenue {N M : ℕ} (B : ℕ) (I : Instance N M) (A : RandAlg N M) : ℝ := by
  classical
  exact ∑ a : DetAlg N M, (A a).toReal * (revenue B I a : ℝ)

/-- Offline revenue of an arbitrary allocation `τ` (`τ t = none`: query `t` unassigned): each bidder
pays 1 for every assigned query it bids on, up to its budget `B`. -/
noncomputable def offlineRevenue {N M : ℕ} (B : ℕ) (I : Instance N M)
    (τ : Fin M → Option (Fin N)) : ℕ :=
  ∑ r, min B ((univ.filter (fun t => τ t = some r ∧ r ∈ I t)).card)

/-- The permuted round instance of p. 15, scaled to budget `B` and 0/1 bids: `N` rounds of `B`
queries; the query at position `t` belongs to round `t / B` (zero-based), and bidder `r` bids on
round `i` iff its position `π⁻¹ r` in the permutation is `≥ i`, i.e. bidders `π i, …, π (N-1)`. -/
def roundInstance (N B : ℕ) (π : Equiv.Perm (Fin N)) : Instance N (N * B) :=
  fun t => univ.filter (fun r => t.val / B ≤ (π.symm r).val)

/-- The allocation of p. 15 that gives every query of round `i` (zero-based) to bidder `π i`. -/
def roundAllocation (N B : ℕ) (π : Equiv.Perm (Fin N)) : Fin (N * B) → Option (Fin N) :=
  fun t => if h : t.val / B < N then some (π ⟨t.val / B, h⟩) else none

/-- Number of queries of round `i` won by bidder `r`, with the paper's **1-based** round index `i`:
the queries at positions `t` with `t / B + 1 = i`. -/
noncomputable def wonInRound {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) (i : ℕ)
    (r : Fin N) : ℕ :=
  (univ.filter (fun t : Fin M => t.val / B + 1 = i ∧ winner B I a t = some r)).card

/-- Average of `f` over the uniform distribution on the `N!` permutations of the bidders. -/
noncomputable def permAvg (N : ℕ) (f : Equiv.Perm (Fin N) → ℝ) : ℝ :=
  (∑ π, f π) / (Nat.factorial N : ℝ)

end AdWordsMSVV.LowerBound


