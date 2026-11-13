-- Prove2me | Definitions.Def_GMRDiversity_LivePoolPolicy
-- name    : GMRDiversity_LivePoolPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:39:28.919791+00:00
-- url     : https://prove2.me/theorems/bd6300a7-a983-4e3f-81bf-46493c6a9874
-- title:
--   Policies with a live pool of at most $w$ candidates for parity learning
-- statement:
--   A **live-pool policy** with pool size at most $w$ for $\mathfrak G^{\mathrm{par}}_x$ acts in rounds $t=1,2,\dots$. Its entire persistent state after round $t$ is an ordered list $P_t$ of at most $w$ candidates, starting from the empty list $P_0$. Round $t$ proceeds as follows.
--
--   1. Given only $t$ and $P_{t-1}$, the policy draws an action: either a generation, or a recombination $\mathrm{XOR}(P_{t-1}[i],P_{t-1}[j])$ of two (not necessarily distinct) pool entries.
--   2. The candidate $z_t$ is produced: $z_t\sim\mathrm{Gen}_x$, or $z_t=P_{t-1}[i]\oplus P_{t-1}[j]$.
--   3. Given $t$, $P_{t-1}$, its action and the full feedback $(z_t,U_x(z_t))$, the policy draws the next pool $P_t$, a list of at most $w$ candidates, each of which lies in the $\mathbb F_2$-span of the entries of $P_{t-1}$ and $z_t$.
--
--   Both draws may use fresh randomness. The policy never sees $x$ except through the feedback, and it is fixed before $x$ is drawn. Such a policy **retains only queried candidates** if, moreover, every possible $P_t$ arises from $z_t$ and $P_{t-1}$ by deleting entries and reordering.
--
--   This is the paper's notion of a policy with live pool size $w$: after every round its persistent state is the ordered list $P_t$, conditional on $P_t$ and $t$ the future actions are independent of the earlier history, and every operator argument belongs to the current pool.
--
--   **Formalization Note** A policy is a pair of probability kernels `act`, `keep` with the field `keep_valid` (length at most $w$, entries in the span). The bound $w$ is enforced at every round, not only before a horizon $T$; the value at $T$ depends only on rounds up to $T$. The span condition is the broadest reading of "previously queried candidates" and is used for the lower bound; `RetainsQueried` (the next pool is a sub-permutation of $z_t$ followed by $P_{t-1}$) is the strictest one and is required of the policies the upper bound constructs.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), §2 'Policies', p.4; §6 'Diversity', p.8

import Mathlib
import Definitions.Def_GMRDiversity_Cand

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Policies whose persistent state is a live pool of at most `w` candidates**, for the parity
instance `𝔊^par_x` (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with Optimization Guided
Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, §2 "Policies", p.4, and §6
"Diversity", p.8): "after every round `t < T`, its entire persistent state is an ordered list `P_t` of
at most `w` previously queried candidates. Conditional on `P_t` and `t`, the distribution of all
future actions is independent of the earlier history. In particular, every candidate used as an
argument to a future operator must belong to the current live pool."

A policy is given by two probability kernels.
* `act t P` is the law of the action of round `t` given the pool `P = P_{t−1}`: `none` is a
  generation `Gen_x`, and `some (i, j)` is the recombination `XOR(P[i], P[j])` of the pool entries
  `i` and `j` (not necessarily distinct, p.4).
* `keep t P a z r` is the law of the next pool `P_t`, given the round `t`, the old pool `P`, the
  action `a`, the queried candidate `z` and the feedback bit `r = U_x(z)` (full feedback
  `(z, U_x(z))`, p.8).

`keep_valid`: every possible next pool has at most `w` entries, each of which lies in the
`𝔽₂`-span of the old pool and the new candidate (as elements of `𝔽₂ⁿ × 𝔽₂`).

**Formalization Note.** The pool starts empty, so at round 1 only generation is possible (the action
type `Option (Fin 0 × Fin 0)` has the single value `none`), as on p.4. Fresh randomness inside a
round is free (the kernels are arbitrary probability mass functions). The bound `≤ w` is imposed at
every round, not only before `T`; the value at time `T` depends only on rounds `≤ T`, so this changes
no instance. `keep_valid` only asks the new entries to lie in the span of `P_{t−1}` and `z_t`, which
contains every reading of "previously queried candidates" (the strict reading, where the new pool
arises from the old one by adding `z_t`, deleting and reordering, is the predicate
`LivePoolPolicy.RetainsQueried`). The policy never sees `x` and is fixed before `x` is drawn. -/
structure LivePoolPolicy (n w : ℕ) where
  /-- Law of the action of round `t` given the current pool. -/
  act : ℕ → (P : List (Cand n)) → PMF (Option (Fin P.length × Fin P.length))
  /-- Law of the next pool given the round, the old pool, the action, the new candidate and
  the feedback bit. -/
  keep : ℕ → (P : List (Cand n)) → Option (Fin P.length × Fin P.length) → Cand n → Bool →
    PMF (List (Cand n))
  /-- Every next pool has at most `w` entries, all in the span of the old pool and `z`. -/
  keep_valid : ∀ t P a z r, ∀ P' ∈ (keep t P a z r).support,
    P'.length ≤ w ∧ ∀ y ∈ P', y ∈ Submodule.span (ZMod 2) {u | u ∈ P ∨ u = z}

/-- **Pools made only of queried candidates** (§6 "Diversity", p.8, strict reading): every possible
next pool is obtained from the old pool and the newly queried candidate `z` by deleting entries and
reordering, i.e. it is a sub-permutation of `z :: P`. The paper's own policy in the proof of
Lemma 2 (p.11, "Live pool") has this property. -/
def LivePoolPolicy.RetainsQueried {n w : ℕ} (π : LivePoolPolicy n w) : Prop :=
  ∀ t P a z r, ∀ P' ∈ (π.keep t P a z r).support, P'.Subperm (z :: P)

end GMRDiversity


