-- Prove2me | Definitions.Def_BudgetClock_NonMonotone_Mechanism
-- name    : BudgetClock_NonMonotone_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:11:35.00198+00:00
-- url     : https://prove2.me/theorems/71bea914-10f3-48b8-ab66-4c1ecbf2770e
-- title:
--   Mechanism 3, p. 11 — Simultaneous-Iterative-Pruning, its phases, and the six candidate solutions
-- statement:
--   This file defines Mechanism 3 of the paper, **Simultaneous-Iterative-Pruning**, a descending clock auction for a budget $B$, a valuation $v$ on the bidders $N$, and true costs $c_i$. A bidder offered a price $x$ accepts if and only if $c_i \le x$; a bidder who rejects leaves the auction for good. The mechanism also takes a subroutine $\mathrm{USM}$ that maps a set $X$ to a subset of $X$ (an unconstrained submodular maximizer).
--
--   **Initialization (line 1).** All bidders are active ($A = N$), $S^1_0 = S^2_0 = S^1_1 = \emptyset$, $S^2_1 = \{i^\star\}$ where $i^\star$ maximizes $v(\{i\})$, the target is $\widetilde{OPT} = v(S^2_1)$, the phase is $t = 1$, and every price is $p_i = B$.
--
--   **Phases (lines 2–10).** While some active bidder lies outside $S^1_{t-1} \cup S^2_{t-1} \cup S^1_t \cup S^2_t$, a new phase starts: $t \leftarrow t+1$, $\widetilde{OPT} \leftarrow 2\widetilde{OPT}$, the two sets of the previous phase are set aside as $S^1_{t-1}, S^2_{t-1}$, and $S^1_t = S^2_t = \emptyset$. While $\max\{v(S^1_t), v(S^2_t)\} < \widetilde{OPT}$ and some active bidder $i$ lies outside the four sets, the mechanism picks the pair $(i, k)$, $k \in \{1, 2\}$, maximizing $v(\{i\} \mid S^k_t)$, lowers the price to
--
--   $$p_i \leftarrow \min\Big\{p_i,\ v(\{i\} \mid S^k_t) \cdot \frac{B}{\widetilde{OPT}}\Big\},$$
--
--   and appends $i$ to $S^k_t$ if it accepts, or removes it from $A$ otherwise. The target of phase $t$ is $\widetilde{OPT}_t = 2^{t-1} v(S^2_1)$; $\hat t$ denotes the last phase.
--
--   **Output (lines 11–15).** With $T^k_j = \mathrm{USM}(S^k_j)$ for $j \in \{\hat t - 1, \hat t\}$ and $k \in \{1, 2\}$, the mechanism picks the set $S$ of maximum value among the six candidates $S^1_{\hat t-1}, S^2_{\hat t-1}, T^1_{\hat t}, T^2_{\hat t}, T^1_{\hat t-1}, T^2_{\hat t-1}$. If $\sum_{i \in S} p_i > B$, it removes the last bidder added to $S$. It returns $S$ and the prices.
--
--   The file also names the objects that the lemmas of §4 talk about: the last phase $\hat t$, the targets $\widetilde{OPT}_t$, the sets $(S^1_t, S^2_t)$ at the end of phase $t$, the active bidders $A_t$ at the end of phase $t$ ($A_0 = N$), the bidders rejected in phase $t$ ($A_{t-1} \setminus A_t$), and the list of six candidates.
--
--   **Formalization Note**
--   1. Ties are broken by the least bidder index: in line 5 the least bidder $i$ of a maximizing pair, with $k = 1$ before $k = 2$; for $i^\star$ the least maximizer; in line 12 the first maximizer in the printed order of the six candidates. The paper fixes no tie rule.
--   2. The tentative sets are lists in insertion order. $T^k_j$ is the sublist of $S^k_j$ formed by the bidders in $\mathrm{USM}(S^k_j)$, so that "the last bidder added to $S$" is defined for every candidate. For $\hat t = 1$, $S^1_0 = S^2_0 = \emptyset$.
--   3. The inner loop has fuel $n$ (each iteration removes one bidder from the pool). The outer loop is run for at most $n+2$ phases after phase 1. For non-negative submodular $v$ this is never cut short unless $\max_i v(\{i\}) = 0$, in which case $v \equiv 0$ and the paper's loop never terminates; the docstring of `finalState` gives the argument.
--   4. `USM` is an argument of the mechanism. The theorems quantify over every subroutine with the paper's guarantee.
--   5. The clock-auction property is built in: every price update is the minimum of the old price and a new one.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 11, Mechanism 3 (with the description on pp. 11–12)

import Mathlib
import Definitions.Def_BudgetClock_Monotone_Setting

namespace BudgetClock.NonMonotone

/-! Mechanism 3 (Simultaneous-Iterative-Pruning, p. 11) of Balkanski et al., arXiv:2107.09239v2.
A bidder offered price `x` accepts iff `c i ≤ x`; a bidder who rejects leaves `A` for good. Ties in
every argmax are broken by the least index of `Fin n` (in line 5, least bidder `i` first, then
`k = 1` before `k = 2`; in line 12, the first maximizer in the printed order). -/

/-- The state of Mechanism 3: active bidders `A`; the lists `prev1 = S¹_{t-1}`, `prev2 = S²_{t-1}`,
`cur1 = S¹_t`, `cur2 = S²_t` in insertion order; the target `tgt = OP̃T`; the phase counter `t`;
the current prices `p`. -/
structure State (n : ℕ) where
  A : Finset (Fin n)
  prev1 : List (Fin n)
  prev2 : List (Fin n)
  cur1 : List (Fin n)
  cur2 : List (Fin n)
  tgt : ℝ
  t : ℕ
  p : Fin n → ℝ

/-- The bidders still to be offered a price in the current phase:
`A \ (S¹_{t-1} ∪ S²_{t-1} ∪ S¹_t ∪ S²_t)`. -/
def pool {n : ℕ} (s : State n) : Finset (Fin n) :=
  s.A \ (s.prev1.toFinset ∪ s.prev2.toFinset ∪ s.cur1.toFinset ∪ s.cur2.toFinset)

/-- The larger of the two marginal contributions `v({i} | S¹_t)` and `v({i} | S²_t)`. -/
def bestMarg {n : ℕ} (v : Finset (Fin n) → ℝ) (s : State n) (i : Fin n) : ℝ :=
  max (BudgetClock.Monotone.marg v {i} s.cur1.toFinset) (BudgetClock.Monotone.marg v {i} s.cur2.toFinset)

/-- Line 5, the bidder: the least bidder `i` of the pool for which some pair `(i, k)` maximizes
`v({i} | S^k_t)` over the pool and `k ∈ {1, 2}`; `none` iff the pool is empty. -/
noncomputable def pickBidder {n : ℕ} (v : Finset (Fin n) → ℝ) (s : State n) : Option (Fin n) :=
  let M := (pool s).filter (fun i => ∀ j ∈ pool s, bestMarg v s j ≤ bestMarg v s i)
  if h : M.Nonempty then some (M.min' h) else none

/-- Lines 6–10 for bidder `i`, with `k = 1` if `v({i} | S¹_t) ≥ v({i} | S²_t)` and `k = 2`
otherwise: the price becomes `p_i ← min {p_i, v({i} | S^k_t) · B / OP̃T}`; if `c i ≤ p_i` the
bidder accepts and is appended to `S^k_t`, otherwise it is removed from `A`. -/
noncomputable def innerStep {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (s : State n) (i : Fin n) : State n :=
  let m1 := BudgetClock.Monotone.marg v {i} s.cur1.toFinset
  let m2 := BudgetClock.Monotone.marg v {i} s.cur2.toFinset
  let x := min (s.p i) ((if m2 ≤ m1 then m1 else m2) * B / s.tgt)
  let p' := Function.update s.p i x
  if c i ≤ x then
    if m2 ≤ m1 then { s with p := p', cur1 := s.cur1 ++ [i] }
    else { s with p := p', cur2 := s.cur2 ++ [i] }
  else { s with p := p', A := s.A.erase i }

/-- Lines 4–10: the inner while loop, run while `max {v(S¹_t), v(S²_t)} < OP̃T` and the pool is
nonempty. Each iteration removes one bidder from the pool, so fuel `n` is never exhausted. -/
noncomputable def innerLoop {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ℕ → State n → State n
  | 0, s => s
  | k + 1, s =>
    if s.tgt ≤ max (v s.cur1.toFinset) (v s.cur2.toFinset) then s
    else
      match pickBidder v s with
      | none => s
      | some i => innerLoop v c B k (innerStep v c B s i)

/-- Lines 3–10: one phase. `t ← t + 1`, `OP̃T ← 2 OP̃T`, `(S¹_{t-1}, S²_{t-1}) ←` the old
`(S¹_t, S²_t)`, `S¹_t, S²_t ← ∅`, then the inner loop. -/
noncomputable def phase {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (s : State n) : State n :=
  innerLoop v c B n
    { s with t := s.t + 1, tgt := 2 * s.tgt, prev1 := s.cur1, prev2 := s.cur2,
             cur1 := [], cur2 := [] }

/-- Line 1, `S²_1 = {argmax_{i ∈ N} v({i})}`: the least bidder maximizing `v({i})`, as a list;
empty when `n = 0`. -/
noncomputable def bestSingleton {n : ℕ} (v : Finset (Fin n) → ℝ) : List (Fin n) :=
  let M := (Finset.univ : Finset (Fin n)).filter (fun i => ∀ j, v {j} ≤ v {i})
  if h : M.Nonempty then [M.min' h] else []

/-- Line 1: `A ← N`, `S¹_0, S²_0, S¹_1 ← ∅`, `S²_1 ← {argmax_i v({i})}`, `OP̃T ← v(S²_1)`,
`t ← 1`, `p_i ← B` for all `i`. The bidder of `S²_1` is not asked to accept anything. -/
noncomputable def initState {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) : State n :=
  { A := Finset.univ, prev1 := [], prev2 := [], cur1 := [], cur2 := bestSingleton v,
    tgt := v (bestSingleton v).toFinset, t := 1, p := fun _ => B }

/-- One iteration of the outer while loop (line 2): run a phase if the pool is nonempty,
otherwise stay (the mechanism has stopped). -/
noncomputable def outerStep {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (s : State n) : State n :=
  if (pool s).Nonempty then phase v c B s else s

/-- The state at the end of phase `k + 1` (`k = 0` is the state after line 1). After the last
phase the state no longer changes. -/
noncomputable def phaseEnd {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (k : ℕ) :
    State n :=
  (outerStep v c B)^[k] (initState v B)

/-- The state when the outer loop has ended: `n + 2` iterations of the outer loop.

Why this fuel suffices for non-negative submodular `v`. Let `m = v(S²_1) = max_i v({i})`. For
`n ≤ 1` the pool is empty after line 1 and no phase is run. For `n ≥ 2`, submodularity on two
disjoint singletons gives `v(∅) ≤ 2m`, and every marginal satisfies `v({i} | S) ≤ v({i}) - v(∅) ≤ m`,
so every `S` has `v(S) ≤ max {v(∅), |S| m} ≤ n m`. If `m > 0`, a phase `t ≥ 2` that ends with a
nonempty pool has reached its target, so `2^{t-1} m ≤ n m`; hence phase `n + 1` at the latest
ends with an empty pool and the run stops on its own. If `m = 0`, then `v ≡ 0`, every phase ends
at once, the paper's loop never ends, and the run is cut after `n + 2` iterations (every
statement about the output is then trivial, as `v ≡ 0`). -/
noncomputable def finalState {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    State n :=
  phaseEnd v c B (n + 2)

/-- `t̂`, the last phase of the run. -/
noncomputable def lastPhase {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) : ℕ :=
  (finalState v c B).t

/-- `OP̃T_t = 2^{t-1} v(S²_1)`, the target of phase `t ≥ 1` (it starts at `v(S²_1)` and doubles in
every phase). The value at `t = 0` (`0`) is never used. -/
noncomputable def target {n : ℕ} (v : Finset (Fin n) → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (2 : ℝ) ^ t * v (bestSingleton v).toFinset

/-- `(S¹_t, S²_t)`, in insertion order, at the end of phase `t`; `(∅, ∅)` for `t = 0`. -/
noncomputable def phaseSets {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ℕ → List (Fin n) × List (Fin n)
  | 0 => ([], [])
  | t + 1 => ((phaseEnd v c B t).cur1, (phaseEnd v c B t).cur2)

/-- `A_t`, the active bidders (not yet rejected) at the end of phase `t`; `A_0 = N`. -/
noncomputable def survivors {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ℕ → Finset (Fin n)
  | 0 => Finset.univ
  | t + 1 => (phaseEnd v c B t).A

/-- The bidders rejected (removed from `A`) during phase `t`: `A_{t-1} \ A_t` for `t ≥ 1`; empty
for `t = 0`. Phase 1 (line 1) rejects nobody. -/
noncomputable def rejectedIn {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ℕ → Finset (Fin n)
  | 0 => ∅
  | t + 1 => survivors v c B t \ survivors v c B (t + 1)

/-- Line 11 on one list: `T = UnconstrainedSubMax(v, S)` is `usm S`, kept as the sublist of `S`
(in the insertion order of `S`) of the bidders that lie in `usm S`, so that "the last bidder
added" (line 14) is defined. -/
def usmList {n : ℕ} (usm : Finset (Fin n) → Finset (Fin n)) (S : List (Fin n)) :
    List (Fin n) :=
  S.filter (fun i => decide (i ∈ usm S.toFinset))

/-- Lines 11–12: the six candidate solutions built from the state `s` after the last phase `t̂`,
in the printed order `S¹_{t̂-1}, S²_{t̂-1}, T¹_{t̂}, T²_{t̂}, T¹_{t̂-1}, T²_{t̂-1}` (for `t̂ = 1`,
`S¹_0 = S²_0 = ∅`). -/
def candidates {n : ℕ} (usm : Finset (Fin n) → Finset (Fin n)) (s : State n) :
    List (List (Fin n)) :=
  [s.prev1, s.prev2, usmList usm s.cur1, usmList usm s.cur2, usmList usm s.prev1,
    usmList usm s.prev2]

/-- The first list of `Ls` of maximum value `v(·)` (the empty list if `Ls` is empty). -/
noncomputable def firstArgmax {n : ℕ} (v : Finset (Fin n) → ℝ) :
    List (List (Fin n)) → List (Fin n)
  | [] => []
  | [L] => L
  | L :: L' :: Ls =>
    let R := firstArgmax v (L' :: Ls)
    if v R.toFinset ≤ v L.toFinset then L else R

/-- Lines 12–14 on the state `s` after the last phase: `S ←` the first maximizer of `v` among the
six candidates; if `∑_{i ∈ S} p_i > B`, the last bidder of `S` is removed. -/
noncomputable def chosenSet {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ)
    (usm : Finset (Fin n) → Finset (Fin n)) (s : State n) : List (Fin n) :=
  let S := firstArgmax v (candidates usm s)
  if B < BudgetClock.Monotone.listCost s.p S then S.dropLast else S

/-- Mechanism 3, Simultaneous-Iterative-Pruning, run on valuation `v`, true costs `c`, budget `B`
and an unconstrained submodular maximization subroutine `usm`. Returns the winning set `S` (line
15) and the final price vector `p` (each winner is paid `p i`). -/
noncomputable def simultaneousIterativePruning {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (B : ℝ) (usm : Finset (Fin n) → Finset (Fin n)) : Finset (Fin n) × (Fin n → ℝ) :=
  ((chosenSet v B usm (finalState v c B)).toFinset, (finalState v c B).p)

end BudgetClock.NonMonotone


