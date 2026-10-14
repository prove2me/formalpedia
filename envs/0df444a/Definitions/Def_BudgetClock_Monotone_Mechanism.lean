-- Prove2me | Definitions.Def_BudgetClock_Monotone_Mechanism
-- name    : BudgetClock_Monotone_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:44.79188+00:00
-- url     : https://prove2.me/theorems/63ed5b33-7e07-4601-b744-198f3f602c6e
-- title:
--   Mechanism 1 (Iterative-Pruning, p. 6) and Algorithm 2 (Maximize-Value, p. 7), with the phases, targets and sets of the run
-- statement:
--   The deterministic clock auction **Iterative-Pruning** (Mechanism 1) followed by **Maximize-Value** (Algorithm 2). A bidder offered a price $x$ accepts iff $c_i \le x$; a bidder who rejects leaves for good.
--
--   *Phase 1 (line 1).* All bidders are active ($A = N$), $S_0 = \emptyset$, $S_1 = \{i_1\}$ for a bidder $i_1$ maximizing $v(\{i\})$, the target is $\widetilde{\mathrm{OPT}} = v(S_1)$, and every price is $p_i = B$. The bidder $i_1$ is not asked anything.
--
--   *Phases $t \ge 2$ (lines 2–10).* While $A \setminus (S_{t-1} \cup S_t) \ne \emptyset$, a new phase starts: $t \leftarrow t+1$, $\widetilde{\mathrm{OPT}} \leftarrow 2\widetilde{\mathrm{OPT}}$, $S_t \leftarrow \emptyset$. Within the phase, while $v(S_t) < \widetilde{\mathrm{OPT}}$ and $A \setminus (S_{t-1} \cup S_t) \ne \emptyset$, the bidder $i$ of $A \setminus (S_{t-1} \cup S_t)$ with the largest marginal contribution $v(\{i\} \mid S_t)$ is offered
--   $$p_i \leftarrow \min\Bigl\{p_i,\; v(\{i\} \mid S_t)\cdot \frac{B}{\widetilde{\mathrm{OPT}}}\Bigr\};$$
--   if $i$ accepts it is appended to $S_t$, otherwise it is removed from $A$. Write $\hat t$ for the last phase and $\widetilde{\mathrm{OPT}}_t$ for the target of phase $t$, so that $\widetilde{\mathrm{OPT}}_t = 2^{t-1} v(S_1)$.
--
--   *Pruning (lines 11–17).* $W_1 \leftarrow S_{\hat t-1}$ and $\overline W_2 \leftarrow S_{\hat t}$. If $\sum_{i \in W_1} p_i > B$, the last bidder $j^*$ added to $S_{\hat t-1}$ is offered $\min\{p_{j^*}, v(\{j^*\} \mid S_{\hat t}) \cdot B/\widetilde{\mathrm{OPT}}_{\hat t}\}$ and removed from $W_1$; if it accepts it is appended to $\overline W_2$.
--
--   *Maximize-Value.* At the final prices, $W_2$ is the longest budget-feasible prefix of $\overline W_2$, $T$ is the longest prefix of $W_1$ such that $W_2 \cup T$ is budget feasible, $W_3 = W_2 \cup T$, and the output $W$ is whichever of $W_1$, $W_3$ has the larger value, together with the final prices.
--
--   The definitions also expose the components of the run used in the analysis: the state at the end of each phase, $\hat t$, $\widetilde{\mathrm{OPT}}_t$, $S_t$, the prices at the end of phase $t$, $W_1$, $\overline W_2$, $W_2$, $T$, $W_3$ and the final prices.
--
--   **Formalization Note** (1) Every argmax is broken toward the least bidder index (the paper leaves ties open; its claims hold for every tie rule). With no bidders, $S_1 = \emptyset$. (2) The inner loop is run with fuel $n$, which is never exhausted because every iteration removes one bidder from $A \setminus (S_{t-1}\cup S_t)$. (3) The outer loop is run for at most $n+2$ phases after phase 1. If $m = \max_i v(\{i\}) > 0$ and $v$ is monotone, submodular and non-negative, a phase $t \ge 2$ that does not exhaust the bidders reaches its target, so $2^{t-1} m \le (n+1) m$ and the mechanism stops on its own well before the cut. If $m = 0$, $v$ is constant, every phase ends at once with $S_t = \emptyset$, the paper's loop never terminates, and the run is cut after phase $n+3$; then $\widetilde{\mathrm{OPT}} = 0$ and the junk value $x/0 = 0$ appears in the prices, which is harmless since every set has the same value. (4) Line 12 tests $\sum_{i\in W_1}p_i > B$ on the list $S_{\hat t-1}$, which has no repeated bidder. (5) Maximize-Value returns $W_1$ when $v(W_3) \le v(W_1)$. (6) The clock-auction property is visible in the definition: every price update is a minimum with the previous price.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 6, Mechanism 1; p. 7, Algorithm 2 and the definitions of t̂ and OP̃T_t

import Mathlib
import Definitions.Def_BudgetClock_Monotone_Setting

namespace BudgetClock.Monotone

/-! Mechanism 1 (Iterative-Pruning, p. 6) and Algorithm 2 (Maximize-Value, p. 7) of Balkanski et al.,
arXiv:2107.09239v2. A bidder offered price `x` accepts iff `c i ≤ x`. Ties in every argmax are broken
by the least index of `Fin n`. -/

/-- The state of Mechanism 1: active bidders `A`, the lists `prev = S_{t-1}` and `cur = S_t` in
insertion order, the target `tgt = OP̃T`, the phase counter `t`, and the current prices `p`. -/
structure State (n : ℕ) where
  A : Finset (Fin n)
  prev : List (Fin n)
  cur : List (Fin n)
  tgt : ℝ
  t : ℕ
  p : Fin n → ℝ

/-- The bidders still to be offered a price in the current phase: `A \ (S_{t-1} ∪ S_t)`. -/
def pool {n : ℕ} (s : State n) : Finset (Fin n) :=
  s.A \ (s.prev.toFinset ∪ s.cur.toFinset)

/-- Line 5: the bidder of the pool with maximum marginal contribution `v({i} | S_t)`, least index
among the maximizers; `none` iff the pool is empty. -/
noncomputable def pickBidder {n : ℕ} (v : Finset (Fin n) → ℝ) (s : State n) : Option (Fin n) :=
  let M := (pool s).filter
    (fun i => ∀ j ∈ pool s, marg v {j} s.cur.toFinset ≤ marg v {i} s.cur.toFinset)
  if h : M.Nonempty then some (M.min' h) else none

/-- Lines 6–10 for bidder `i`: the price becomes `p_i ← min {p_i, v({i} | S_t) · B / OP̃T}`; if
`c i ≤ p_i` the bidder accepts and is appended to `S_t`, otherwise it is removed from `A`. -/
noncomputable def innerStep {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (s : State n) (i : Fin n) : State n :=
  let x := min (s.p i) (marg v {i} s.cur.toFinset * B / s.tgt)
  let p' := Function.update s.p i x
  if c i ≤ x then { s with p := p', cur := s.cur ++ [i] }
  else { s with p := p', A := s.A.erase i }

/-- Lines 4–10: the inner while loop, run while `v(S_t) < OP̃T` and the pool is nonempty. Each
iteration removes one bidder from the pool, so fuel `n` is never exhausted. -/
noncomputable def innerLoop {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    ℕ → State n → State n
  | 0, s => s
  | k + 1, s =>
    if s.tgt ≤ v s.cur.toFinset then s
    else
      match pickBidder v s with
      | none => s
      | some i => innerLoop v c B k (innerStep v c B s i)

/-- Lines 3–10: one phase. `t ← t + 1`, `OP̃T ← 2 OP̃T`, `S_{t-1} ←` the old `S_t`, `S_t ← ∅`, then
the inner loop. -/
noncomputable def phase {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (s : State n) : State n :=
  innerLoop v c B n { s with t := s.t + 1, tgt := 2 * s.tgt, prev := s.cur, cur := [] }

/-- Line 1: `A ← N`, `S_0 ← ∅`, `S_1 ← {argmax_i v({i})}` (least index among the maximizers; empty
when `n = 0`), `OP̃T ← v(S_1)`, `t ← 1`, `p_i ← B` for all `i`. The bidder of `S_1` is not asked to
accept anything. -/
noncomputable def initState {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) : State n :=
  let M := (Finset.univ : Finset (Fin n)).filter (fun i => ∀ j, v {j} ≤ v {i})
  let S1 : List (Fin n) := if h : M.Nonempty then [M.min' h] else []
  { A := Finset.univ, prev := [], cur := S1, tgt := v S1.toFinset, t := 1, p := fun _ => B }

/-- One iteration of the outer while loop (line 2): run a phase if the pool is nonempty, otherwise
stay (the mechanism has stopped). -/
noncomputable def outerStep {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (s : State n) : State n :=
  if (pool s).Nonempty then phase v c B s else s

/-- The state at the end of phase `t` (for `1 ≤ t`; phase 1 is line 1). After the last phase the
state no longer changes. -/
noncomputable def phaseState {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (t : ℕ) :
    State n :=
  (outerStep v c B)^[t - 1] (initState v B)

/-- The state when the outer loop has ended, after at most `n + 2` phases beyond phase 1.

Why the fuel `n + 2` suffices: let `m = max_i v({i})`. If `m > 0`, a phase `t ≥ 2` that ends with a
nonempty pool has reached its target, so `2^{t-1} m ≤ v(S_t) ≤ v(∅) + |S_t| m ≤ (n + 1) m` (monotone,
submodular, `v ≥ 0`); hence the last phase is at most `2 + log₂ (n + 1) ≤ n + 3` and the run
stops on its own. If `m = 0`, then `v` is constant on `S ⊆ N`, every phase ends at once with
`S_t = ∅`, the paper's loop never ends, and the run is cut after `n + 3` phases. -/
noncomputable def finalState {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) : State n :=
  (outerStep v c B)^[n + 2] (initState v B)

/-- `t̂`, the last phase of the run. -/
noncomputable def lastPhase {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) : ℕ :=
  (finalState v c B).t

/-- `OP̃T_t`, the target of phase `t` (equal to `2^{t-1} v(S_1)` for `1 ≤ t ≤ t̂`). -/
noncomputable def target {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (t : ℕ) : ℝ :=
  (phaseState v c B t).tgt

/-- `S_t`, in insertion order, at the end of phase `t`. -/
noncomputable def phaseSet {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (t : ℕ) :
    List (Fin n) :=
  (phaseState v c B t).cur

/-- The prices at the end of phase `t`. -/
noncomputable def phasePrices {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (t : ℕ) :
    Fin n → ℝ :=
  (phaseState v c B t).p

/-- Lines 11–17 applied to the final state `s`: `W_1 ← S_{t-1}`, `W̄_2 ← S_t`; if
`∑_{i ∈ W_1} p_i > B`, the last bidder `j*` of `S_{t-1}` is offered
`min {p_{j*}, v({j*} | S_t) · B / OP̃T_t}`, removed from `W_1`, and appended to `W̄_2` if it accepts.
Returns `(W_1, W̄_2, p)`. -/
noncomputable def prune {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (s : State n) :
    List (Fin n) × List (Fin n) × (Fin n → ℝ) :=
  if B < listCost s.p s.prev then
    match s.prev.getLast? with
    | none => (s.prev, s.cur, s.p)
    | some j =>
      let x := min (s.p j) (marg v {j} s.cur.toFinset * B / s.tgt)
      let p' := Function.update s.p j x
      if c j ≤ x then (s.prev.dropLast, s.cur ++ [j], p') else (s.prev.dropLast, s.cur, p')
  else (s.prev, s.cur, s.p)

/-- Algorithm 2, line 1: `W_2`, the longest budget-feasible prefix of `W̄_2`. -/
noncomputable def mvW2 {n : ℕ} (p : Fin n → ℝ) (B : ℝ) (W2bar : List (Fin n)) : List (Fin n) :=
  longestFeasiblePrefix p B W2bar

/-- Algorithm 2, line 2: `T`, the longest prefix of `W_1` such that `W_2 ∪ T` is budget feasible. -/
noncomputable def mvT {n : ℕ} (p : Fin n → ℝ) (B : ℝ) (W1 W2 : List (Fin n)) : List (Fin n) :=
  W1.take (Nat.findGreatest (fun k => listCost p W2 + listCost p (W1.take k) ≤ B) W1.length)

/-- Algorithm 2: `W_3 = W_2 ∪ T`, and the output is whichever of `W_1`, `W_3` has the larger value
(`W_1` on a tie), with the prices `p`. -/
noncomputable def maximizeValue {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (W1 W2bar : List (Fin n))
    (p : Fin n → ℝ) : Finset (Fin n) × (Fin n → ℝ) :=
  let W2 := mvW2 p B W2bar
  let W3 := W2 ++ mvT p B W1 W2
  (if v W3.toFinset ≤ v W1.toFinset then W1.toFinset else W3.toFinset, p)

/-- Lines 11–17 of the run: `(W_1, W̄_2, p)` after pruning. -/
noncomputable def pruned {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    List (Fin n) × List (Fin n) × (Fin n → ℝ) :=
  prune v c B (finalState v c B)

/-- `W_1` after pruning (line 15). -/
noncomputable def W1 {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) : List (Fin n) :=
  (pruned v c B).1

/-- `W̄_2` after pruning (line 17). -/
noncomputable def W2bar {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) : List (Fin n) :=
  (pruned v c B).2.1

/-- The final prices. -/
noncomputable def finalPrices {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    Fin n → ℝ :=
  (pruned v c B).2.2

/-- `W_2` of Algorithm 2 on the run. -/
noncomputable def W2 {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) : List (Fin n) :=
  mvW2 (finalPrices v c B) B (W2bar v c B)

/-- `T` of Algorithm 2 on the run. -/
noncomputable def Tpre {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) : List (Fin n) :=
  mvT (finalPrices v c B) B (W1 v c B) (W2 v c B)

/-- `W_3 = W_2 ∪ T` of Algorithm 2 on the run. -/
noncomputable def W3 {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) : List (Fin n) :=
  W2 v c B ++ Tpre v c B

/-- Iterative-Pruning (Mechanism 1 followed by Algorithm 2): the winning set `W` and the final
prices. -/
noncomputable def iterativePruning {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) :
    Finset (Fin n) × (Fin n → ℝ) :=
  maximizeValue v B (W1 v c B) (W2bar v c B) (finalPrices v c B)

end BudgetClock.Monotone


