-- Prove2me | Definitions.Def_RGMISFast_run
-- name    : RGMISFast_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:03.226178+00:00
-- url     : https://prove2.me/theorems/92897d94-22a5-4b05-9743-5e87ff57fbf7
-- title:
--   Procedure 1.1: memoized, pruned $\mathrm{RGMIS}(v,G,r)$ and the fresh-call count $Q(u^*)$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, $r:V\to[0,\infty)$ a rank function and $u^*\in V$ the **root**. Procedure 1.1, $\mathrm{RGMIS}(v,G,r)$, decides whether $v$ belongs to the greedy maximal independent set:
--
--   1. **Memo step.** If $v$ is in the memo table, return the recorded answer.
--   2. For every neighbour $w\in N(v)$ with $r(w)<r(v)$, **in increasing order of rank**: invoke $\mathrm{RGMIS}(w,G,r)$ recursively; if it answers YES ($w\in\mathrm{MIS}$), exit the loop (**pruning step**).
--   3. $v\in\mathrm{MIS}$ if and only if no invocation of the loop returned YES.
--   4. Record the answer in the memo table and return it.
--
--   The memo table starts empty at the call on $u^*$ and is shared by all calls of the run. A call is **fresh** if its result is not yet recorded in the memo table, and
--   $$
--   Q(u^*)=\#\{\text{fresh calls made during }\mathrm{RGMIS}(G,r,u^*)\text{, including the initial call}\}.
--   $$
--   The module also records the execution's **call trace**: for each invocation, the vertex whose scan made it (none for the initial call), the vertex called, and whether the call was fresh.
--
--   $Q(u^*)$ is the quantity bounded by the mission's goal theorem.
--
--   **Formalization Note** The procedure is a recursion on the rank with an explicit state (memo table, fresh-call counter, trace); a bound on the number of vertices of smaller rank is threaded through the recursion so that it is total, and the case without remaining budget is impossible by typing, so no default value is ever returned. Ranks take values in any linearly ordered type. The scan list sorts the lower neighbours by rank and breaks rank ties (an event of probability zero for continuous i.i.d. ranks) by a fixed linear order on $V$. $Q$ is the counter of fresh calls, not the size of the memo table.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Procedure 1.1, p.2 (PDF p.4); memoization, fresh calls and Q(u∗), p.3 (PDF p.5)

import Mathlib

set_option autoImplicit false

namespace RGMISFast

/-- The scan order of a finite set of vertices `s` under the rank function `r`: the elements of
`s` listed in increasing order of rank, ties broken by the fixed linear order of the vertex type
(Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every
Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), Procedure 1.1, step 2, p.2: "in
increasing order of rank").

**Formalization Note** The list is obtained by insertion sort of the keys `(r w, w)` in
lexicographic order, which is independent of the internal order of the multiset `s.val`; for
injective ranks it is the order by rank, and ties (an event of probability zero under i.i.d.
continuous ranks) are broken by the order on `V`. -/
def scanOrder {V : Type*} [LinearOrder V] {α : Type*} [LinearOrder α] (r : V → α)
    (s : Finset V) : List V :=
  (Quot.liftOn (s.val.map (fun w => toLex (r w, w)))
    (fun l => l.insertionSort (· ≤ ·))
    (fun _ _ h => ((List.perm_insertionSort _ _).trans
      (h.trans (List.perm_insertionSort _ _).symm)).eq_of_pairwise'
        (List.pairwise_insertionSort _ _) (List.pairwise_insertionSort _ _))).map
    (fun p => (ofLex p).2)

theorem mem_scanOrder {V : Type*} [LinearOrder V] {α : Type*} [LinearOrder α] (r : V → α)
    (s : Finset V) (w : V) : w ∈ scanOrder r s ↔ w ∈ s := by
  rcases s with ⟨m, hm⟩
  induction m using Quot.ind with
  | mk l => simp [scanOrder, Finset.mem_mk]

/-- The number of vertices of rank strictly below `r v`; it decreases along every recursive call
of Procedure 1.1 and serves as the termination measure. -/
def rk {V : Type*} [Fintype V] {α : Type*} [LinearOrder α] (r : V → α) (v : V) : ℕ :=
  (Finset.univ.filter (fun x => r x < r v)).card

theorem rk_lt {V : Type*} [Fintype V] {α : Type*} [LinearOrder α] (r : V → α) {v w : V}
    (h : r w < r v) : rk r w < rk r v := by
  unfold rk
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact lt_trans hx h
  · have : w ∈ Finset.univ.filter (fun x => r x < r w) := hsub (by simp [h])
    simp at this

/-- The neighbours `w ∈ N(v)` with `r(w) < r(v)`, in the scan order of Procedure 1.1, step 2. -/
def lowerNbrs {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [LinearOrder α] (r : V → α) (v : V) : List V :=
  scanOrder r ((G.neighborFinset v).filter (fun w => r w < r v))

theorem mem_lowerNbrs {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {α : Type*} [LinearOrder α] (r : V → α) {v w : V} :
    w ∈ lowerNbrs G r v ↔ G.Adj v w ∧ r w < r v := by
  simp [lowerNbrs, mem_scanOrder]

/-- One invocation of `RGMIS` in an execution: the vertex whose scan made it (`none` for the
initial call at the root), the vertex called, and whether the call was fresh (its answer was not
yet in the memo table). -/
structure CallEvent (V : Type*) where
  caller : Option V
  callee : V
  fresh : Bool

/-- The state of an execution of Procedure 1.1: the memo table (`some b` records the answer
"whether v ∈ MIS?" as `b`), the number of fresh calls made so far, and the call trace. -/
structure RunState (V : Type*) where
  memo : V → Option Bool
  count : ℕ
  trace : List (CallEvent V)

/-- One invocation `RGMIS(v, G, r)` of Procedure 1.1 (Dalirrooyfard, Makarychev, Mitrović,
Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript
sha256 e93cdfec…), Procedure 1.1, p.2, with memoization as on p.3), run on the state `s`, made by
the scan of `caller`. Returns the answer (`true` = YES, `v ∈ MIS`) and the new state.

1. (Memo step) if `v` is in the memo table, return the recorded answer (a non-fresh call);
2. otherwise the call is fresh: increment the fresh-call counter, then for every neighbour `w` with
   `r w < r v` in increasing order of rank, invoke `RGMIS(w)` recursively, and exit the loop at
   the first `w` answering YES (pruning step);
3. `v ∈ MIS` iff no invocation of the loop returned YES;
4. record the answer in the memo table and return it.

**Formalization Note** The first argument `n` is a bound on the termination measure
`rk r v < n`; the case `n = 0` is impossible (it is eliminated by `absurd`), so no value is ever
produced without running the procedure. The loop is a left fold over the scan list in which, once
a YES has been seen, the remaining iterations leave the state unchanged: this is the exit of
step 2.ii. Every invocation (fresh or memoized) is appended to the trace. -/
def callF {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [LinearOrder α] (r : V → α) :
    (n : ℕ) → (caller : Option V) → (v : V) → rk r v < n → RunState V → Bool × RunState V
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, caller, v, h, s =>
    match s.memo v with
    | some b => (b, { s with trace := s.trace ++ [⟨caller, v, false⟩] })
    | none =>
      let s₁ : RunState V :=
        { s with count := s.count + 1, trace := s.trace ++ [⟨caller, v, true⟩] }
      let res := (lowerNbrs G r v).attach.foldl
        (fun (acc : Bool × RunState V) (w : {w // w ∈ lowerNbrs G r v}) =>
          if acc.1 then acc
          else callF G r n (some v) w.1
            (by have := rk_lt r ((mem_lowerNbrs G r).1 w.2).2; omega) acc.2)
        (false, s₁)
      (!res.1, { res.2 with memo := Function.update res.2.memo v (some (!res.1)) })

/-- The initial state: empty memo table, no fresh calls, empty trace. -/
def initState {V : Type*} : RunState V := ⟨fun _ => none, 0, []⟩

/-- The execution `RGMIS(G, r, u∗)` of Procedure 1.1 from the root `u`, started with an empty
memo table ("When v = u∗, the memo table is empty", Procedure 1.1, p.2; Dalirrooyfard,
Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*, STOC 2027
submission (manuscript sha256 e93cdfec…)). Returns the answer for `u` and the final state (memo
table, fresh-call counter, call trace).

**Formalization Note** The procedure is a recursion on the rank with an explicit state: the memo
table is shared by all calls of the run. Ranks take values in any linearly ordered type (ℝ in the
probabilistic statements), and the scan order breaks rank ties by the order on `V`. -/
def run {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [LinearOrder α] (r : V → α) (u : V) : Bool × RunState V :=
  callF G r (rk r u + 1) none u (Nat.lt_succ_self _) initState

/-- `Q(u∗)`, the number of fresh calls made during `RGMIS(G, r, u∗)`, including the initial call
(Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every
Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), p.3): "We say that a call of RGMIS is
fresh if its result is not already recorded in the memo table. We denote by Q(u∗), the number of
fresh calls made during RGMIS(G, r, u∗), including the initial call."

**Formalization Note** `Q` is the fresh-call counter of the final state of `run`, not the size of
the memo table (the two agree by Observation 2.2(b), a milestone). -/
def Q {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [LinearOrder α] (u : V) (r : V → α) : ℕ :=
  (run G r u).2.count

end RGMISFast


