-- Prove2me | Definitions.Def_Timetabling85_TwoPeriod_Backtracking
-- name    : Timetabling85_TwoPeriod_Backtracking
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:47.48596+00:00
-- url     : https://prove2.me/theorems/9528b46d-9cad-400a-ac87-f1667f104c25
-- title:
--   Proof of Proposition 2.4, pp. 154–155 — implications of a decision and the limited backtracking procedure
-- statement:
--   This file fixes the limited backtracking method of the proof of de Werra's Proposition 2.4, on an abstract conflict graph.
--
--   **Conflict graph.** There are $n$ teachers, and each teacher $t_j$ has two nodes, $x_j$ (written $(j,\mathrm{true})$) and $\bar x_j$ (written $(j,\mathrm{false})$), one for each of its possible schedules. $G$ is any simple graph on these $2n$ nodes.
--
--   **Implications.** For a set $S$ of chosen nodes, its set of implications $\mathrm{cl}(S)$ is the least set of nodes that contains $S$ and is closed under the rule: if $u\in\mathrm{cl}(S)$ and $u$ is linked in $G$ to a node $w$ of another teacher, then the other node of $w$'s teacher is in $\mathrm{cl}(S)$ (choosing $u$ forbids $w$, which fixes that teacher's schedule). A teacher $t_j$ is *fixed* in $A$ if $x_j\in A$ or $\bar x_j\in A$.
--
--   **The procedure.** Its states are $\mathrm{run}(A)$, with $A$ the set of nodes fixed so far, and $\mathrm{fail}$. It starts at $\mathrm{run}(\emptyset)$. From $\mathrm{run}(A)$, for any teacher $t_j$ not fixed in $A$ and any first choice $b$ of one of its two nodes (the arbitrary decision):
--   1. if $\mathrm{cl}(A\cup\{(j,b)\})$ is a set of pairwise non-adjacent nodes, the procedure moves to $\mathrm{run}(\mathrm{cl}(A\cup\{(j,b)\}))$ — the decision becomes permanent;
--   2. otherwise, if $\mathrm{cl}(A\cup\{(j,\lnot b)\})$ is pairwise non-adjacent, it moves to $\mathrm{run}(\mathrm{cl}(A\cup\{(j,\lnot b)\}))$ — the decision is reversed;
--   3. otherwise it moves to $\mathrm{fail}$.
--
--   A state $\mathrm{run}(A)$ with every teacher fixed, and $\mathrm{fail}$, have no moves. The reachable states are those reached from $\mathrm{run}(\emptyset)$ by finitely many moves.
--
--   Because both the teacher and the first choice are arbitrary, the moves form a relation rather than a function; every run of the procedure is a path in it.
--
--   **Formalization Note** The implications are an inductive predicate (no iteration bound), collected into a `Finset` with classical decidability. A contradiction ("for some teacher no schedule can be found") is a set of implications that is not independent in $G$. The decision $(j,b)$ is examined against all previously fixed nodes as well, so a forced node adjacent to an earlier choice is a contradiction.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), pp. 154–155, Proof of Proposition 2.4 (the limited backtracking method)

import Mathlib

namespace Timetabling85.TwoPeriod

/-- Implications of a set `S` of chosen schedules in a conflict graph on `Fin n × Bool`
(node `(j, true)` is x_j, node `(j, false)` is x̄_j): the least set containing `S` and such
that whenever `u` is in it and `u` is linked to a node `w` of another teacher, the other
schedule `(w.1, !w.2)` of that teacher is in it. -/
inductive InClosure {n : ℕ} (G : SimpleGraph (Fin n × Bool)) (S : Set (Fin n × Bool)) :
    Fin n × Bool → Prop
  | base {u : Fin n × Bool} : u ∈ S → InClosure G S u
  | force {u w : Fin n × Bool} : InClosure G S u → G.Adj u w → w.1 ≠ u.1 →
      InClosure G S (w.1, !w.2)

/-- All the implications of the chosen schedules `S`, as a finite set. -/
noncomputable def closure {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (S : Finset (Fin n × Bool)) : Finset (Fin n × Bool) := by
  classical
  exact Finset.univ.filter (InClosure G (S : Set (Fin n × Bool)))

/-- Teacher `j` has a fixed schedule in `A`. -/
def Fixed {n : ℕ} (A : Finset (Fin n × Bool)) (j : Fin n) : Prop :=
  (j, true) ∈ A ∨ (j, false) ∈ A

instance {n : ℕ} (A : Finset (Fin n × Bool)) (j : Fin n) : Decidable (Fixed A j) :=
  inferInstanceAs (Decidable ((j, true) ∈ A ∨ (j, false) ∈ A))

/-- States of the limited backtracking: `run A` with `A` the schedules fixed so far, or `fail`
(no timetable exists). -/
inductive State (n : ℕ) where
  | run (A : Finset (Fin n × Bool))
  | fail

/-- One move of the limited backtracking of the proof of Proposition 2.4 (pp. 154–155).
From `run A`, for any teacher `j` not yet fixed and any first choice `b` (the arbitrary
decision): if the implications of `A ∪ {(j, b)}` are pairwise non-adjacent the decision is kept;
otherwise the decision is reversed if the implications of `A ∪ {(j, !b)}` are pairwise
non-adjacent; otherwise the procedure fails. A `run A` with every teacher fixed and `fail` have
no moves. -/
inductive Step {n : ℕ} (G : SimpleGraph (Fin n × Bool)) : State n → State n → Prop
  | keep {A : Finset (Fin n × Bool)} {j : Fin n} {b : Bool} :
      ¬ Fixed A j →
      G.IsIndepSet (closure G (insert (j, b) A) : Set (Fin n × Bool)) →
      Step G (State.run A) (State.run (closure G (insert (j, b) A)))
  | reverse {A : Finset (Fin n × Bool)} {j : Fin n} {b : Bool} :
      ¬ Fixed A j →
      ¬ G.IsIndepSet (closure G (insert (j, b) A) : Set (Fin n × Bool)) →
      G.IsIndepSet (closure G (insert (j, !b) A) : Set (Fin n × Bool)) →
      Step G (State.run A) (State.run (closure G (insert (j, !b) A)))
  | fail {A : Finset (Fin n × Bool)} {j : Fin n} {b : Bool} :
      ¬ Fixed A j →
      ¬ G.IsIndepSet (closure G (insert (j, b) A) : Set (Fin n × Bool)) →
      ¬ G.IsIndepSet (closure G (insert (j, !b) A) : Set (Fin n × Bool)) →
      Step G (State.run A) State.fail

/-- The states reachable from the initial state `run ∅` (nothing fixed). -/
def Reachable {n : ℕ} (G : SimpleGraph (Fin n × Bool)) (s : State n) : Prop :=
  Relation.ReflTransGen (Step G) (State.run ∅) s

end Timetabling85.TwoPeriod


