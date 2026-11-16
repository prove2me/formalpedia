-- Prove2me | Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Rounds
-- name    : AnonymousDirectedCounting_Exact_Supplement_Rounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:50:23.184764+00:00
-- url     : https://prove2.me/theorems/e94e248b-4e9b-4bcf-96c9-d03bc78e179a
-- title:
--   One-round realizations of full history-prefix data, and path connectivity
-- statement:
--   Let $\mathrm{Old}$ and $\mathrm{New}$ be finite sets of old and new history-tree nodes with parent map $\pi:\mathrm{New}\to\mathrm{Old}$, anonymities $a(v)$, outdegrees $d(v)$, and required receipts $\mu(u,v)$, the number of arcs that every agent of the fiber of $v$ receives from the fiber of the old node $u$. Put $N=\sum_v a(v)$.
--
--   A **strongly connected round realization** of these data consists of an assignment of the $N$ agents to new nodes, exactly $a(v)$ of them to $v$, and a round multigraph on the agents (loops and parallel arcs allowed) in which every agent of $v$ has outdegree $d(v)$, every agent of $v$ receives exactly $\mu(u,v)$ arcs from the agents whose new node has parent $u$, and every nonempty proper set of agents has an outgoing arc.
--
--   A relation is **path connected** when every ordered pair of elements is joined by a directed path of related steps (the empty path joining an element to itself).
--
--   These objects state the realizability criterion used by the certificate verifier of Appendix E.
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 25 (PDF p. 27), Appendix E.3, Lemmas 10–11

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_NetworkModel

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact.Supplement

open AnonymousDirectedCounting.Exact
open scoped Classical

noncomputable section

/-- Every ordered pair is joined by a directed path (the empty path for equal endpoints). -/
def PathConnected {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x y : α, Relation.ReflTransGen R x y

/-- A strongly connected round realization of one level of proposed full history-prefix data
(Lemma 11, printed p. 25, PDF p. 27). The `N = ∑ a(v)` agents are `Fin N`; `f` sends each agent to its
new node, with exactly `a(v)` agents on `v`; the fiber of an old node `u` is the set of agents whose
new node has parent `u`. Every agent of `v` has outdegree `d(v)` and receives exactly `μ(u, v)` arcs
from the fiber of `u`; loops and parallel arcs are allowed; the round graph is strongly connected. -/
def RoundRealization {Old New : Type} [Fintype New] (π : New → Old) (a d : New → ℕ)
    (μ : Old → New → ℕ) : Prop :=
  ∃ (f : Fin (∑ v, a v) → New) (e : Fin (∑ v, a v) → Fin (∑ v, a v) → ℕ),
    (∀ v : New, (Finset.univ.filter (fun x => f x = v)).card = a v) ∧
    (∀ x, ∑ y, e x y = d (f x)) ∧
    (∀ (x : Fin (∑ v, a v)) (u : Old),
      ∑ y ∈ Finset.univ.filter (fun y => π (f y) = u), e y x = μ u (f x)) ∧
    StronglyConnected e

end

end AnonymousDirectedCounting.Exact.Supplement


