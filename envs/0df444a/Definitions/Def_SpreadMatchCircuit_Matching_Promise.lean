-- Prove2me | Definitions.Def_SpreadMatchCircuit_Matching_Promise
-- name    : SpreadMatchCircuit_Matching_Promise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:39.834928+00:00
-- url     : https://prove2.me/theorems/3b96de27-aede-463b-9b83-2c7295995582
-- title:
--   A circuit distinguishing $k$-matchings from graphs with no $q$-matching
-- statement:
--   A monotone circuit $C$ whose variables are the edges of $[n]$ reads a graph $x$ through its edge indicators: the variable $e$ has value $1$ exactly when $e\in x$.
--
--   Fix a partition $(L,L^{\mathrm c})$ of $[n]$. The circuit **distinguishes** $k$-matchings from graphs with no $q$-matching on this partition if, for every graph $x$ that is bipartite with sides $L$ and $L^{\mathrm c}$,
--
--   1. $C(x)=1$ if $x$ has a matching of size $k$, and
--   2. $C(x)=0$ if $x$ has no matching of size $q$.
--
--   Nothing is required on other inputs: the gap between the two conditions and the graphs that are not bipartite with these sides are unconstrained.
--
--   This is the promise problem of Theorem 1 of the source.
--
--   **Formalization Note** A circuit correct on all $n$-vertex bipartite graphs satisfies this definition for every $L$, so the fixed-partition promise is the weaker requirement on $C$.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 2, Theorem 1 (the promise)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_MonotoneCircuit

namespace SpreadMatchCircuit.Matching

variable {n : ℕ}

/-- The edge-indicator assignment of the graph `x`. -/
def graphInput (x : Finset (Edge n)) : Edge n → Bool := fun e => decide (e ∈ x)

/-- `C` distinguishes, among the graphs bipartite with sides `L` and `Lᶜ`, those with a matching
of size `k` from those with no matching of size `q`: it outputs `1` on the former and `0` on the
latter. Behaviour on every other input is unconstrained. -/
def DistinguishesMatchings (C : MonotoneCircuit (Edge n)) (L : Finset (Fin n)) (k q : ℕ) : Prop :=
  ∀ x : Finset (Edge n), IsCrossGraph L x →
    (HasMatchingOfSize x k → C.eval (graphInput x) = true) ∧
    (¬ HasMatchingOfSize x q → C.eval (graphInput x) = false)

end SpreadMatchCircuit.Matching


