-- Prove2me | Definitions.Def_BuchiRabinIndex_LowerBound_Rabin
-- name    : BuchiRabinIndex_LowerBound_Rabin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:46.243785+00:00
-- url     : https://prove2.me/theorems/78358b3d-25ed-419a-8df7-9b4bbfd65f71
-- title:
--   Rabin conditions, history traces, and cycles
-- statement:
--   A history trace on $\alpha$ begins in the initial tree and follows the partial successor at every step. Its transition sequence consists of triples $(H_i,\alpha(i),H_{i+1})$. A finite Rabin condition is a finite set of pairs of arbitrary sets. A pair $(A,R)$ accepts an infinite recurring set $D$ precisely when
--   $$D\cap A\ne\varnothing\quad\text{and}\quad D\cap R=\varnothing.$$
--
--   Transition acceptance applies this rule to the infinitely recurring transitions; state acceptance applies it to infinitely recurring history trees. A condition is correct exactly when the resulting language equals the run-defined $L(B)$. Both languages require an infinite trace, so every dying trace is rejected, regardless of the pair sets.
--
--   A closed walk has positive length, begins at a reachable history tree, and ends there. A cycle is exactly the edge set of such a walk. An accepting cycle is a cycle all of whose infinite realizations belong to $L(B)$; a rejecting cycle requires every realization to be outside $L(B)$. Finite words, their visited histories, and their actual edge sets are defined by iterating the concrete successor.
--
--   The edge carrier permits arbitrary triples, but traces and walk edge sets contain only actual successors. Arbitrary unreachable or nonactual triples in pair components do not affect acceptance.
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Definition 1, pp. 4–5; §2.4, p. 9; §6.1, pp. 25–26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_History

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound
noncomputable section
open scoped Classical

/-- Actual edges are triples whose third component is the partial successor. -/
abbrev Edge (Q Sigma : Type) := History Q × Sigma × History Q

def IsEdge {Q Sigma : Type} (B : NBW Q Sigma) (e : Edge Q Sigma) : Prop :=
  successor B e.1 e.2.1 = some e.2.2

def acc {Q Sigma : Type} (B : NBW Q Sigma) (e : Edge Q Sigma) : Finset Node :=
  acceptingNodes B e.1 e.2.1

def unst {Q Sigma : Type} (B : NBW Q Sigma) (e : Edge Q Sigma) : Finset Node :=
  unstable B e.1 e.2.1

def IsTrace {Q Sigma : Type} (B : NBW Q Sigma) (α : ℕ → Sigma)
    (ρ : ℕ → History Q) : Prop :=
  initialHistory B = some (ρ 0) ∧ ∀ i, successor B (ρ i) (α i) = some (ρ (i + 1))

def edgeSequence {Q Sigma : Type} (α : ℕ → Sigma) (ρ : ℕ → History Q) : ℕ → Edge Q Sigma :=
  fun i => (ρ i, α i, ρ (i + 1))

abbrev RabinPair (X : Type) := Set X × Set X
abbrev RabinCondition (X : Type) := Finset (RabinPair X)

def PairAccepts {X : Type} (p : RabinPair X) (D : Set X) : Prop :=
  (D ∩ p.1).Nonempty ∧ D ∩ p.2 = ∅

def transitionLanguage {Q Sigma : Type} (B : NBW Q Sigma)
    (r : RabinCondition (Edge Q Sigma)) : Set (ℕ → Sigma) :=
  {α | ∃ ρ, IsTrace B α ρ ∧ ∃ p ∈ r, PairAccepts p (infSet (edgeSequence α ρ))}

def stateLanguage {Q Sigma : Type} (B : NBW Q Sigma)
    (r : RabinCondition (History Q)) : Set (ℕ → Sigma) :=
  {α | ∃ ρ, IsTrace B α ρ ∧ ∃ p ∈ r, PairAccepts p (infSet ρ)}

def CorrectTransition {Q Sigma : Type} (B : NBW Q Sigma)
    (r : RabinCondition (Edge Q Sigma)) : Prop := transitionLanguage B r = language B

def CorrectState {Q Sigma : Type} (B : NBW Q Sigma)
    (r : RabinCondition (History Q)) : Prop := stateLanguage B r = language B

/-- Deterministic finite-word iteration, propagated through Option without a sink. -/
def readWord {Q Sigma : Type} (B : NBW Q Sigma) :
    Option (History Q) → List Sigma → Option (History Q)
  | H, [] => H
  | H, σ :: v => readWord B (H.bind fun h => successor B h σ) v

def Reachable {Q Sigma : Type} (B : NBW Q Sigma) (H : History Q) : Prop :=
  ∃ v, readWord B (initialHistory B) v = some H

/-- Exactly the edges traversed, including no triples with an incorrect target. -/
def wordEdges {Q Sigma : Type} (B : NBW Q Sigma) (H : Option (History Q))
    (v : List Sigma) : Set (Edge Q Sigma) :=
  {e | ∃ i : Fin v.length, readWord B H (v.take i.val) = some e.1 ∧
    e.2.1 = v[i] ∧ successor B e.1 e.2.1 = some e.2.2}

def ClosedWalk {Q Sigma : Type} (B : NBW Q Sigma) (H : History Q) (v : List Sigma) : Prop :=
  0 < v.length ∧ Reachable B H ∧ readWord B (some H) v = some H

def Cycle {Q Sigma : Type} (B : NBW Q Sigma) (D : Set (Edge Q Sigma)) : Prop :=
  ∃ H v, ClosedWalk B H v ∧ wordEdges B (some H) v = D

def AcceptingCycle {Q Sigma : Type} (B : NBW Q Sigma) (D : Set (Edge Q Sigma)) : Prop :=
  Cycle B D ∧ ∀ α ρ, IsTrace B α ρ → infSet (edgeSequence α ρ) = D → α ∈ language B

def RejectingCycle {Q Sigma : Type} (B : NBW Q Sigma) (D : Set (Edge Q Sigma)) : Prop :=
  Cycle B D ∧ ∀ α ρ, IsTrace B α ρ → infSet (edgeSequence α ρ) = D → α ∉ language B

def visited {Q Sigma : Type} (B : NBW Q Sigma) (H : History Q) (v : List Sigma) : Set (History Q) :=
  {K | ∃ i ≤ v.length, readWord B (some H) (v.take i) = some K}

end
end BuchiRabinIndex.LowerBound


