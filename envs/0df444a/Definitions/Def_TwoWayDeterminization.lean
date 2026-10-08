-- Prove2me | Definitions.Def_TwoWayDeterminization
-- name    : TwoWayDeterminization
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:35.869981+00:00
-- url     : https://prove2.me/theorems/e7c115e1-4948-4d2f-8800-97f760d3c950
-- statement:
--   relStar(R) is the reflexive transitive closure of a relation R on a set, so every element is related to itself by the empty path. A TwoNFA over an alphabet Sigma with state type Q is a read-only two-way nondeterministic automaton given by an initial state, a set of accepting states, and a transition function sending each state and scanned symbol to a set of pairs (next state, move code). Scanned symbols are either one of two distinct endmarkers, Sum.inl 0 and Sum.inl 1, or a letter of Sigma, and move codes 0, 1, 2 mean left, stay, right. For an input word w, tapeSymbol places the left endmarker at position 0, the letters of w at positions 1 through |w|, and the right endmarker at position |w|+1, even when w is empty. A configuration is a pair of a state and a head position in {0,...,|w|+1}. The step relation holds from c to d when some move m has (next state of d, m) in the transition set of c's state and scanned symbol, and the new position equals the old position plus m minus 1, which keeps the head within the marked input. The language of the automaton is the set of words w for which some configuration with an accepting state is reachable, by a run of length zero or more, from the initial state at position 0 on the left endmarker. Deterministic means that every state and scanned symbol has at most one transition pair (a subsingleton set). For a set H, relationProduct of a list of relations on H is their composition via a right fold, with the empty list giving the identity relation, and sourceLanguage(H) is the set of lists of relations on H whose relationProduct is nonempty. These are definitions only, with no theorem about determinization asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TwoWayDeterminization.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TwoWayDeterminization.lean; bytes 16..2264
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Reflexive transitive closure, including the empty path. -/
def relStar {α : Type*} (R : SetRel α α) : SetRel α α :=
  {(x, y) | Relation.ReflTransGen (fun a b => (a, b) ∈ R) x y}

/-- A read-only 2NFA. The two endmarkers are `Sum.inl 0` and `Sum.inl 1`.
    Move codes 0, 1, 2 mean left, stay, right. -/
structure TwoNFA (Sigma Q : Type*) where
  /-- The state in which the machine starts on the left endmarker. -/
  initial : Q
  /-- States whose occurrence on a finite run constitutes acceptance. -/
  accepting : Set Q
  /-- Allowed next-state and move pairs, determined by the state and scanned symbol. -/
  transition : Q → (Fin 2 ⊕ Sigma) → Set (Q × Fin 3)

/-- Tape lookup includes two distinct endmarkers, even on empty input. -/
def tapeSymbol {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) : Fin 2 ⊕ Sigma :=
  if hleft : p.val = 0 then .inl 0
  else if hright : p.val = w.length + 1 then .inl 1
  else .inr (w[p.val - 1]'(by omega))

namespace TwoNFA

/-- One legal step: both head positions stay within the marked input. -/
def step {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma) :
    SetRel (Q × Fin (w.length + 2)) (Q × Fin (w.length + 2)) :=
  {(c, d) | ∃ move : Fin 3,
    (d.1, move) ∈ A.transition c.1 (tapeSymbol w c.2) ∧
    (d.2.val : ℤ) = (c.2.val : ℤ) + (move.val : ℤ) - 1}

/-- Existential finite-run acceptance, allowing a run of length zero. -/
def language {Sigma Q : Type*} (A : TwoNFA Sigma Q) : Set (List Sigma) :=
  {w | ∃ c, c.1 ∈ A.accepting ∧
    ((A.initial, ⟨0, by omega⟩), c) ∈ relStar (A.step w)}

end TwoNFA

/-- At most one next-state/move pair at every state and scanned symbol. -/
def TwoNFA.Deterministic {Sigma Q : Type*} (A : TwoNFA Sigma Q) : Prop :=
  ∀ q symbol, (A.transition q symbol).Subsingleton

/-- Relation product for an input word; the empty product is the identity. -/
def relationProduct {H : Type*} (w : List (SetRel H H)) : SetRel H H :=
  w.foldr SetRel.comp SetRel.id

/-- The source language consists of the words with nonempty relation product. -/
def sourceLanguage (H : Type*) : Set (List (SetRel H H)) :=
  {w | (relationProduct w).Nonempty}



end TwoWayComplementation
end OAI


