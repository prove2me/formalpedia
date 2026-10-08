-- Prove2me | Definitions.Def_TwoWayComplementation
-- name    : TwoWayComplementation
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:35.640351+00:00
-- url     : https://prove2.me/theorems/c771a940-cc09-4ba1-846f-e4ea0ed1c6ba
-- statement:
--   For a binary relation R on a type α, relStar(R) is its reflexive transitive closure: the set of pairs (x,y) such that y can be reached from x by finitely many (possibly zero) R-steps. A TwoNFA over an alphabet Sigma with state type Q is a nondeterministic two-way automaton given by an initial state, a set of accepting states, and a transition function sending each state and each tape symbol, which is either one of two endmarkers (Fin 2, index 0 on the left and 1 on the right) or a letter of Sigma, to a set of pairs (next state, move), where the move is an element of Fin 3. For a word w, tapeSymbol(w,p) reads the tape of length |w|+2 with positions 0,…,|w|+1: position 0 holds the left endmarker, position |w|+1 holds the right endmarker, and position p in between holds the letter w[p−1]. A configuration is a pair (state, head position), and the step relation for w relates c to d when some move m in Fin 3 has (d's state, m) in the transition set for c's state and the symbol under c's head, and d's head position equals c's head position plus m minus 1, so moves 0, 1, 2 shift the head left, keep it in place, or shift it right; since positions are confined to the tape, steps that would leave it are not allowed. The language of the automaton is the set of words w for which some configuration with an accepting state is reachable, via relStar of the step relation, from the initial state with the head at position 0. The block only defines these notions and states no theorem, such as closure under complementation.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TwoWayComplementation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TwoWayComplementation.lean; bytes 16..1061
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

def relStar {α : Type*} (R : SetRel α α) : SetRel α α :=
  {(x, y) | Relation.ReflTransGen (fun a b => (a, b) ∈ R) x y}

structure TwoNFA (Sigma Q : Type*) where
  initial : Q
  accepting : Set Q
  transition : Q → (Fin 2 ⊕ Sigma) → Set (Q × Fin 3)

def tapeSymbol {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) : Fin 2 ⊕ Sigma :=
  if hleft : p.val = 0 then .inl 0
  else if hright : p.val = w.length + 1 then .inl 1
  else .inr (w[p.val - 1]'(by omega))

namespace TwoNFA

def step {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma) :
    SetRel (Q × Fin (w.length + 2)) (Q × Fin (w.length + 2)) :=
  {(c, d) | ∃ move : Fin 3,
    (d.1, move) ∈ A.transition c.1 (tapeSymbol w c.2) ∧
    (d.2.val : ℤ) = (c.2.val : ℤ) + (move.val : ℤ) - 1}

def language {Sigma Q : Type*} (A : TwoNFA Sigma Q) : Set (List Sigma) :=
  {w | ∃ c, c.1 ∈ A.accepting ∧
    ((A.initial, ⟨0, by omega⟩), c) ∈ relStar (A.step w)}

end TwoNFA



end TwoWayComplementation
end OAI


