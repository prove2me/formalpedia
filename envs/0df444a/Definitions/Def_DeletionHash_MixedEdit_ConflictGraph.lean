-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_ConflictGraph
-- name    : DeletionHash_MixedEdit_ConflictGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:21.27507+00:00
-- url     : https://prove2.me/theorems/441db9b4-9cef-4cad-b41c-c19224f47587
-- title:
--   Exceptional equal-label conflicts and their surviving graph
-- statement:
--   For a fixed hash, the exceptional family $E$ contains exactly the $k$-unique length-$n$ words having a valid record of at most $2t$ edits leading to a distinct length-$n$ word with the same label, when the record is shorter than $2t$ or is not separated. The target need not be unique. The graph $\Gamma_H$ has vertices $W_{n,k}\setminus E$ and joins distinct confusable equal-label words. The bad-component event means the word survives and its graph component admits no two-colouring. It is false for a discarded word and is an unconditional event. Edges are defined from the channel, without assuming a catalogue representation or bipartiteness.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 3.4 and Definition 3.5, printed p. 10 (PDF p. 12); §6.2, unconditional discard event, printed p. 19 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Labels
import Definitions.Def_DeletionHash_MixedEdit_Channel
import Definitions.Def_DeletionHash_MixedEdit_Regime

namespace DeletionHash.MixedEdit

universe u

def Exceptional {α : Type u} [Fintype α] [DecidableEq α] {L r : ℕ}
    (n k t b : ℕ) (ξ : HashSample α L r) (x : Word α n) : Prop :=
  IsUnique k (letters x) ∧ ∃ record : List (Edit α),
    record.length ≤ 2*t ∧ ValidRecord b (letters x) record ∧
    (target (letters x) record).length = n ∧ target (letters x) record ≠ letters x ∧
    hash ξ (spectrum L (target (letters x) record)) = hash ξ (spectrum L (letters x)) ∧
    (record.length < 2*t ∨ ¬ Separated n t b L record)

def Good {α : Type u} [Fintype α] [DecidableEq α] {L r : ℕ}
    (n k t b : ℕ) (ξ : HashSample α L r) (x : Word α n) : Prop :=
  IsUnique k (letters x) ∧ ¬ Exceptional n k t b ξ x

def conflictGraph {α : Type u} [Fintype α] [DecidableEq α] {L r : ℕ}
    (n k t b : ℕ) (ξ : HashSample α L r) : SimpleGraph {x : Word α n // Good n k t b ξ x} where
  Adj x y := x ≠ y ∧ Confusable b t (letters x.val) (letters y.val) ∧
    hash ξ (spectrum L (letters x.val)) = hash ξ (spectrum L (letters y.val))
  symm := by
    constructor
    intro x y h
    rcases h with ⟨hne, ⟨z, hx, hy⟩, heq⟩
    exact ⟨hne.symm, ⟨z, hy, hx⟩, heq.symm⟩
  loopless := by constructor; intro x h; exact h.1 rfl

/-- False for discarded x. On a vertex this is failure of a two-colouring of its component. -/
def BadComponent {α : Type u} [Fintype α] [DecidableEq α] {L r : ℕ}
    (n k t b : ℕ) (ξ : HashSample α L r) (x : Word α n) : Prop :=
  ∃ hx : Good n k t b ξ x,
    ¬ ∃ color : {y : Word α n // Good n k t b ξ y} → Fin 2,
      ∀ y z, (conflictGraph n k t b ξ).Reachable ⟨x,hx⟩ y →
        (conflictGraph n k t b ξ).Reachable ⟨x,hx⟩ z →
        (conflictGraph n k t b ξ).Adj y z → color y ≠ color z

end DeletionHash.MixedEdit


