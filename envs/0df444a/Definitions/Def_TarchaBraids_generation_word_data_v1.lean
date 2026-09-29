-- Prove2me | Definitions.Def_TarchaBraids_generation_word_data_v1
-- name    : TarchaBraids_generation_word_data_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T19:56:16.786279+00:00
-- url     : https://prove2.me/theorems/888281e4-8d07-46a3-a8a6-d3a7f53c59fb
-- title:
--   Finite signed half-twist words for Tarcha generation
-- statement:
--   Signed adjacent Artin generator letters, their free-group evaluation, their positive or reversed elementary half-twist loops, finite word evaluation, and the path-level proposition that every based geometric braid loop has such a finite signed word normal form.
-- source:
--   Formal data layer for Tarcha Teorema 3.11.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

/-!
# Finite signed half-twist words

Reusable signed-word data for the generation branch.

The list order is algebraic order. Because the pinned fundamental group uses
`p * q = q.trans p`, path concatenation is reversed relative to multiplication.
-/

namespace TarchaBraids

open BraidsLinksMCG

noncomputable section

inductive BraidLetterSign where
  | positive
  | negative
  deriving DecidableEq

structure BraidLetter (n : ℕ) where
  index : Fin (n - 1)
  sign : BraidLetterSign
  deriving DecidableEq

def braidLetterFree {n : ℕ} (a : BraidLetter n) : FreeGroup (Fin (n - 1)) :=
  match a.sign with
  | .positive => FreeGroup.of a.index
  | .negative => (FreeGroup.of a.index)⁻¹

def braidLetterLoop (n : ℕ) (a : BraidLetter n) :
    Path (baseUnordered n) (baseUnordered n) :=
  match a.sign with
  | .positive => halfTwistLoop n a.index
  | .negative => (halfTwistLoop n a.index).symm

def braidWordFree {n : ℕ} : List (BraidLetter n) → FreeGroup (Fin (n - 1))
  | [] => 1
  | a :: w => braidLetterFree a * braidWordFree w

def braidWordLoop (n : ℕ) : List (BraidLetter n) →
    Path (baseUnordered n) (baseUnordered n)
  | [] => Path.refl (baseUnordered n)
  | a :: w => (braidWordLoop n w).trans (braidLetterLoop n a)

/-- Path-level normal form needed for Tarcha's generation theorem. -/
def EveryLoopHasBraidWord (n : ℕ) : Prop :=
  ∀ γ : Path (baseUnordered n) (baseUnordered n),
    ∃ w : List (BraidLetter n), Path.Homotopic γ (braidWordLoop n w)

end

end TarchaBraids


