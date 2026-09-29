-- Prove2me | Definitions.Def_TarchaBraids_adjacent_word_loops_v1
-- name    : TarchaBraids_adjacent_word_loops_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T09:34:13.769375+00:00
-- url     : https://prove2.me/theorems/4a704e4e-3a2c-4f75-89e6-070cdff010c5
-- title:
--   Tarcha adjacent braid-word loops
-- statement:
--   The two concatenated three-half-twist loops representing the left and right adjacent Artin braid words.
-- source:
--   Modular loop definitions extracted from Tarcha's adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

noncomputable section

open BraidsLinksMCG

def leftBraidWordLoop (n : ℕ) (i j : Fin (n - 1)) :
    Path (baseUnordered n) (baseUnordered n) :=
  (halfTwistLoop n i).trans ((halfTwistLoop n j).trans (halfTwistLoop n i))

def rightBraidWordLoop (n : ℕ) (i j : Fin (n - 1)) :
    Path (baseUnordered n) (baseUnordered n) :=
  (halfTwistLoop n j).trans ((halfTwistLoop n i).trans (halfTwistLoop n j))

end

end TarchaBraids


