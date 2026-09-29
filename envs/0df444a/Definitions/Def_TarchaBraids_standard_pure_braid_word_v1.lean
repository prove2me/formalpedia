-- Prove2me | Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
-- name    : TarchaBraids_standard_pure_braid_word_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-22T08:40:15.765447+00:00
-- url     : https://prove2.me/theorems/c33bae80-6988-4cd4-9cda-0fa398df6ff8
-- title:
--   The classical pure half-twist word for a standard punctured-plane loop
-- statement:
--   The explicit signed adjacent-generator word σ_{n-1}⋯σ_{j+1} σ_j² σ_{j+1}^{-1}⋯σ_{n-1}^{-1} for the pure braid in which the last strand encircles puncture j.
-- source:
--   Classical pure braid generator A_{i,n+1}.

import Mathlib
import Definitions.Def_TarchaBraids_generation_word_data_v1

/-!
# The classical pure braid word for a punctured-plane standard loop

For the standard loop in which the last strand encircles puncture `j`, the
classical Artin word is

`σ_{n-1} ... σ_{j+1} σ_j^2 σ_{j+1}^{-1} ... σ_{n-1}^{-1}`

in zero-based generator indexing.
-/

namespace TarchaBraids

noncomputable section

/-- The signed adjacent-generator word for the pure braid in which the last
strand encircles puncture `j`. The list is in algebraic multiplication order. -/
def standardPureBraidWord (n : ℕ) (j : Fin n) : List (BraidLetter (n + 1)) :=
  let higher := (List.finRange n).filter (fun k => j < k)
  let positive : Fin n → BraidLetter (n + 1) := fun k =>
    { index := Fin.cast (by omega) k
      sign := .positive }
  let negative : Fin n → BraidLetter (n + 1) := fun k =>
    { index := Fin.cast (by omega) k
      sign := .negative }
  higher.reverse.map positive ++
    [positive j, positive j] ++
    higher.map negative

end

end TarchaBraids


