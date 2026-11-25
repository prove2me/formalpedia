-- Prove2me | Definitions.Def_AllOnesComparator_Solution
-- name    : AllOnesComparator_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T20:58:12.77761+00:00
-- url     : https://prove2.me/theorems/5ffe3672-2c46-49e4-a1c6-6d9bdb03c965
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Brandon M. Yates (BrandonMYates/allones-comparator; see pinned Apache-2.0 LICENSE and README.md)'s pinned All-ones polynomials over GF(2) under the quadratic substitution (OEIS A071642, TheoremDB P12771) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/Solution.lean

import Definitions.Def_AllOnesLab
set_option autoImplicit true
open Polynomial
namespace AllOnesGallardo
noncomputable def allOnes (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), X ^ i
noncomputable def P : (ZMod 2)[X] := X ^ 2 + X + 1
noncomputable def allOnesP (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), P ^ i
example : @allOnes = @AllOnesLab.allOnes := rfl
example : P = AllOnesLab.P := rfl
example : @allOnesP = @AllOnesLab.allOnesP := rfl
end AllOnesGallardo


