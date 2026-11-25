-- Prove2me | Definitions.Def_AllOnesLab_Defs
-- name    : AllOnesLab_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T20:48:06.228093+00:00
-- url     : https://prove2.me/theorems/098d826f-807a-5bf0-a4ef-02bef2b04b92
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Brandon M. Yates (BrandonMYates/allones-comparator; see pinned Apache-2.0 LICENSE and README.md)'s pinned All-ones polynomials over GF(2) under the quadratic substitution (OEIS A071642, TheoremDB P12771) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Defs.lean

import Mathlib
set_option autoImplicit true
open Polynomial
namespace AllOnesLab
noncomputable def allOnes (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), X ^ i
noncomputable def P : (ZMod 2)[X] := X ^ 2 + X + 1
noncomputable def allOnesP (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), P ^ i
end AllOnesLab


