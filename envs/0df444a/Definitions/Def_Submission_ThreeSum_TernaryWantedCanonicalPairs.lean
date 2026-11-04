-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
-- name    : Submission_ThreeSum_TernaryWantedCanonicalPairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:22:27.064135+00:00
-- url     : https://prove2.me/theorems/9b095303-0ae2-4982-b9cb-4cccfc972a64
-- title:
--   Ternary Wanted Canonical Pairs
-- statement:
--   Definitions and structural lemmas for Ternary Wanted Canonical Pairs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
set_option autoImplicit false
namespace ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix
def wantedCodes (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (code R mapCode S : ℕ) : List (ℕ × ℕ) :=
  (wantedOutputs p raws j x).map fun is =>
    (TernaryWantedCanonical.encode words R code is,TernaryWantedCanonical.encode maps S mapCode is)
def rowCells (original : ℕ) (codes : List (ℕ × ℕ)) : List ℤ :=
  codes.flatMap fun code => [(original : ℤ),(code.1 : ℤ),(code.2 : ℤ)]
def blockWords (localWords : ℕ → List ℕ) (is : List ℕ) : List ℕ := is.flatMap localWords
end ThreeSum.TernaryWantedCanonicalPairs


