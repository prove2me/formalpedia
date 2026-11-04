-- Prove2me | Definitions.Def_Submission_ThreeSum_Auxiliary
-- name    : Submission_ThreeSum_Auxiliary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:55.617842+00:00
-- url     : https://prove2.me/theorems/3a3d999c-4b05-4a48-802f-78b11d60bab1
-- title:
--   Auxiliary
-- statement:
--   Definitions and structural lemmas for Auxiliary, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
set_option autoImplicit false
namespace ThreeSum.Auxiliary
open Finset
open scoped BigOperators
def moduli (C : Finset ℕ) : Finset ℤ := C.image (fun p : ℕ => (p : ℤ))
end ThreeSum.Auxiliary


