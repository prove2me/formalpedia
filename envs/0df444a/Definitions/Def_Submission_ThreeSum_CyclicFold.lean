-- Prove2me | Definitions.Def_Submission_ThreeSum_CyclicFold
-- name    : Submission_ThreeSum_CyclicFold
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:14:05.171844+00:00
-- url     : https://prove2.me/theorems/28ef995a-be1e-45ad-aefe-ca479eca0ffe
-- title:
--   Cyclic Fold
-- statement:
--   Definitions and structural lemmas for Cyclic Fold, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
set_option autoImplicit false
namespace ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators
def cyclic (p : ℕ) (as bs : List ℤ) (r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
    if (i + j) % p = r then as.getD i 0 * bs.getD j 0 else 0
def vector (p : ℕ) (f : ZMod p → ℕ) : List ℤ :=
  (List.range p).map fun (i : ℕ) => (f (i : ZMod p) : ℤ)
def padTo (n : ℕ) (as : List ℤ) : List ℤ :=
  as ++ List.replicate (n - as.length) 0
end ThreeSum.CyclicFold


