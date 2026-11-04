-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockIndex
-- name    : Submission_ThreeSum_BlockIndex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:25:05.361668+00:00
-- url     : https://prove2.me/theorems/8b809020-6f46-4722-8b69-fe74e7f3b73e
-- title:
--   Block Index
-- statement:
--   Definitions and structural lemmas for Block Index, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Mathlib.Logic.Equiv.Fin.Basic
set_option autoImplicit false
namespace ThreeSum.BlockIndex
open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
def coordEquiv (J L : ℕ) : Coord J L ≃ Fin (J*L) :=
  (Equiv.sigmaEquivProd (Fin J) (Fin L)).trans finProdFinEquiv
def indexSet {J L : ℕ} (S : Finset (Coord J L)) : Finset (Fin (J*L)) :=
  S.map (coordEquiv J L).toEmbedding
def unindexSet {J L : ℕ} (S : Finset (Fin (J*L))) : Finset (Coord J L) :=
  S.map (coordEquiv J L).symm.toEmbedding
def coefficient {h J : ℕ} (o : Occurrences h J) (b : Bool)
    (c : Coord J (512*h)) : ℕ :=
  localPrime h ^ c.1.val * (mapAt h (o c.1) (c.2,b)).val
def maskHash {h J : ℕ} (o : Occurrences h J) (flip : Bool)
    (S : Finset (Coord J (512*h))) : ℕ :=
  OneHotMask.eval
    (OneHotMask.extend (coefficient o flip ∘ (coordEquiv J (512*h)).symm))
    (OneHotMask.extend (coefficient o (!flip) ∘ (coordEquiv J (512*h)).symm))
    (J*(512*h)) (SubsetAddress.subsetMask (indexSet S))
end ThreeSum.BlockIndex


