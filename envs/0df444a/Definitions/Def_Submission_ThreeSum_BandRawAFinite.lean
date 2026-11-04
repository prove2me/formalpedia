-- Prove2me | Definitions.Def_Submission_ThreeSum_BandRawAFinite
-- name    : Submission_ThreeSum_BandRawAFinite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:41:29.561682+00:00
-- url     : https://prove2.me/theorems/8cddbc83-81a5-4a3d-a4f5-67fdd4a40e0b
-- title:
--   Band Raw AFinite
-- statement:
--   Definitions and structural lemmas for Band Raw AFinite, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean

import Definitions.Def_Submission_ThreeSum_BandRawAScore
set_option autoImplicit false
namespace ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
def coordinates {a b c : ℕ} (t : Fin a × Fin b × Fin c) : ℕ × ℕ × ℕ :=
  (t.1.val,t.2.1.val,t.2.2.val)
def finiteAIndices (n g : ℕ) (rs : List Record) (s : ℕ) :
    Finset (Fin (items n g rs).length) :=
  univ.filter fun i => i.val ∈ aIndices n g rs s
def finiteBandPositions (n g a : ℕ) : Finset (Fin n) :=
  univ.filter fun i => i.val ∈ bandPositions n g a
def finiteOwnerProduct (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) :
    Finset (Fin (items nA g rs).length × Fin nB × Fin nC) :=
  finiteAIndices nA g rs s ×ˢ (finiteBandPositions nB g (rs.getD s default).b ×ˢ
    finiteBandPositions nC g (rs.getD s default).c)
def finiteAllProducts (nA nB nC g : ℕ) (rs : List Record) :
    Finset (Fin (items nA g rs).length × Fin nB × Fin nC) :=
  univ.filter fun t => coordinates t ∈ allProducts nA nB nC g rs
end ThreeSum.BandRawA


