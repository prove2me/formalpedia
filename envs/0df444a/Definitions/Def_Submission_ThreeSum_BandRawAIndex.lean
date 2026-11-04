-- Prove2me | Definitions.Def_Submission_ThreeSum_BandRawAIndex
-- name    : Submission_ThreeSum_BandRawAIndex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:28:33.552954+00:00
-- url     : https://prove2.me/theorems/30311853-a618-47ff-8b45-2c2800f446c0
-- title:
--   Band Raw AIndex
-- statement:
--   Definitions and structural lemmas for Band Raw AIndex, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
set_option autoImplicit false
namespace ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
def labelAt (n g : ℕ) (rs : List Record) (i : ℕ) : Label :=
  (items n g rs).getD i default
def ownerRecord (n g : ℕ) (rs : List Record) (i : ℕ) : Record :=
  rs.getD (labelAt n g rs i).owner default
def localA (n g : ℕ) (rs : List Record) (i : ℕ) : ℕ :=
  (labelAt n g rs i).position-BandPartition.start g (ownerRecord n g rs i).a
end ThreeSum.BandRawA


