-- Prove2me | Definitions.Def_Submission_ThreeSum_BandRawA
-- name    : Submission_ThreeSum_BandRawA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:19:23.532576+00:00
-- url     : https://prove2.me/theorems/61186d9c-e2b2-49ab-8376-ca6d360b9224
-- title:
--   Band Raw A
-- statement:
--   Definitions and structural lemmas for Band Raw A, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
set_option autoImplicit false
namespace ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
structure Label where
  owner : ℕ
  position : ℕ
  deriving DecidableEq, Inhabited
def bandLength (n g a : ℕ) : ℕ := stop n g a-start g a
def row (n g owner : ℕ) (r : Record) : List Label :=
  if r.flag=1 then
    (List.range (bandLength n g r.a)).map (fun j => ⟨owner,start g r.a+j⟩)
  else []
def firstRows (n g : ℕ) (rs : List Record) (i : ℕ) : List Label :=
  (List.range i).flatMap fun owner => row n g owner (rs.getD owner default)
def items (n g : ℕ) (rs : List Record) : List Label := firstRows n g rs rs.length
def count (n g : ℕ) (rs : List Record) (i : ℕ) : ℕ := (firstRows n g rs i).length
def values (f : ℕ → ℤ) (ls : List Label) : List ℤ := ls.map (fun l => f l.position)
def ownerLabels (ls : List Label) : List ℤ := ls.map (fun l => (l.owner : ℤ))
def positionLabels (ls : List Label) : List ℤ := ls.map (fun l => (l.position : ℤ))
end ThreeSum.BandRawA


