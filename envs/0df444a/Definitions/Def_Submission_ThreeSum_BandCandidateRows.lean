-- Prove2me | Definitions.Def_Submission_ThreeSum_BandCandidateRows
-- name    : Submission_ThreeSum_BandCandidateRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:12:17.982687+00:00
-- url     : https://prove2.me/theorems/da9dc394-7774-4f25-9c6e-25583e7df4f6
-- title:
--   Band Candidate Rows
-- statement:
--   Definitions and structural lemmas for Band Candidate Rows, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
set_option autoImplicit false
namespace ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
inductive Mode where
  | bc
  | ab
  | ac
  deriving DecidableEq
structure Record where
  flag : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  deriving DecidableEq, Inhabited
def make (mode : Mode) (i j r : ℕ) : Record :=
  match mode with
  | .bc => ⟨if 0 < r then 1 else 0, r - 1, i, j⟩
  | .ab => ⟨if 0 < r then 1 else 0, i, j, r - 1⟩
  | .ac => ⟨if 0 < r then 1 else 0, i, r - 1, j⟩
def Record.cells (r : Record) : List ℤ :=
  [r.flag, r.a, r.b, r.c]
def bc (A B C : Family) (j k : ℕ) : Record :=
  make .bc j k (LightBandLookup.result A.lower A.upper A.size (C.lower k - B.upper j))
def ab (A B C : Family) (i j : ℕ) : Record :=
  make .ab i j (LightBandLookup.result C.lower C.upper C.size (A.lower i + B.lower j))
def ac (A B C : Family) (i k : ℕ) : Record :=
  make .ac i k (LightBandLookup.result B.lower B.upper B.size (C.lower k - A.lower i))
def rect (m n : ℕ) (F : ℕ → ℕ → Record) : List Record :=
  (List.range m).flatMap fun i => (List.range n).map (F i)
def records (A B C : Family) : List Record :=
  rect B.size C.size (bc A B C) ++ (rect A.size B.size (ab A B C) ++ rect A.size C.size (ac A B C))
def cells (rs : List Record) : List ℤ :=
  rs.flatMap Record.cells
def slot (A B C : Family) : Owner A B C → ℕ
  | .inl (j, k) => j.val * C.size + k.val
  | .inr (i, .inl j) => B.size * C.size + i.val * B.size + j.val
  | .inr (i, .inr k) => B.size * C.size + A.size * B.size + i.val * C.size + k.val
def fromOwner (A B C : Family) : Owner A B C → Record
  | .inl (j, k) => bc A B C j.val k.val
  | .inr (i, .inl j) => ab A B C i.val j.val
  | .inr (i, .inr k) => ac A B C i.val k.val
def fromTriple {A B C : Family} (t : Triple A B C) : Record :=
  ⟨1, t.1.val, t.2.1.val, t.2.2.val⟩
end ThreeSum.BandCandidateRows


