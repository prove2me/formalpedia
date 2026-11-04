-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockRows
-- name    : Submission_ThreeSum_BlockRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:35.366178+00:00
-- url     : https://prove2.me/theorems/d9c10fcc-a7ac-4037-940a-bfc3b07e5ae7
-- title:
--   Block Rows
-- statement:
--   Definitions and structural lemmas for Block Rows, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace ThreeSum.BlockRows
open Finset
open scoped BigOperators
abbrev Coord (J L : ℕ) := Σ _i : Fin J, Fin L
def join {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    Finset (Coord J L) := I.sigma u
def flat {J L : ℕ} (u : Fin J → Finset (Fin L)) : Finset (Coord J L) := join univ u
def row {J L : ℕ} (S : Finset (Coord J L)) (i : Fin J) : Finset (Fin L) :=
  Finset.univ.filter fun x => Sigma.mk i x ∈ S
def prefixIndices (J k : ℕ) : Finset (Fin J) := univ.filter fun i => i.val < k
end ThreeSum.BlockRows


