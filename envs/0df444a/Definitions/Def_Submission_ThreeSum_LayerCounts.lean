-- Prove2me | Definitions.Def_Submission_ThreeSum_LayerCounts
-- name    : Submission_ThreeSum_LayerCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:27.612933+00:00
-- url     : https://prove2.me/theorems/5173410d-cfdf-4d81-bad8-b619b4438564
-- title:
--   Layer Counts
-- statement:
--   Definitions and structural lemmas for Layer Counts, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace ThreeSum.LayerCounts
open Finset
def vertices (L h : ℕ) : Finset (Finset (Fin L)) :=
  Finset.univ.powersetCard h
def edgeSet (L h : ℕ) : Finset (Finset (Fin L) × Finset (Fin L)) :=
  (vertices L h ×ˢ vertices L h).filter (fun p => Disjoint p.1 p.2)
end ThreeSum.LayerCounts


