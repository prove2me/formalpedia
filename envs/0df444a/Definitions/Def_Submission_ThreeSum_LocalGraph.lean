-- Prove2me | Definitions.Def_Submission_ThreeSum_LocalGraph
-- name    : Submission_ThreeSum_LocalGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:04:47.542686+00:00
-- url     : https://prove2.me/theorems/c2492daf-966e-43aa-bd3f-7da9b0a35d47
-- title:
--   Local Graph
-- statement:
--   Definitions and structural lemmas for Local Graph, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
def leftWord (s : Finset α) : α → Bool := fun i => decide (i ∈ s)
def rightWord (v : Finset α) : α → Bool := fun i => decide (i ∉ v)
section ConcreteGraph
open LayerCounts
abbrev Edge (L h : ℕ) := {p // p ∈ edgeSet L h}
variable {L h : ℕ}
def left (e : Edge L h) : Fin L → Bool := leftWord e.val.1
def right (e : Edge L h) : Fin L → Bool := rightWord e.val.2
def output (e : Edge L h) : Finset (Fin L) := e.val.1 ∪ e.val.2
def equalityMask (e : Edge L h) : Fin L → Bool := fun i => left e i == right e i
def leftVertices (L h : ℕ) : Finset (Fin L → Bool) :=
  (vertices L h).image leftWord
def rightVertices (L h : ℕ) : Finset (Fin L → Bool) :=
  (vertices L h).image rightWord
end ConcreteGraph
end ThreeSum.LocalGraph


