-- Prove2me | Definitions.Def_GridHam_Defs
-- name    : GridHam_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:20:13.390467+00:00
-- url     : https://prove2.me/theorems/2cd99cbe-e765-40dc-b47b-207243fa9a4b
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from zzyzek and contributors's pinned Hamiltonian paths in rectangular grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GridHam
abbrev Coord := ℕ × ℕ
def InBounds (width height : ℕ) (v : Coord) : Prop :=
  v.1 < width ∧ v.2 < height
instance : DecidablePred (fun v => InBounds width height v) :=
  fun v => by unfold InBounds; infer_instance
def Adjacent (v w : Coord) : Prop :=
  (v.1 = w.1 ∧ (v.2 + 1 = w.2 ∨ w.2 + 1 = v.2)) ∨
  (v.2 = w.2 ∧ (v.1 + 1 = w.1 ∨ w.1 + 1 = v.1))
instance : DecidableRel Adjacent := fun v w => by unfold Adjacent; infer_instance
def adjacentB (v w : Coord) : Bool := decide (Adjacent v w)
def chainAdjacent : List Coord → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => adjacentB a b && chainAdjacent (b :: rest)
def allCoords (width height : ℕ) : List Coord :=
  (List.range width).flatMap (fun x => (List.range height).map (fun y => (x, y)))
def ValidPath (width height : ℕ) (s t : Coord) (p : List Coord) : Prop :=
  p.length = width * height ∧
  p.head? = some s ∧
  p.getLast? = some t ∧
  p.Nodup ∧
  (∀ v ∈ p, InBounds width height v) ∧
  (∀ v ∈ allCoords width height, v ∈ p) ∧
  chainAdjacent p = true
def HasHamPath (width height : ℕ) (s t : Coord) : Prop :=
  ∃ p, ValidPath width height s t p
instance : DecidablePred (fun p => ValidPath width height s t p) :=
  fun p => by unfold ValidPath; infer_instance
def parity (v : Coord) : ℕ := (v.1 + v.2) % 2
def ColorCompatible (width height : ℕ) (s t : Coord) : Prop :=
  if (width * height) % 2 = 1 then
    parity s = 0 ∧ parity t = 0
  else
    parity s ≠ parity t
instance : DecidablePred (fun p : Coord × Coord => ColorCompatible width height p.1 p.2) :=
  fun p => by unfold ColorCompatible; infer_instance
def IsCorner (width height : ℕ) (v : Coord) : Prop :=
  v = (0, 0) ∨ v = (width - 1, 0) ∨ v = (0, height - 1) ∨ v = (width - 1, height - 1)
instance : DecidablePred (fun v => IsCorner width height v) :=
  fun v => by unfold IsCorner; infer_instance
def ForbiddenCase1 (width height : ℕ) (s t : Coord) : Prop :=
  let isW := width = 1
  let bound := if isW then height else width
  let far : Coord := if isW then (0, bound - 1) else (bound - 1, 0)
  ¬ ((s = (0, 0) ∧ t = far) ∨ (s = far ∧ t = (0, 0)))
instance : DecidablePred (fun p : Coord × Coord => ForbiddenCase1 width height p.1 p.2) :=
  fun p => by unfold ForbiddenCase1; infer_instance
def ForbiddenCase2 (width height : ℕ) (s t : Coord) : Prop :=
  ¬ IsCorner width height s ∧ ¬ IsCorner width height t ∧
  ((width = 2 ∧ s.2 = t.2) ∨ (height = 2 ∧ s.1 = t.1))
def ForbiddenCase3 (width height : ℕ) (s t : Coord) : Prop :=
  let isW := width = 3
  let oppDim := if isW then height else width
  oppDim % 2 = 0 ∧
  parity s ≠ parity t ∧
  ( let c0 := if isW then s.2 else s.1
    let c1 := if isW then t.2 else t.1
    let oppCoord := if isW then s.1 else s.2
    let isGreater := c1 < c0
    let distance := if isGreater then c0 - c1 else c1 - c0
    let distSat := if oppCoord = 1 then distance > 0 else distance > 1
    distSat ∧
    ((isGreater ∧ parity s ≠ 1) ∨ ((¬ isGreater) ∧ parity s ≠ 0)) )
def IsForbidden (width height : ℕ) (s t : Coord) : Prop :=
  if width = 1 ∨ height = 1 then ForbiddenCase1 width height s t
  else if width = 2 ∨ height = 2 then ForbiddenCase2 width height s t
  else if width = 3 ∨ height = 3 then ForbiddenCase3 width height s t
  else False
def IsAcceptable (width height : ℕ) (s t : Coord) : Prop :=
  ColorCompatible width height s t ∧ ¬ IsForbidden width height s t
instance instDecColorCompatible (w h : ℕ) (s t : Coord) :
    Decidable (ColorCompatible w h s t) := by
  unfold ColorCompatible; infer_instance
instance instDecForbiddenCase1 (w h : ℕ) (s t : Coord) :
    Decidable (ForbiddenCase1 w h s t) := by
  unfold ForbiddenCase1; infer_instance
instance instDecForbiddenCase2 (w h : ℕ) (s t : Coord) :
    Decidable (ForbiddenCase2 w h s t) := by
  unfold ForbiddenCase2 IsCorner; infer_instance
instance instDecForbiddenCase3 (w h : ℕ) (s t : Coord) :
    Decidable (ForbiddenCase3 w h s t) := by
  unfold ForbiddenCase3; infer_instance
instance instDecIsForbidden (w h : ℕ) (s t : Coord) :
    Decidable (IsForbidden w h s t) := by
  unfold IsForbidden; infer_instance
instance instDecIsAcceptable (w h : ℕ) (s t : Coord) :
    Decidable (IsAcceptable w h s t) := by
  unfold IsAcceptable; infer_instance
end GridHam


