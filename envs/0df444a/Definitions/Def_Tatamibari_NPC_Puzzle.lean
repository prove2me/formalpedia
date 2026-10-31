-- Prove2me | Definitions.Def_Tatamibari_NPC_Puzzle
-- name    : Tatamibari_NPC_Puzzle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:32:46.630948+00:00
-- url     : https://prove2.me/theorems/5cbc2dbd-be0b-420d-8d3a-1d75c9132c8e
-- title:
--   Dense Tatamibari boards and legal solutions
-- statement:
--   A board is a positive-width, positive-height rectangular grid with one entry per cell: empty, square, horizontal, or vertical. A solution is a collection of nonempty grid-aligned rectangles, one per clue. Their cells are disjoint and cover the board, each rectangle contains exactly one clue, square clues have equal side lengths, horizontal clues have strictly greater width, vertical clues have strictly greater height, and no four distinct rectangles share a corner. Boundary edges may be shared. Existence of a solution is the decision predicate; uniqueness is not required.
--
--   Formalization Note: rectangles use half-open intervals of natural cell coordinates, with the vertical coordinate increasing downwards. Raw board and rectangle records have no proof fields; the executable validity and solution tests enforce the requirements. Lists represent finite collections; disjoint nonempty rectangles preclude duplicates. Zero dimensions and incorrect dense-list lengths are rejected.
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 2, Sections 1–3 (definitions and figures)

import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace Tatamibari.NPC

/-- Coordinates are cell indices, with rows increasing downwards. -/
abbrev Cell := Nat × Nat

/-- A half-open, axis-aligned integer rectangle. Nonemptiness is checked separately. -/
structure Rectangle where
  left : Nat
  top : Nat
  right : Nat
  bottom : Nat
  deriving DecidableEq, Repr, Inhabited

def Rectangle.width (r : Rectangle) : Nat := r.right - r.left
def Rectangle.height (r : Rectangle) : Nat := r.bottom - r.top
def Rectangle.nonempty (r : Rectangle) : Bool := r.left < r.right && r.top < r.bottom
def Rectangle.contains (r : Rectangle) (p : Cell) : Bool :=
  r.left ≤ p.1 && p.1 < r.right && r.top ≤ p.2 && p.2 < r.bottom
def Rectangle.corners (r : Rectangle) : List Cell :=
  [(r.left, r.top), (r.right, r.top), (r.left, r.bottom), (r.right, r.bottom)]
def Rectangle.cells (r : Rectangle) : List Cell :=
  (List.range r.height).flatMap fun y =>
    (List.range r.width).map fun x => (r.left + x, r.top + y)
def Rectangle.disjoint (r s : Rectangle) : Bool :=
  r.right ≤ s.left || s.right ≤ r.left || r.bottom ≤ s.top || s.bottom ≤ r.top

inductive Clue where
  | empty | square | horizontal | vertical
  deriving DecidableEq, Repr, Inhabited

def Clue.fits (c : Clue) (r : Rectangle) : Bool :=
  match c with
  | .empty => false
  | .square => r.width == r.height
  | .horizontal => r.height < r.width
  | .vertical => r.width < r.height

/-- Dense row-major cells; validity includes positive dimensions and exact length. -/
structure Board where
  width : Nat
  height : Nat
  entries : List Clue
  deriving DecidableEq, Repr, Inhabited

def Board.valid (b : Board) : Bool :=
  0 < b.width && 0 < b.height && b.entries.length == b.width * b.height
def Board.area (b : Board) : Rectangle := ⟨0, 0, b.width, b.height⟩
def Board.at (b : Board) (p : Cell) : Clue :=
  if b.area.contains p then b.entries.getD (p.2 * b.width + p.1) .empty else .empty
def Board.clues (b : Board) : List Cell :=
  b.area.cells.filter fun p => b.at p != .empty
def Board.cluesIn (b : Board) (r : Rectangle) : List Cell :=
  b.clues.filter r.contains

/-- Cell-disjointness allows shared boundary edges. -/
def pairwiseDisjoint (rs : List Rectangle) : Bool :=
  rs.zipIdx |>.all fun ri =>
    rs.zipIdx |>.all fun sj => ri.2 == sj.2 || ri.1.disjoint sj.1

/-- Counts distinct rectangles, since the solution predicate separately forbids duplicates. -/
def noFourCorners (rs : List Rectangle) : Bool :=
  (rs.flatMap Rectangle.corners).all fun p =>
    (rs.filter fun r => r.corners.contains p).length < 4

def Board.legalRectangle (b : Board) (r : Rectangle) : Bool :=
  r.nonempty && r.right ≤ b.width && r.bottom ≤ b.height &&
  match b.cluesIn r with
  | [p] => (b.at p).fits r
  | _ => false

/-- The complete seven-rule predicate, without gadget, parity, or uniqueness restrictions. -/
def Board.isSolution (b : Board) (rs : List Rectangle) : Bool :=
  b.valid && rs.length == b.clues.length &&
  rs.all b.legalRectangle && pairwiseDisjoint rs &&
  b.area.cells.all (fun p => rs.any (fun r => r.contains p)) && noFourCorners rs

def Board.solvable (b : Board) : Prop := ∃ rs, b.isSolution rs = true

end Tatamibari.NPC


