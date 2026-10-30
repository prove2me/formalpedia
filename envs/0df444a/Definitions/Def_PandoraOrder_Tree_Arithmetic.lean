-- Prove2me | Definitions.Def_PandoraOrder_Tree_Arithmetic
-- name    : PandoraOrder_Tree_Arithmetic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T21:58:26.787832+00:00
-- url     : https://prove2.me/theorems/16b92c40-7627-4636-9d60-722072f8edb4
-- title:
--   Costed exact-real arithmetic and affine tables
-- statement:
--   An exact-real computation returns either failure or a result with counters for elapsed primitive work and allocated cells. Addition, subtraction, multiplication, comparison, guarded nonzero division, scalar reads, list traversal, list construction and control all have explicit charges. A zero denominator fails. No integral, expectation, optimization, root-finding or feasibility oracle is a primitive.
--
--   The implementation uses an allocation arena: allocated input, intermediate, list and control-frame cells remain live until the computation ends. Recursive control frames reserve sixteen cells for registers and pointers. An allocation also costs time, and the cell counter is the peak storage of this arena convention. Thus storage is not a free polynomial certificate placed in an input. The theorems must prove a uniform polynomial bound on the counters.
--
--   A piecewise-affine table consists of sorted rows containing a left endpoint, slope and intercept; the last row extends to infinity. Table evaluation scans the rows and performs scalar arithmetic. Sorted insertion removes repeated knots. These are general computational definitions, separate from the Pandora model.
--
--   Formalization Note: exact real arithmetic is the reading of the source's size measure in $n$ and support size $s$, rather than a bit-complexity or rational-input restriction. Failure is explicit and must be ruled out by the theorem. Arena allocation is a deliberately simple implementation with no garbage collection.
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, §1.1, p. 2; distributional assumptions, p. 6; computational clauses of Theorems 5–7, pp. 8–11; https://arxiv.org/abs/2002.06968v2

import Mathlib

namespace PandoraOrder.Tree

/-- Exact arithmetic with an allocation arena: allocated cells remain live until the
whole run finishes. This deliberately simple implementation charges all allocations;
`cells` is therefore also its peak live storage. Integer/index and list operations
are charged as well as real arithmetic. Recursive control frames reserve 16
arena cells for their scalar registers and pointers; those cells are never reclaimed. No optimization or expectation oracle exists. -/
structure Meter where
  time : ℕ := 0
  cells : ℕ := 0
  deriving Inhabited

abbrev Calc (α : Type) := StateT Meter Option α

def charge (work cells : ℕ) : Calc Unit := fun m =>
  some ((), ⟨m.time + work + cells, m.cells + cells⟩)

def readCell {α : Type} (x : α) : Calc α := do
  charge 1 16
  pure x

def consCell {α : Type} (width : ℕ) (x : α) (xs : List α) : Calc (List α) := do
  charge 1 (width + 1)
  pure (x :: xs)

noncomputable def plus (x y : ℝ) : Calc ℝ := do
  charge 1 1
  pure (x + y)

noncomputable def minus (x y : ℝ) : Calc ℝ := do
  charge 1 1
  pure (x - y)

noncomputable def times (x y : ℝ) : Calc ℝ := do
  charge 1 1
  pure (x * y)

noncomputable def less (x y : ℝ) : Calc Bool := by
  classical
  exact do
    charge 1 1
    pure (decide (x < y))

noncomputable def divide (x y : ℝ) : Calc ℝ := by
  classical
  exact do
    charge 1 1
    if y = 0 then failure else
      charge 1 1
      pure (x / y)

noncomputable def maximum (x y : ℝ) : Calc ℝ := do
  if ← less x y then pure y else pure x

/-- All list traversal and all constructed list spines are counted. -/
def mapCells {α β : Type} (width : ℕ) (f : α → Calc β) : List α → Calc (List β)
  | [] => do charge 1 16; pure []
  | a :: as => do
      charge 1 16
      let b ← f a
      let bs ← mapCells width f as
      consCell width b bs

def foldCells {α β : Type} (f : β → α → Calc β) : β → List α → Calc β
  | b, [] => do charge 1 16; pure b
  | b, a :: as => do charge 1 16; let c ← f b a; foldCells f c as

def finCells (n : ℕ) : Calc (List (Fin n)) := do
  charge (n + 1) (2 * n)
  pure (List.finRange n)

def appendCells {α : Type} (width : ℕ) : List α → List α → Calc (List α)
  | [], ys => do charge 1 16; pure ys
  | x :: xs, ys => do charge 1 16; let zs ← appendCells width xs ys; consCell width x zs

def reverseCells {α : Type} (width : ℕ) (xs : List α) : Calc (List α) :=
  foldCells (fun ys x => consCell width x ys) [] xs

def memberCell {α : Type} [DecidableEq α] (a : α) : List α → Calc Bool
  | [] => do charge 1 16; pure false
  | b :: bs => do
      charge 2 1
      if a = b then pure true else memberCell a bs

/-- Sorted insertion, dropping equal knots. Comparisons include repeated atoms. -/
noncomputable def insertKnot (x : ℝ) : List ℝ → Calc (List ℝ)
  | [] => consCell 1 x []
  | y :: ys => do
      charge 1 16
      if ← less x y then consCell 1 x (y :: ys)
      else if ← less y x then
        let zs ← insertKnot x ys
        consCell 1 y zs
      else pure (y :: ys)

/-- An affine row is active from its left endpoint to the next row's endpoint;
the final row continues to infinity. -/
structure AffineRow where
  left : ℝ
  slope : ℝ
  intercept : ℝ
  deriving Inhabited

abbrev Table := List AffineRow

noncomputable def affineEval (r : AffineRow) (x : ℝ) : Calc ℝ := do
  let m ← readCell r.slope
  let b ← readCell r.intercept
  let y ← times m x
  plus y b

noncomputable def tableEval (rows : Table) (x : ℝ) : Calc ℝ := do
  let row ← foldCells (fun best r => do
    let a ← readCell r.left
    if ← less x a then pure best else pure r) (⟨0, 1, 0⟩ : AffineRow) rows
  affineEval row x

end PandoraOrder.Tree


