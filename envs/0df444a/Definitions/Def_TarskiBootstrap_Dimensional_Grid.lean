-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Grid
-- name    : TarskiBootstrap_Dimensional_Grid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:11.1012+00:00
-- url     : https://prove2.me/theorems/30a38228-2211-4a14-b39f-e115675f5205
-- title:
--   Finite grid and block coordinates
-- statement:
--   For positive integers $n,k$, the **grid** $[n]^k$ has coordinates in $[n]=\{0,\ldots,n-1\}$ and the coordinatewise order. A family is a set of actual endomaps, so distinct functions may have the same answer but duplicate labels are absent.
--
--   For a positive integer $t$, block coordinates identify $([n]^k)^t$ with $[n]^{tk}$. The declaration `flattenBlocks` is an explicit order equivalence. Finiteness of families follows from finiteness of the grid; the instance does not assert monotonicity or uniqueness.
--
--   This coordinate interface supports both the original oracle and the chained oracle.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, §2.1, Definition 2.1, PDF/printed p. 6; Definition 3.1, PDF/printed p. 11, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Mathlib

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- The full coordinatewise ordered grid, §2.1, PDF/printed p. 6. -/
abbrev Grid (n k : ℕ+) := Fin (k : ℕ) → Fin (n : ℕ)

/-- A family consists of actual functions, without duplicate labels. -/
noncomputable instance mapFamilyFintype {X : Type*} [Fintype X]
    (F : Set (X → X)) : Fintype F := Fintype.ofFinite F

/-- Block coordinates for the same grid of dimension t*k. -/
abbrev Blocks (n k t : ℕ+) := Fin (t : ℕ) → Grid n k

/-- Explicit flattening of the pointwise block order to the pointwise tk-coordinate order. -/
def flattenBlocks (n k t : ℕ+) : Blocks n k t ≃o (Fin ((t : ℕ) * (k : ℕ)) → Fin (n : ℕ)) where
  toFun x j := x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  invFun y i j := y (finProdFinEquiv (i, j))
  left_inv x := by funext i j; simp
  right_inv y := by
    funext j
    change y (finProdFinEquiv (finProdFinEquiv.symm j)) = y j
    rw [Equiv.apply_symm_apply]
  map_rel_iff' := by
    intro x y
    constructor
    · intro h i j
      have hij := h (finProdFinEquiv (i, j))
      change x (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
        (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 ≤
        y (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
        (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 at hij
      simpa only [Equiv.symm_apply_apply] using hij
    · intro h j
      exact h _ _

end TarskiBootstrap.Dimensional


