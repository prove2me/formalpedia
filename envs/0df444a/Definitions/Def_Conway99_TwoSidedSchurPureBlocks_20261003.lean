-- Prove2me | Definitions.Def_Conway99_TwoSidedSchurPureBlocks_20261003
-- name    : Conway99_TwoSidedSchurPureBlocks_20261003
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T01:03:30.728213+00:00
-- url     : https://prove2.me/theorems/16b72251-9bce-4ef3-937f-e2f043bf1439
-- title:
--   Pure finite-coordinate two-sided Schur block definitions
-- statement:
--   Defines the two complementary matrices on one finite real K/W/R triple, their common cross matrix, and the squared-norm/action notation. Both PSD facts are explicit hypotheses of the target theorem.
-- source:
--   Local pinned source: adversarial-review-r230/scratchpad/theorem_hunt/cycle_core_residual_theorem/breakthrough_exceptional_two_sided_schur.md, SHA-256 a6aa4d71010e9382cec7fd055f48a3a9907265f13aeb150d4dddd015fe00c18d. Both PSD premises refer to one K/W/R; deriving them from an actual rooted graph remains open.

import Mathlib

set_option autoImplicit false

/-! Pure definitions for one complementary pair of K/W/R blocks. -/

namespace Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

def normSq (x : g → ℝ) : ℝ := ∑ i, x i * x i

def action (L : Matrix g e ℝ) (y : e → ℝ) : g → ℝ :=
  fun i => ∑ j, L i j * y j

section LiteralBlocks

variable {h : Type*} [Fintype h] [DecidableEq g] [DecidableEq h]

/-- The first full block, using one common checkerboard Gram, owner matrix,
and curvature matrix. -/
def firstBlock (K : Matrix (g ⊕ h) (g ⊕ h) ℝ)
    (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ) :
    Matrix ((g ⊕ h) ⊕ h) ((g ⊕ h) ⊕ h) ℝ :=
  Matrix.fromBlocks ((40 : ℝ) • 1 - K) (-W) (-Wᵀ) R

/-- The complementary block from exactly the same `K`, `W`, and `R`. -/
def secondBlock (K : Matrix (g ⊕ h) (g ⊕ h) ℝ)
    (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ) :
    Matrix ((g ⊕ h) ⊕ h) ((g ⊕ h) ⊕ h) ℝ :=
  Matrix.fromBlocks (K - (12 : ℝ) • 1) W Wᵀ ((28 : ℝ) • 1 - R)

/-- The source's single cross matrix `[K_GH,W_GH]`. -/
def goodCross (K : Matrix (g ⊕ h) (g ⊕ h) ℝ)
    (W : Matrix (g ⊕ h) h ℝ) : Matrix g (h ⊕ h) ℝ :=
  Matrix.fromCols (K.submatrix Sum.inl Sum.inr) (W.submatrix Sum.inl id)

end LiteralBlocks

end Conway99Formal.TwoSidedSchur


