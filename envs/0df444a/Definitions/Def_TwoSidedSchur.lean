-- Prove2me | Definitions.Def_TwoSidedSchur
-- name    : TwoSidedSchur
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T05:18:49.908087+00:00
-- url     : https://prove2.me/theorems/a6478ba9-50c4-4c55-82ae-8ba94cca3ae2
-- title:
--   Complementary positive-semidefinite block forms
-- statement:
--   For real coordinate spaces and shared matrices L, K, W, and R, the bundle records complementary PSD inequalities in one structure, defines squared norms and the action/pairing of L, and specifies two block matrices evaluated on paired coordinates (x,t·y). The same matrix data enter both block forms.
-- source:
--   Exact original Lean source: formalization/2026-10-03/two-sided-schur/TwoSidedSchur.lean#L13, 15-16, 18-19, 21-30, 150-151, 224-229, 231-235; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 61d8a9ae110b34e6c9ea60c974ec342f79de6b77c383dd7b756583ac0b54a3e8. Canonical generated Definition: Definitions/Def_TwoSidedSchur.lean; generated SHA-256 def978c81cb6edceb17ec27732cef4658340360378024f0d14e00d2c3fc1c3cb; Lab Git revision 2dab4ffd5b7171f28ee48cad872ef5e2203bdd30, path fixtures/generated-project-definitions/Definitions/Def_TwoSidedSchur.lean.

import Mathlib

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

namespace Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

def normSq (x : g → ℝ) : ℝ := ∑ i, x i * x i

def action (L : Matrix g e ℝ) (y : e → ℝ) : g → ℝ :=
  fun i => ∑ j, L i j * y j

def pairing (L : Matrix g e ℝ) (x : g → ℝ) (y : e → ℝ) : ℝ :=
  ∑ i, x i * action L y i

/-- The two complementary PSD block inequalities, evaluated on `(x,t*y)`.
The same `L`, `a`, and `q` occur in both blocks. -/
structure ComplementaryPSD (L : Matrix g e ℝ) where
  a : (g → ℝ) → ℝ
  q : (e → ℝ) → ℝ
  first : ∀ (x : g → ℝ) (y : e → ℝ) (t : ℝ),
    0 ≤ a x + t ^ 2 * q y - 2 * t * pairing L x y
  second : ∀ (x : g → ℝ) (y : e → ℝ) (t : ℝ),
    0 ≤ 28 * normSq x - a x + t ^ 2 * (28 * normSq y - q y) +
      2 * t * pairing L x y



















private def pairVector [DecidableEq e] (j k : e) (t : ℝ) : e → ℝ :=
  fun z => if z = j then t else if z = k then 1 else 0




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
















































































end LiteralBlocks

end Conway99Formal.TwoSidedSchur


