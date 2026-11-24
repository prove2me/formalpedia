-- Prove2me | Definitions.Def_GaussianPerimeter_ExpBounds
-- name    : GaussianPerimeter_ExpBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:05:58.405794+00:00
-- url     : https://prove2.me/theorems/b29235ce-4a97-48a1-837f-fdd7e94ef4ea
-- title:
--   Exp Bounds
-- statement:
--   Definitions and structural lemmas for Exp Bounds, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/ExpBounds.lean

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GaussianPerimeter
namespace ExpBounds
def scale : ℚ := 1000000000000
def roundDown (x : ℚ) : ℚ := ⌊x * scale⌋ / scale
def roundUp (x : ℚ) : ℚ := ⌈x * scale⌉ / scale
def lowerSquares : ℕ → ℚ → ℚ
  | 0, x => max 0 x
  | n + 1, x => roundDown ((lowerSquares n x) ^ 2)
def upperSquares : ℕ → ℚ → ℚ
  | 0, x => x
  | n + 1, x => roundUp ((upperSquares n x) ^ 2)
def intScale : ℤ := 1000000000000
def scaledInt (r : ℤ) : ℚ := (r : ℚ) / intScale
def roundedStep (x : ℚ) (k : ℕ) (r : ℤ) : ℤ :=
  intScale + x.num * r / ((x.den : ℤ) * k)
def roundedHorner (x : ℚ) : ℕ → ℤ → ℤ
  | 0, r => r
  | n + 1, r => roundedHorner x n (roundedStep x (n + 1) r)
def roundedLowerSquares : ℕ → ℤ → ℤ
  | 0, r => max 0 r
  | n + 1, r =>
    let z := roundedLowerSquares n r
    z * z / intScale
def roundedUpperSquares : ℕ → ℤ → ℤ
  | 0, r => r
  | n + 1, r =>
    let z := roundedUpperSquares n r
    Int.neg (Int.neg (z * z) / intScale)
end ExpBounds
open ExpBounds
def expLower (x : ℚ) : ℚ :=
  if |x| ≤ 32 then
    scaledInt (roundedLowerSquares 5 (roundedHorner (x / 32) 16 0 - 17))
  else 0
def expUpper (x : ℚ) : ℚ :=
  scaledInt (roundedUpperSquares 5 (roundedHorner (x / 32) 16 0 + 17))
end GaussianPerimeter


