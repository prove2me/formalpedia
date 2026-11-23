-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:19.768298+00:00
-- url     : https://prove2.me/theorems/e4fc3615-4607-4cc7-b5f9-d87ae4ac2225
-- title:
--   Division Points
-- statement:
--   Definitions and structural lemmas for Division Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
section Sequence
variable {R : Type*} [CommRing R] [IsDomain R]
end Sequence
section Values
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
noncomputable def psiAt (x y : R) (n : ℤ) : R :=
  (W.ψ n).evalEval x y
end Values
section Algebra
variable {F : Type*} [Field F]
end Algebra
section Points
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
def xOf : W.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x
variable [DecidableEq F]
end Points
section Main
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
def Good (n : ℤ) : Prop :=
  (n • Point.some x₀ y₀ h₀ = 0 ↔ psiAt W x₀ y₀ n = 0) ∧
    (psiAt W x₀ y₀ n ≠ 0 → xOf W (n • Point.some x₀ y₀ h₀) =
      x₀ - psiAt W x₀ y₀ (n + 1) * psiAt W x₀ y₀ (n - 1) / psiAt W x₀ y₀ n ^ 2)
end Main
section Statements
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
end Statements
end GroundTheory.Arith.Abelian


