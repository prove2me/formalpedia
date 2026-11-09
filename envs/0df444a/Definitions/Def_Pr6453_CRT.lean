-- Prove2me | Definitions.Def_Pr6453_CRT
-- name    : Pr6453_CRT
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T22:25:07.967829+00:00
-- url     : https://prove2.me/theorems/4fc9ce48-31d9-4666-be56-af439a27cd86
-- title:
--   PR #6453: multiplication by a fixed vector on a product of fields
-- statement:
--   Multiplication by a fixed vector on a product of fields.
--
--   `mulLin x` is the map `y ↦ x * y` on `ι → K`, as a `K`-linear map. This is the shape a word's action takes once its rows are indexed by CRT coordinates: the product ring `∏_i K` is the CRT image of a ring modulo a product of coprime moduli, and there multiplication is coordinatewise, i.e. multiplication by the coordinate vector of one factor.
--
--   The accompanying theorems show that in this basis the matrix of multiplication by `x` is the diagonal matrix of `x`, that composing two such multiplications gives the diagonal matrix of the product, and that the CRT isomorphism `ZMod (m*n) ≃+* ZMod m × ZMod n` carries products to products.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, RESULT.json (module block: the identity L S A B Idle S^-1 C R = D_A D_B (U(q) plus q plus q^-1), six fields, four Gaussian characters).

/-
PR #6453: multiplication by a fixed vector, on a product of fields.
-/
import Mathlib

set_option autoImplicit false

namespace CRTBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K]

/-- Multiplication by a fixed vector `x`, as a `K`-linear map on the product ring `ι → K` — the
shape a word's action takes once its rows are indexed by the CRT coordinates. -/
def mulLin (x : ι → K) : (ι → K) →ₗ[K] (ι → K) where
  toFun y := x * y
  map_add' y z := by funext i; simp [mul_add]
  map_smul' c y := by
    funext i
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem mulLin_apply (x y : ι → K) : mulLin x y = x * y := rfl

end CRTBasis


