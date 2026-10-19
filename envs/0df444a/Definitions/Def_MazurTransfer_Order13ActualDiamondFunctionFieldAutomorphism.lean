-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism
-- name    : MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:27:53.823034+00:00
-- url     : https://prove2.me/theorems/f64a9cfe-a7fb-467a-b0e5-9a753c8c5208
-- title:
--   The actual rational diamond field automorphism and its inverse
-- statement:
--   The specified coordinate substitution on the existing function field $L$ of the literal order-thirteen curve defines a $\mathbb Q$-algebra automorphism $\sigma:L\simeq L$. Its third iterate satisfies $$\sigma^3(x)=x,\qquad\sigma^3(y)=-y,$$ and its fifth iterate is its two-sided inverse. These original constructors and iterate identities supply the actual curve automorphism and its Picard action.
-- source:
--   Original complete bodies from MazurTheorem Order13ActualDiamondFunctionFieldAutomorphism.lean and its four short original coordinate-iterate helpers, Apache-2.0, Vas and contributors. Seventeen complete original closed types and five data values are kernel-compared. Public imports alone replace project dependencies; original extensionality is a separate Proved theorem. Named downstream consumer: the actual diamond curve isomorphism and re-rigidified Picard action.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the actual rational diamond field automorphism with its
original coordinate iterates, inverse and coefficient algebra action.
Named downstream consumer: the actual curve diamond isomorphism and
re-rigidified Picard scheme endomorphism. -/
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldMap
import Theorems.Thm_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism_fieldMap_ext_xy
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Explicit iterate formulas adapt MazurTheorem XOneThirteenDescent.lean
at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Design boundary: the cube fixes x and negates y on the sextic, over any
field with the two denominators nonzero. Named downstream consumer:
the actual function-field diamond automorphism and its exact order six.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13DiamondSexticIterates
open Order13DiamondSexticSymmetry
variable {F : Type u} [Field F]

theorem diamondX_sq (x : F) (hx : x ≠ 0) (hd : x + 1 ≠ 0) :
    diamondX (diamondX x) = -(x + 1) / x := by
  dsimp [diamondX]
  field_simp [hx, hd] <;> ring

theorem diamondX_cube (x : F) (hx : x ≠ 0) (hd : x + 1 ≠ 0) :
    diamondX (diamondX (diamondX x)) = x := by
  rw [diamondX_sq x hx hd]
  dsimp [diamondX]
  field_simp [hx] <;> ring

theorem diamondY_sq (x y : F) (hx : x ≠ 0) (hd : x + 1 ≠ 0) :
    diamondY (diamondX x) (diamondY x y) = y / x ^ 3 := by
  dsimp [diamondY, diamondX]
  field_simp [hx, hd] <;> ring

theorem diamondY_cube (x y : F) (hx : x ≠ 0) (hd : x + 1 ≠ 0) :
    diamondY (diamondX (diamondX x))
      (diamondY (diamondX x) (diamondY x y)) = -y := by
  rw [diamondX_sq x hx hd, diamondY_sq x y hx hd]
  dsimp [diamondY]
  field_simp [hx] <;> ring

end MazurTransfer.Order13DiamondSexticIterates
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a genuine Q-algebra automorphism of the literal order-13
function field, whose cube fixes x and negates y. Named downstream consumer:
the induced Picard action and the nineteen-isogeny rank-zero descent.
-/

noncomputable section
namespace MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13ActualOrdinaryPolynomialTranscendence Order13ActualDiamondFunctionFieldMap
open Order13DiamondSexticSymmetry Order13DiamondSexticIterates
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩



def diamondSecond : actualCurveFunctionField ℚ →+* actualCurveFunctionField ℚ :=
  diamondFieldMap.comp diamondFieldMap
def diamondThird : actualCurveFunctionField ℚ →+* actualCurveFunctionField ℚ :=
  diamondFieldMap.comp diamondSecond

theorem map_diamondX (f : actualCurveFunctionField ℚ →+* actualCurveFunctionField ℚ)
    (x : actualCurveFunctionField ℚ) : f (diamondX x) = diamondX (f x) := by
  simp only [diamondX, map_div₀, map_neg, map_one, map_add]

theorem map_diamondY (f : actualCurveFunctionField ℚ →+* actualCurveFunctionField ℚ)
    (x y : actualCurveFunctionField ℚ) : f (diamondY x y) = diamondY (f x) (f y) := by
  simp only [diamondY, map_div₀, map_pow, map_add, map_one]

theorem xImage_ne_zero : xImage ℚ ≠ 0 := by
  intro H
  apply xImage_transcendental
  rw [H]
  exact isIntegral_zero.isAlgebraic

theorem diamondThird_x : diamondThird (xImage ℚ) = xImage ℚ := by
  simp only [diamondThird, diamondSecond, RingHom.comp_apply, diamondFieldMap_x, map_diamondX]
  exact diamondX_cube (xImage ℚ) xImage_ne_zero xImage_add_one_ne_zero

theorem diamondThird_y : diamondThird (yImage ℚ) = -yImage ℚ := by
  simp only [diamondThird, diamondSecond, RingHom.comp_apply, diamondFieldMap_y, map_diamondY,
    diamondFieldMap_x, map_diamondX]
  exact diamondY_cube (xImage ℚ) (yImage ℚ) xImage_ne_zero xImage_add_one_ne_zero

theorem diamondThird_square : diamondThird.comp diamondThird = RingHom.id _ := by
  apply fieldMap_ext_xy
  · simp only [RingHom.comp_apply, diamondThird_x, RingHom.id_apply]
  · simp only [RingHom.comp_apply, diamondThird_y, map_neg, neg_neg, RingHom.id_apply]

def diamondInverse : actualCurveFunctionField ℚ →+* actualCurveFunctionField ℚ :=
  diamondSecond.comp diamondThird

theorem diamond_inverse_left : diamondInverse.comp diamondFieldMap = RingHom.id _ := by
  change diamondFieldMap.comp (diamondFieldMap.comp
    (diamondFieldMap.comp (diamondFieldMap.comp (diamondFieldMap.comp diamondFieldMap)))) = _
  exact diamondThird_square

theorem diamond_inverse_right : diamondFieldMap.comp diamondInverse = RingHom.id _ := by
  change diamondFieldMap.comp (diamondFieldMap.comp
    (diamondFieldMap.comp (diamondFieldMap.comp (diamondFieldMap.comp diamondFieldMap)))) = _
  exact diamondThird_square

def diamondRingEquiv : actualCurveFunctionField ℚ ≃+* actualCurveFunctionField ℚ where
  __ := diamondFieldMap
  invFun := diamondInverse
  left_inv b := RingHom.congr_fun diamond_inverse_left b
  right_inv b := RingHom.congr_fun diamond_inverse_right b

def diamondAlgEquiv : actualCurveFunctionField ℚ ≃ₐ[ℚ] actualCurveFunctionField ℚ :=
  AlgEquiv.ofRingEquiv (f := diamondRingEquiv) (fun r => RingHom.congr_fun
    (Subsingleton.elim (diamondFieldMap.comp (algebraMap ℚ (actualCurveFunctionField ℚ)))
      (algebraMap ℚ (actualCurveFunctionField ℚ))) r)

end MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism
#print axioms MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism.fieldMap_ext_xy
#print axioms MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism.diamondThird_square
#print axioms MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv


