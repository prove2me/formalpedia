-- Prove2me | Definitions.Def_MazurTransfer_Order13DiamondQuotientConicData
-- name    : MazurTransfer_Order13DiamondQuotientConicData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T16:05:26.382082+00:00
-- url     : https://prove2.me/theorems/bde505c8-dfe2-49fc-bea0-3fd4623580a1
-- title:
--   Literal diamond quotient functions, conic equation and cubic orbit norm
-- statement:
--   Over any field, the original quotientU, quotientV and fiberCubic give invariant/sign-transformed diamond quotient functions, the conic equation, the cubic root identity and the full three-factor orbit norm under the original nonzero denominator and sextic-equation hypotheses. Eight full original types and three data values are checked. Named downstream consumer: Order13ActualDiamondQuotientFunctions, then the actual rational fixed field.
-- source:
--   Unchanged original MazurTheorem conic/quotient declarations and proofs, Apache-2.0, Vas and contributors; formulas from XOneThirteenDescent at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Eight complete types and three data values kernel-compared with the original source.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The displayed quotient functions reuse the formulas in MazurTheorem's
XOneThirteenDescent.lean. Design boundary: identities over arbitrary fields;
named downstream consumer: the actual function-field order-three quotient
and the Picard trace relation required for nineteen-isogeny descent.
Public data boundary: original quotient formulas and their unchanged certificates.
Named downstream consumer: MazurTransfer.Order13ActualConicFunctionParameter,
then the actual cubic fixed-field identification.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism

noncomputable section
namespace MazurTransfer.Order13DiamondQuotientConic
open Order13DiamondSexticSymmetry Order13DiamondSexticIterates
open Order13PellChartCertificate
variable {F : Type*} [Field F]

def quotientU (x : F) : F := (x ^ 3 - 3 * x - 1) / (x * (x + 1))
def quotientV (x y : F) : F := y / (x * (x + 1))
def fiberCubic (u z : F) : F := z ^ 3 - u * z ^ 2 - (u + 3) * z - 1

theorem quotientU_diamond (x : F) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    quotientU (diamondX x) = quotientU x := by
  simp only [quotientU, diamondX]
  field_simp [hx, hx1]
  ring

theorem quotientV_diamond (x y : F) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    quotientV (diamondX x) (diamondY x y) = -quotientV x y := by
  simp only [quotientV, diamondX, diamondY]
  field_simp [hx, hx1]
  ring

theorem quotient_conic (x y : F) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0)
    (hcurve : y ^ 2 = sextic x) :
    quotientV x y ^ 2 = quotientU x ^ 2 + 2 * quotientU x + 5 := by
  simp only [quotientU, quotientV, sextic] at hcurve ⊢
  field_simp [hx, hx1]
  linear_combination hcurve

theorem fiberCubic_quotientU (x : F) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    fiberCubic (quotientU x) x = 0 := by
  simp only [fiberCubic, quotientU]
  field_simp [hx, hx1]
  ring

theorem orbit_norm (x z : F) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    (z - x) * (z - diamondX x) * (z - diamondX (diamondX x)) =
      fiberCubic (quotientU x) z := by
  rw [diamondX_sq x hx hx1]
  simp only [fiberCubic, quotientU, diamondX]
  field_simp [hx, hx1]
  ring

end MazurTransfer.Order13DiamondQuotientConic
#print axioms MazurTransfer.Order13DiamondQuotientConic.quotient_conic
#print axioms MazurTransfer.Order13DiamondQuotientConic.orbit_norm


