-- Prove2me | Definitions.Def_MazurTransfer_Order13CubicNormChartOriginalDataAndCertificates20261018
-- name    : MazurTransfer_Order13CubicNormChartOriginalDataAndCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T19:02:57.467038+00:00
-- url     : https://prove2.me/theorems/6e9ee6f7-61c6-4654-8a29-736d76bd10d4
-- title:
--   Original cubic functions on the two curve charts
-- statement:
--   Retain the six original cubic polynomial and coordinate-function constructors, with their six exact norm-factorization and chart-evaluation certificates over arbitrary commutative rings. All twelve complete original declaration types and all six nonproof values are compared. Named downstream consumers are the ordinary cusp and infinity local-order certificates.
-- source:
--   Original retained MazurTheorem cubic and local-ring modules, Apache-2.0, Vas and contributors. Complete original declaration types and whole nonproof constructor values are compared. This packages existing checked constructors and their proved certificates; it adds no arithmetic assumption or new theorem acceptance credit.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Polynomial coefficients from the literal MazurTheorem order-thirteen curve.
Design boundary: the short cubic norm factorization on both actual charts.
Named downstream consumer: Order13CubicCuspLocalOrders and Order13CubicInfinityLocalOrders, leading to the actual cusp principal divisor and infinity-class norm eigenvalue.
This interface exposes the retained original six constructors and six complete coordinate certificates; it adds no new arithmetic assumption.
-/
import Definitions.Def_MazurTransfer_Order13PellInfinityFactorEvaluations

noncomputable section
universe u
namespace MazurTransfer.Order13CubicNormChartCertificate
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open Order13PellChartCertificate
variable {R : Type u} [CommRing R]

def cubic (x : R) : R := x ^ 3 + x ^ 2 + 2 * x + 1
def reciprocalCubic (z : R) : R := 1 + z + 2 * z ^ 2 + z ^ 3

theorem cubic_norm_identity (x : R) : sextic x - cubic x ^ 2 = -4 * x ^ 3 * (x + 1) := by
  simp only [sextic, cubic]
  ring

theorem reciprocal_cubic_norm_identity (z : R) :
    infinitySextic z - reciprocalCubic z ^ 2 = -4 * z ^ 2 * (1 + z) := by
  simp only [infinitySextic, reciprocalCubic]
  ring

def ordinaryMinus (R : Type u) [CommRing R] : CoordinateRing R :=
  yCoordinate R - cubic (xCoordinate R)
def ordinaryPlus (R : Type u) [CommRing R] : CoordinateRing R :=
  yCoordinate R + cubic (xCoordinate R)
def reciprocalMinus (R : Type u) [CommRing R] : ReciprocalRing R :=
  wCoordinate R - reciprocalCubic (zCoordinate R)
def reciprocalPlus (R : Type u) [CommRing R] : ReciprocalRing R :=
  wCoordinate R + reciprocalCubic (zCoordinate R)

theorem ordinary_product (R : Type u) [CommRing R] :
    ordinaryMinus R * ordinaryPlus R = -4 * xCoordinate R ^ 3 * (xCoordinate R + 1) := by
  have hy := yCoordinate_sq R
  have hy' : yCoordinate R ^ 2 = sextic (xCoordinate R) := by
    simpa only [sexticPolynomial, sextic, map_add, map_mul, map_pow,
      _root_.map_ofNat, _root_.map_one, Polynomial.aeval_X] using hy
  calc
    _ = yCoordinate R ^ 2 - cubic (xCoordinate R) ^ 2 := by dsimp [ordinaryMinus, ordinaryPlus]; ring
    _ = _ := by rw [hy']; exact cubic_norm_identity _

theorem reciprocal_product (R : Type u) [CommRing R] :
    reciprocalMinus R * reciprocalPlus R = -4 * zCoordinate R ^ 2 * (1 + zCoordinate R) := by
  have hw := wCoordinate_sq R
  have hw' : wCoordinate R ^ 2 = infinitySextic (zCoordinate R) := by
    simpa only [reciprocalPolynomial, infinitySextic, map_add, map_mul, map_pow,
      _root_.map_ofNat, _root_.map_one, Polynomial.aeval_X, add_comm, add_left_comm, add_assoc] using hw
  calc
    _ = wCoordinate R ^ 2 - reciprocalCubic (zCoordinate R) ^ 2 := by dsimp [reciprocalMinus, reciprocalPlus]; ring
    _ = _ := by rw [hw']; exact reciprocal_cubic_norm_identity _

theorem reciprocalMinus_evaluation (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1) :
    Order13InfinityEvaluationKernel.evaluation R a ha (reciprocalMinus R) = a - 1 := by
  simp [reciprocalMinus, reciprocalCubic, Order13InfinityEvaluationKernel.evaluation,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_z,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_w]

theorem reciprocalPlus_evaluation (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1) :
    Order13InfinityEvaluationKernel.evaluation R a ha (reciprocalPlus R) = a + 1 := by
  simp [reciprocalPlus, reciprocalCubic, Order13InfinityEvaluationKernel.evaluation,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_z,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_w]

end MazurTransfer.Order13CubicNormChartCertificate
#print axioms MazurTransfer.Order13CubicNormChartCertificate.ordinary_product
#print axioms MazurTransfer.Order13CubicNormChartCertificate.reciprocal_product


