-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseCombinationCoordinates
-- name    : MazurTransfer_Order13InverseCombinationCoordinates
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T05:32:18.763251+00:00
-- url     : https://prove2.me/theorems/e54dc6a2-aba3-4acd-ace7-2b8ce2b127b8
-- title:
--   Actual inverse-parameter coordinates and denominator-clearing identities
-- statement:
--   Let $R$ be a commutative ring and write $t=y+x^3+x^2+1$, $p=xt$, and $q=x(p+2)$ in the literal ordinary order-thirteen coordinate algebra. In its localization at $t$, put $s=1/t$, $a=p/t^2$, and $b=q/t^2$. This interface specifies the image of $t$, the ordered generators $1,a,b$, the identity $ts=1$, and the denominator-clearing identities for $a,b$. For a polynomial $F$ with degree at most $N$, it also gives $F^{\mathrm{reflect},N}(t)=F(s)t^N$. These are the coordinates and structural identities used by the inverse polynomial-combination independence theorem and the actual inverse finite-chart basis.
-- source:
--   Six selected original declarations from MazurTheorem Order13InverseParameterPolynomialCombinationIndependence.lean, reassembled using the published canonical primitive scopes. Both data constructor bodies are unchanged. The denominator-clearing proofs explicitly unfold the kernel-equal public alias targets; the independence theorem is omitted and published separately. All six complete original types are checked by closed witnesses, and both data values are compared with their unchanged original bodies using the kernel-equal primitive interfaces. Full native, strict and frontend checks pass. Original headers and Apache-2.0 are retained. Vas and contributors.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original inverse-parameter combination coordinates and structural denominator-clearing identities; the combination independence theorem is separate.
Named downstream consumer: original inverse finite-chart basis and its unchanged polynomial-combination kernel. Original data constructor bodies and full statement types are retained. -/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: independence of the actual inverse parameter combinations
of 1,p/t²,q/t² inside the ordinary t-localization.
Named downstream consumer: the inverse finite algebra's explicit R[S]-basis
and all evaluated-quotient bases for whole single-section FiniteMapData.
-/
import Definitions.Def_MazurTransfer_Order13CanonicalFiniteMapPrimitiveScopes


noncomputable section

universe u
namespace MazurTransfer.Order13InverseParameterPolynomialCombinationIndependence
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open Order13SingleSectionFiniteMapIdentities (t p q)
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
open Order13InverseParameterPolynomialIdentities (s a b)
variable (R : Type u) [CommRing R]

def tImage : ordinaryParameterLocalization R :=
  algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (t R)

theorem tImage_mul_s : tImage R * s R = 1 :=
  IsLocalization.Away.mul_invSelf (t R)

theorem reflected_aeval (F : Polynomial R) (N : ℕ) (hF : F.natDegree ≤ N) :
    aeval (tImage R) (F.reflect N) = aeval (s R) F * tImage R ^ N := by
  let := (Order13InverseParameterFiniteAlgebra.s_isUnit R).invertible
  have hi : ⅟(s R) = tImage R := invOf_eq_left_inv (tImage_mul_s R)
  have h := eval₂_reflect_mul_pow (algebraMap R (ordinaryParameterLocalization R)) (s R) N F hF
  rw [hi] at h
  change aeval (tImage R) (F.reflect N) * s R ^ N = aeval (s R) F at h
  rw [← h, mul_assoc, ← mul_pow, mul_comm (s R), tImage_mul_s, one_pow, mul_one]

def generator : Fin 3 → ordinaryParameterLocalization R :=
  fun i => if i = 0 then 1 else if i = 1 then a R else b R

theorem clear_a (N : ℕ) : a R * tImage R ^ (N + 2) =
    algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (p R) * tImage R ^ N := by
  have ht : (s R * tImage R) ^ 2 = 1 := by
    rw [mul_comm, tImage_mul_s, one_pow]
  dsimp [a, InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterPolynomialIdentities.a]
  rw [pow_add]
  calc
    _ = algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (p R) *
      (s R * tImage R) ^ 2 * tImage R ^ N := by ring
    _ = _ := by rw [ht, mul_one]

theorem clear_b (N : ℕ) : b R * tImage R ^ (N + 2) =
    algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (q R) * tImage R ^ N := by
  have ht : (s R * tImage R) ^ 2 = 1 := by
    rw [mul_comm, tImage_mul_s, one_pow]
  dsimp [b, InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterPolynomialIdentities.b]
  rw [pow_add]
  calc
    _ = algebraMap (CoordinateRing R) (ordinaryParameterLocalization R) (q R) *
      (s R * tImage R) ^ 2 * tImage R ^ N := by ring
    _ = _ := by rw [ht, mul_one]

variable [IsDomain R] [IsNoetherianRing R]



end MazurTransfer.Order13InverseParameterPolynomialCombinationIndependence



#print axioms MazurTransfer.Order13InverseParameterPolynomialCombinationIndependence.reflected_aeval
#print axioms MazurTransfer.Order13InverseParameterPolynomialCombinationIndependence.clear_b


