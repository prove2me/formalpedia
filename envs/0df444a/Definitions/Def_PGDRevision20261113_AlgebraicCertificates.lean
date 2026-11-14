-- Prove2me | Definitions.Def_PGDRevision20261113_AlgebraicCertificates
-- name    : PGDRevision20261113_AlgebraicCertificates
-- status  : Definition
-- author  : @Somehow
-- created : 2026-11-13T08:02:34.355595+00:00
-- url     : https://prove2.me/theorems/f4998572-5204-423d-9a3e-5045af40ad0d
-- title:
--   Exact rational and polynomial envelope certificate data
-- statement:
--   This module defines the rational errors, piecewise-curvature bands, derivative comparison, and the two degree-14 polynomials used by the exact examples. In the asymmetric interior case the envelope data obey the target factorizations
--   $$D[U^2-(1-r)^2V]=16(u-2)^2Q_+(u),\qquad D[(1+r)^2V-L^2]=16(u-2)^2Q_-(u).$$
--   Exact coefficient vectors and Bernstein transformations are included so the obligations are finite and reproducible. The assertions are separate theorem targets.
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Sections 4--8 and Appendix B, with exact source references on each associated theorem.

import Definitions.Def_PGDRevision20261113_Examples

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PGDRevision20261113

def quadraticEnvelopeError (u : ℝ) : ℝ := (9 * u - 2) * (1 - u) / (10 * (2 - u))

def QuadraticEnvelopeIdentitiesClaim : Prop :=
  ∀ u ∈ Set.Icc (0 : ℝ) 1,
    quadraticEnvelopeError u + 1 / 10 = u * (10 - 9 * u) / (10 * (2 - u)) ∧
    1 / 10 - quadraticEnvelopeError u = (3 * u - 2) ^ 2 / (10 * (2 - u)) ∧
    |quadraticEnvelopeError u| ≤ 1 / 10

def AsymmetricQuadraticPolynomialIdentityClaim : Prop :=
  ∀ u : ℝ,
    (3 - 2 * u) ^ 2 - 32 * u * (1 - u) ^ 2 = (1 - 2 * u) ^ 2 * (9 - 8 * u) ∧
    (u ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (3 - 2 * u) ^ 2 - 32 * u * (1 - u) ^ 2)

def RegularityBandIdentitiesClaim : Prop :=
  ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    regularityCurvature x - (1 - x ^ 2) / 10 = (x + 1) * (11 + 29 * x ^ 2) / 180 ∧
    2 * (1 + x ^ 2) / 9 - regularityCurvature x = (1 - x) * (11 + 29 * x ^ 2) / 180 ∧
    (1 - x ^ 2) / 10 ≤ regularityCurvature x ∧ regularityCurvature x ≤ 2 * (1 + x ^ 2) / 9

def TangencyDerivativeIdentityClaim : Prop :=
  ∀ (A B v w : ℝ → ℝ) (x : ℝ),
    DifferentiableAt ℝ A x → DifferentiableAt ℝ B x →
    DifferentiableAt ℝ v x → DifferentiableAt ℝ w x →
    v x + B x ≠ 0 → w x = v x →
      deriv (fun t => (w t - A t) / (w t + B t)) x -
        deriv (fun t => (v t - A t) / (v t + B t)) x =
        (A x + B x) / (v x + B x) ^ 2 * (deriv w x - deriv v x)

def evalDescending (coefficients : List ℝ) (u : ℝ) : ℝ :=
  coefficients.foldl (fun acc coefficient => acc * u + coefficient) 0

def asymPlusCoefficients : List ℝ :=
  [46656,186624,930400,593664,5723604,8612560,16938260,9488400,
   19489705,16190820,19191896,97104,695380,11664,11664]
def asymMinusCoefficients : List ℝ :=
  [-46656,-186624,4244000,20948736,21978796,20251440,16935140,18997200,
   12551095,6477980,2797104,1407696,598220,-11664,-11664]
def asymBernsteinCoefficients : List ℝ :=
  [126930799,510177224,188285428284/91,768381990534/91,34594391124974/1001,
   141462150210424/1001,44256346607248/77,992162426015821/429,
   27478288461840247/3003,5052254731224032/143,10153992612152148/77,
   6106988499516912/13,142665266145360284/91,33276363266470368/7,12312270624196224]
def asymTailCoefficients : List ℝ :=
  [-864,-41472,-841368,-9387360,-62428004,-248596320,-554290792,-556149216,-72103104]
def asymQPlus (u : ℝ) : ℝ := evalDescending asymPlusCoefficients u
def asymQMinus (u : ℝ) : ℝ := evalDescending asymMinusCoefficients u
def asymS (u : ℝ) : ℝ := (u ^ 2 - 1) / (u ^ 2 + 1)
def asymB (u : ℝ) : ℝ := 5184 * (u ^ 2 + 1) ^ 2 / (625 * u ^ 2)
def asymV2 (u : ℝ) : ℝ := 36864 * (u ^ 2 + 1) * (u + 1) ^ 2 / (3125 * u ^ 2)
def asymUpper (u : ℝ) : ℝ := 9 + 7 * asymS u ^ 2 + (5 / 66) * asymB u - 8 * asymS u
def asymLower (u : ℝ) : ℝ := 9 + 7 * asymS u ^ 2 - (5 / 66) * asymB u + 8 * asymS u
def asymDenominator (u : ℝ) : ℝ := 1890625 * u ^ 4 * (u ^ 2 + 1) ^ 4
def asymTransformedCoefficient (i : Fin 15) : ℝ :=
  ∑ k : Fin 15, if i.val ≤ k.val then
    asymMinusCoefficients.reverse.getD k.val 0 * (Nat.choose k.val i.val : ℝ) * (5 : ℝ) ^ i.val else 0

def AsymmetricInteriorFactorizationClaim : Prop :=
  ∀ u : ℝ, 1 ≤ u →
    asymDenominator u * (asymUpper u ^ 2 - (1 - 5 / 66) ^ 2 * asymV2 u) =
      16 * (u - 2) ^ 2 * asymQPlus u ∧
    asymDenominator u * ((1 + 5 / 66) ^ 2 * asymV2 u - asymLower u ^ 2) =
      16 * (u - 2) ^ 2 * asymQMinus u ∧
    0 < asymUpper u ∧ 0 < asymQPlus u ∧
    (u ≤ 6 → 0 < asymQMinus u) ∧ (6 ≤ u → asymLower u < 0) ∧
    (1 - 5 / 66) * Real.sqrt (asymV2 u) ≤ asymUpper u ∧
    asymLower u ≤ (1 + 5 / 66) * Real.sqrt (asymV2 u)

def AsymmetricCoefficientCertificateClaim : Prop :=
  asymPlusCoefficients.length = 15 ∧ asymBernsteinCoefficients.length = 15 ∧
  (∀ j : Fin 15, (11664 : ℝ) ≤ asymPlusCoefficients.getD j.val 0) ∧
  (∃ j : Fin 15, asymPlusCoefficients.getD j.val 0 = 11664) ∧
  (∀ j : Fin 15, (126930799 : ℝ) ≤ asymBernsteinCoefficients.getD j.val 0) ∧
  (∃ j : Fin 15, asymBernsteinCoefficients.getD j.val 0 = 126930799) ∧
  (∀ j : Fin 15, asymBernsteinCoefficients.getD j.val 0 =
    ∑ i : Fin 15, if i.val ≤ j.val then
      (Nat.choose j.val i.val : ℝ) / (Nat.choose 14 i.val : ℝ) * asymTransformedCoefficient i else 0) ∧
  (∀ z : ℝ, asymQMinus (1 + 5 * z) =
    ∑ j : Fin 15, asymBernsteinCoefficients.getD j.val 0 * (Nat.choose 14 j.val : ℝ) *
      z ^ j.val * (1 - z) ^ (14 - j.val)) ∧
  asymTailCoefficients.length = 9 ∧
  (∀ j : Fin 9, asymTailCoefficients.getD j.val 0 ≤ (-864 : ℝ)) ∧
  (∃ j : Fin 9, asymTailCoefficients.getD j.val 0 = -864) ∧
  (∀ z : ℝ, 0 ≤ z → 1375 * (6 + z) ^ 2 * ((6 + z) ^ 2 + 1) ^ 2 * asymLower (6 + z) =
    evalDescending asymTailCoefficients z)

end PGDRevision20261113


