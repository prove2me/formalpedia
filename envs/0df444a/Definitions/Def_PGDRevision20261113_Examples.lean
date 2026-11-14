-- Prove2me | Definitions.Def_PGDRevision20261113_Examples
-- name    : PGDRevision20261113_Examples
-- status  : Definition
-- author  : @Somehow
-- created : 2026-11-13T07:57:15.568722+00:00
-- url     : https://prove2.me/theorems/c0817af8-b745-4387-91b6-3738b907ddc2
-- title:
--   Exact geometry examples, counterexamples and polynomial penalty models
-- statement:
--   This module defines concrete scalar losses, penalties, curvature families, and the precise target propositions for the remaining examples in Sections 4--8. It includes the four interval cases, two real-line polynomial penalties, a smooth bump feature, and a continuous asymmetric curvature with a continuum of optima. For every geometry, the error norm means
--   $$\rho(c,p)=\sup_{t\in I}\left|\frac{pk_c(t)-A(t)}{pk_c(t)+\lambda b(t)}\right|.$$
--   The performance functions and feasibility predicates are the previously published scalar-profile interfaces. The definitions introduce no unproved mathematical facts.
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Sections 4--8 and Appendix B, with exact source references on each associated theorem.

import Definitions.Def_PGDRevision20261113_Contacts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace PGDRevision20261113

def intervalExample (A : ℝ → ℝ) (lam : ℝ) : GeometryData :=
  ⟨.interval 1, A, powerCurvature 1, lam⟩

def ExactGeometryExample (G : GeometryData) (c p r : ℝ) : Prop :=
  AdmissibleGeometry G ∧ UniformGeometryEnvelope G (c, p) r ∧
  geometryRho G c p = ENNReal.ofReal r ∧ GeometryOptimum G (c, p) ∧
  (∀ z, GeometryOptimum G z → z = (c, p)) ∧
  ∀ N : ℕ, 1 ≤ N →
    geometryOmega G (c, p) N = ENNReal.ofReal r ^ (2 * N) ∧
    ∀ z : ℝ × ℝ, FeasiblePair z →
      geometryOmega G (c, p) N ≤ geometryOmega G z N ∧
      (geometryOmega G z N = geometryOmega G (c, p) N → z = (c, p))

def quadraticExample : GeometryData := intervalExample (fun t => 12 - 9 * t ^ 2) 10
def matchedExample : GeometryData := intervalExample (fun t => t ^ 2) 1
def asymmetricQuadraticExample : GeometryData := intervalExample (fun t => 2 + t) 1
def asymmetricInteriorExample : GeometryData :=
  intervalExample (fun t => 9 + 8 * t + 7 * t ^ 2) (20736 / 625)
def asymmetricInteriorScale : ℝ := 768 / (25 * Real.sqrt 10)

def ExactQuadraticExampleClaim : Prop :=
  ExactGeometryExample quadraticExample 0 10 (1 / 10) ∧
  geometryError quadraticExample 0 10 0 = -(1 / 10) ∧
  geometryError quadraticExample 0 10 (Real.sqrt (2 / 3)) = 1 / 10

def ExactMatchedExampleClaim : Prop :=
  ExactGeometryExample matchedExample 1 (1 / 8) (1 / 9) ∧
  geometryError matchedExample 1 (1 / 8) 0 = 1 / 9 ∧
  geometryError matchedExample 1 (1 / 8) (1 / Real.sqrt 2) = -(1 / 9)

def ExactAsymmetricQuadraticExampleClaim : Prop :=
  ExactGeometryExample asymmetricQuadraticExample 0 2 (Real.sqrt 2 / 8) ∧
  geometryError asymmetricQuadraticExample 0 2 (-(1 / Real.sqrt 2)) = Real.sqrt 2 / 8 ∧
  geometryError asymmetricQuadraticExample 0 2 (1 / Real.sqrt 2) = -(Real.sqrt 2 / 8)

def ExactAsymmetricInteriorExampleClaim : Prop :=
  ExactGeometryExample asymmetricInteriorExample (1 / 2) asymmetricInteriorScale (5 / 66) ∧
  geometryError asymmetricInteriorExample (1 / 2) asymmetricInteriorScale (-(3 / 5)) = 5 / 66 ∧
  geometryError asymmetricInteriorExample (1 / 2) asymmetricInteriorScale (3 / 5) = -(5 / 66) ∧
  (∀ t ∈ geometryDomain asymmetricInteriorExample,
    |geometryError asymmetricInteriorExample (1 / 2) asymmetricInteriorScale t| = 5 / 66 ↔
      t = -(3 / 5) ∨ t = 3 / 5) ∧
  ¬ ThreeFeatureContacts asymmetricInteriorExample ((1 / 2), asymmetricInteriorScale) (5 / 66)

def regularityCurvature (x : ℝ) : ℝ :=
  if x ≤ -1 then 0 else if x ≤ 1 then
    (29 + 11 * x + 11 * x ^ 2 + 29 * x ^ 3) / 180 else 4 / 9
def regularityExample : GeometryData :=
  ⟨.realLine, regularityCurvature, (fun x => 1 + x ^ 2), 1⟩
def regularityLoss : ℝ → ℝ := doublePrimitive regularityCurvature

def RegularityCounterexampleClaim : Prop :=
  Continuous regularityCurvature ∧
  (∀ x : ℝ, 0 ≤ regularityCurvature x ∧ regularityCurvature x ≤ 4 / 9) ∧
  ¬ DifferentiableAt ℝ regularityCurvature (-1) ∧
  ¬ DifferentiableAt ℝ regularityCurvature 1 ∧
  ContDiff ℝ 2 regularityLoss ∧ ConvexOn ℝ Set.univ regularityLoss ∧
  (∀ x, deriv (deriv regularityLoss) x = regularityCurvature x) ∧
  (∀ x y : ℝ, |deriv regularityLoss x - deriv regularityLoss y| ≤ (4 / 9) * |x - y|) ∧
  (∀ z : ℝ × ℝ, GeometryOptimum regularityExample z ↔
    0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 = (2 / 9) * Real.rpow 2 (-z.1)) ∧
  (∀ z, GeometryOptimum regularityExample z →
    geometryRho regularityExample z.1 z.2 = ENNReal.ofReal (1 / 10)) ∧
  (∀ c : ℝ, c ∈ Set.Icc 0 1 →
    UniformGeometryEnvelope regularityExample (c, (2 / 9) * Real.rpow 2 (-c)) (1 / 10))

def bumpFeature (x : ℝ) : ℝ := (max (x - 3) 0) ^ 2 * (max (4 - x) 0) ^ 2
def bumpLoss (x : ℝ) : ℝ :=
  (3 / 2) * x ^ 2 + 9 * x * Real.arctan x - (9 / 2) * Real.log (1 + x ^ 2)
def bumpPenalty (x : ℝ) : ℝ := 10 * (x ^ 2 / 2 + x ^ 4 / 12)
def bumpDesign : FeatureData 1 := ⟨bumpLoss, bumpPenalty, fun _ => bumpFeature⟩
def bumpContactFamily : ContactFamily :=
  ⟨Set.univ, (fun x => 3 + 9 / (1 + x ^ 2)), (fun x => 10 * (1 + x ^ 2)),
    (fun theta x => Real.exp (theta * bumpFeature x)), id⟩

def FiniteFeatureNonuniquenessClaim : Prop :=
  AdmissibleFeatures bumpDesign ∧ ContDiff ℝ 1 bumpFeature ∧
  bumpFeature (7 / 2) = 1 / 16 ∧
  (∀ x : ℝ, x ∉ Set.Icc (3 : ℝ) 4 → bumpFeature x = 0) ∧
  (∀ theta : ℝ, theta ≤ 0 →
    ContactOptimum bumpContactFamily Set.univ (theta, 10) ∧
    contactRho bumpContactFamily theta 10 = ENNReal.ofReal (1 / 10)) ∧
  (∀ theta p : ℝ, 0 < p →
    ENNReal.ofReal (1 / 10) ≤ contactRho bumpContactFamily theta p) ∧
  (∀ theta1 theta2 : ℝ, theta1 ≠ theta2 →
    bumpContactFamily.kernel theta1 (7 / 2) ≠ bumpContactFamily.kernel theta2 (7 / 2)) ∧
  (∀ theta : ℝ, theta ≤ 0 → ∀ N : ℕ, 1 ≤ N →
    profileOmega (featureProfile bumpDesign (fun _ => theta)) 10 N =
      ENNReal.ofReal (1 / 10) ^ (2 * N))

def polynomialB1 (x : ℝ) : ℝ := 1 + x ^ 2
def polynomialB2 (x : ℝ) : ℝ := 1 + x ^ 2 + x ^ 3 + x ^ 4
def polynomialPenalty1 (lam x : ℝ) : ℝ := lam * (x ^ 2 / 2 + x ^ 4 / 12)
def polynomialPenalty2 (lam x : ℝ) : ℝ :=
  lam * (x ^ 2 / 2 + x ^ 4 / 12 + x ^ 5 / 20 + x ^ 6 / 30)
def realLineExample (b a : ℝ → ℝ) (lam : ℝ) : GeometryData :=
  ⟨.realLine, (fun x => a (b x)), b, lam⟩

def PolynomialPenaltyModelsClaim : Prop :=
  ∀ lam : ℝ, 0 < lam →
    (∀ x, deriv (deriv (polynomialPenalty1 lam)) x = lam * polynomialB1 x) ∧
    (∀ x, deriv (deriv (polynomialPenalty2 lam)) x = lam * polynomialB2 x) ∧
    (∀ x, 1 ≤ polynomialB1 x ∧ 1 ≤ polynomialB2 x) ∧
    (∀ x, deriv polynomialB2 x = x * (2 + 3 * x + 4 * x ^ 2)) ∧
    (∀ b ∈ ({polynomialB1, polynomialB2} : Set (ℝ → ℝ)),
      AdmissibleGeometry (realLineExample b (fun _ => 1) lam))

def PolynomialQuadraticExamplesClaim : Prop :=
  ∀ b ∈ ({polynomialB1, polynomialB2} : Set (ℝ → ℝ)),
    ExactGeometryExample (realLineExample b (fun s => 3 + 9 / s) 10) 0 10 (1 / 10)

def PolynomialMatchedExamplesClaim : Prop :=
  ∀ b ∈ ({polynomialB1, polynomialB2} : Set (ℝ → ℝ)),
    ExactGeometryExample (realLineExample b (fun s => 1 - 1 / s) 1) 1 (1 / 8) (1 / 9)

def polynomialInteriorLoss (x : ℝ) : ℝ :=
  x ^ 2 - x * Real.arctan x + Real.log (1 + x ^ 2) / 2

def PolynomialInteriorExamplesClaim : Prop :=
  (∀ b ∈ ({polynomialB1, polynomialB2} : Set (ℝ → ℝ)),
    let G := realLineExample b (fun s => 2 - 1 / s) 1
    AdmissibleGeometry G ∧ (∃! z, GeometryOptimum G z) ∧
      ∀ z, GeometryOptimum G z → 0 < z.1 ∧ z.1 < 1) ∧
  (∀ x, deriv (deriv polynomialInteriorLoss) x = 2 - 1 / (1 + x ^ 2)) ∧
  ∀ x, 1 ≤ deriv (deriv polynomialInteriorLoss) x ∧ deriv (deriv polynomialInteriorLoss) x < 2

def AffineLossNonattainmentClaim : Prop :=
  ∀ (family : GeometryFamily) (b : ℝ → ℝ) (lam : ℝ), 0 < lam →
    (match family with
      | .interval beta => 1 ≤ beta ∧ b = powerCurvature beta
      | .realLine => (∀ x : ℝ, 1 ≤ b x) ∧ b 0 = 1) →
    let G : GeometryData := ⟨family, (fun _ => 0), b, lam⟩
    (∀ c p : ℝ, 0 ≤ c → 0 < p → 0 < geometryRho G c p) ∧
    (∀ p : ℝ, 0 < p → geometryRho G 0 p = ENNReal.ofReal (p / (p + lam))) ∧
    (∀ eps : ℝ, 0 < eps → ∃ p > (0 : ℝ), geometryRho G 0 p < ENNReal.ofReal eps) ∧
    ¬ ∃ z, GeometryOptimum G z

def LossMatchedOneStepClaim : Prop :=
  ∀ (P : ScalarProfile) (p : ℝ), AdmissibleProfile P p →
    (∀ t ∈ P.domain, p * deriv P.phi t = deriv P.f t) →
    ∀ (ell : ℝ) (x : ℕ → ℝ), ProfileTrajectory P p ell 1 x →
      objectiveDerivative P ell (x 1) = 0

end PGDRevision20261113


