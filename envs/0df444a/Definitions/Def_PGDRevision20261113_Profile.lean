-- Prove2me | Definitions.Def_PGDRevision20261113_Profile
-- name    : PGDRevision20261113_Profile
-- status  : Definition
-- author  : @Somehow
-- created : 2026-11-13T06:20:42.815782+00:00
-- url     : https://prove2.me/theorems/cad9bf05-f204-41e8-af6c-7da23fd54966
-- title:
--   Scalar profiles, implicit updates and exact relative-gradient performance
-- statement:
--   This module specifies twice differentiable scalar loss, penalty and generator functions on an open interval. It uses their actual derivatives, the implicit update equation, a free linear tilt, and nonzero initial objective derivative. Both the curvature-error norm and realized performance use extended nonnegative suprema, including the unbounded case.
--   It also specifies separable profiles, positive exponential feature geometries, and the two algebraic error bands. Named claim predicates describe targets; no mathematical claim is assumed as an axiom.
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Section 4, Theorem 4.1, Corollary 4.2, Proposition 4.3, pages 10-11.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.ENNReal.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace PGDRevision20261113

structure ScalarProfile where
  domain : Set ℝ
  f : ℝ → ℝ
  g : ℝ → ℝ
  phi : ℝ → ℝ

def lossCurvature (P : ScalarProfile) (t : ℝ) : ℝ := deriv (deriv P.f) t
def penaltyCurvature (P : ScalarProfile) (t : ℝ) : ℝ := deriv (deriv P.g) t
def generatorCurvature (P : ScalarProfile) (t : ℝ) : ℝ := deriv (deriv P.phi) t

def AdmissibleProfile (P : ScalarProfile) (p : ℝ) : Prop :=
  P.domain.Nonempty ∧ IsOpen P.domain ∧ Set.OrdConnected P.domain ∧
  ContDiffOn ℝ 2 P.f P.domain ∧ ContDiffOn ℝ 2 P.g P.domain ∧
  ContDiffOn ℝ 2 P.phi P.domain ∧ 0 < p ∧
  (∀ t ∈ P.domain, 0 ≤ lossCurvature P t ∧ 0 ≤ penaltyCurvature P t ∧
    0 < lossCurvature P t + penaltyCurvature P t ∧ 0 < generatorCurvature P t) ∧
  Set.SurjOn (fun t => p * deriv P.phi t + deriv P.g t) P.domain Set.univ

def objective (P : ScalarProfile) (ell t : ℝ) : ℝ := P.f t + P.g t + ell * t
def objectiveDerivative (P : ScalarProfile) (ell t : ℝ) : ℝ :=
  deriv (objective P ell) t

def ProfileTrajectory (P : ScalarProfile) (p ell : ℝ) (N : ℕ) (x : ℕ → ℝ) : Prop :=
  (∀ i ≤ N, x i ∈ P.domain) ∧
  ∀ i < N, p * deriv P.phi (x (i + 1)) + deriv P.g (x (i + 1)) =
    p * deriv P.phi (x i) - deriv P.f (x i) - ell

def profileError (P : ScalarProfile) (p t : ℝ) : ℝ :=
  (p * generatorCurvature P t - lossCurvature P t) /
    (p * generatorCurvature P t + penaltyCurvature P t)

def profileRho (P : ScalarProfile) (p : ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ P.domain, ENNReal.ofReal |profileError P p t|

def profilePerformanceSet (P : ScalarProfile) (p : ℝ) (N : ℕ) : Set ℝ≥0∞ :=
  {r | ∃ (ell : ℝ) (x : ℕ → ℝ), ProfileTrajectory P p ell N x ∧
    objectiveDerivative P ell (x 0) ≠ 0 ∧
    r = ENNReal.ofReal
      (|objectiveDerivative P ell (x N)| ^ 2 /
        |objectiveDerivative P ell (x 0)| ^ 2)}

def profileOmega (P : ScalarProfile) (p : ℝ) (N : ℕ) : ℝ≥0∞ :=
  sSup (profilePerformanceSet P p N)

def ExactProfileReductionClaim : Prop :=
  ∀ (P : ScalarProfile) (p : ℝ), AdmissibleProfile P p →
    ∀ N : ℕ, 1 ≤ N → profileOmega P p N = profileRho P p ^ (2 * N)

def separableGradientSquared {d : ℕ} (P : Fin d → ScalarProfile)
    (ell x : Fin d → ℝ) : ℝ :=
  ∑ j, |objectiveDerivative (P j) (ell j) (x j)| ^ 2

def SeparableTrajectory {d : ℕ} (P : Fin d → ScalarProfile) (p : ℝ)
    (ell : Fin d → ℝ) (N : ℕ) (x : ℕ → Fin d → ℝ) : Prop :=
  ∀ j, ProfileTrajectory (P j) p (ell j) N (fun i => x i j)

def separablePerformanceSet {d : ℕ} (P : Fin d → ScalarProfile)
    (p : ℝ) (N : ℕ) : Set ℝ≥0∞ :=
  {r | ∃ (ell : Fin d → ℝ) (x : ℕ → Fin d → ℝ),
    SeparableTrajectory P p ell N x ∧ separableGradientSquared P ell (x 0) ≠ 0 ∧
    r = ENNReal.ofReal
      (separableGradientSquared P ell (x N) / separableGradientSquared P ell (x 0))}

def SeparableProfilesClaim : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (P : Fin d → ScalarProfile) (p : ℝ),
    (∀ j, AdmissibleProfile (P j) p) → ∀ N : ℕ, 1 ≤ N →
      sSup (separablePerformanceSet P p N) = ⨆ j, profileRho (P j) p ^ (2 * N)

def lowerBand (A B R : ℝ) : ℝ := (A - R * B) / (1 + R)
def upperBand (A B R : ℝ) : ℝ := (A + R * B) / (1 - R)

def ErrorBandEquivalenceClaim : Prop :=
  ∀ A B v R : ℝ, 0 ≤ A → 0 < B → 0 < v → 0 < R → R < 1 →
    (|(v - A) / (v + B)| ≤ R ↔ lowerBand A B R ≤ v ∧ v ≤ upperBand A B R)

def primitive (a : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, a t
def doublePrimitive (a : ℝ → ℝ) : ℝ → ℝ := primitive (primitive a)

structure FeatureData (d : ℕ) where
  f : ℝ → ℝ
  g : ℝ → ℝ
  feature : Fin d → ℝ → ℝ

def featureCurvature {d : ℕ} (D : FeatureData d) (theta : Fin d → ℝ) (x : ℝ) : ℝ :=
  Real.exp (∑ j, theta j * D.feature j x)

def featureProfile {d : ℕ} (D : FeatureData d) (theta : Fin d → ℝ) : ScalarProfile :=
  ⟨Set.univ, D.f, D.g, doublePrimitive (featureCurvature D theta)⟩

def AdmissibleFeatures {d : ℕ} (D : FeatureData d) : Prop :=
  ContDiff ℝ 2 D.f ∧ ContDiff ℝ 2 D.g ∧
  (∀ x : ℝ, 0 ≤ deriv (deriv D.f) x) ∧
  BddAbove (Set.range (deriv (deriv D.f))) ∧
  (∃ lambda > (0 : ℝ), ∀ x, lambda ≤ deriv (deriv D.g) x) ∧
  ∀ j, ContDiff ℝ 1 (D.feature j) ∧ D.feature j 0 = 0

def FeatureBands {d : ℕ} (D : FeatureData d) (z : ℝ × (Fin d → ℝ)) (R : ℝ) : Prop :=
  ∀ t : ℝ,
    z.1 + ∑ j, z.2 j * D.feature j t ≤
      Real.log (upperBand (deriv (deriv D.f) t) (deriv (deriv D.g) t) R) ∧
    (R * deriv (deriv D.g) t < deriv (deriv D.f) t →
      Real.log (lowerBand (deriv (deriv D.f) t) (deriv (deriv D.g) t) R) ≤
        z.1 + ∑ j, z.2 j * D.feature j t)

def featureSublevel {d : ℕ} (D : FeatureData d) (R : ℝ) : Set (ℝ × (Fin d → ℝ)) :=
  {z | profileRho (featureProfile D z.2) (Real.exp z.1) ≤ ENNReal.ofReal R}

def FiniteFeatureDesignClaim : Prop :=
  ∀ (d : ℕ) (D : FeatureData d), AdmissibleFeatures D →
    (∀ (theta : Fin d → ℝ) (u : ℝ),
      AdmissibleProfile (featureProfile D theta) (Real.exp u)) ∧
    ∀ R : ℝ, 0 < R → R < 1 →
      (∀ z, z ∈ featureSublevel D R ↔ FeatureBands D z R) ∧
      Convex ℝ (featureSublevel D R)

end PGDRevision20261113


