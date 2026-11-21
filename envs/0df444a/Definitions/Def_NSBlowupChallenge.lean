-- Prove2me | Definitions.Def_NSBlowupChallenge
-- name    : NSBlowupChallenge
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T18:48:27.801286+00:00
-- url     : https://prove2.me/theorems/fd345d52-3308-4e5f-be57-f344934faec6
-- title:
--   Navier–Stokes blow-up: space, smooth solutions, profiles (Challenge layer)
-- statement:
--   Definitions for the formalization of Alpöge–Buckmaster Theorem 1.1: the Euclidean space `Space = EuclideanSpace ℝ (Fin 3)`, divergence, Laplacian, pressure gradient and advection; the predicate `IsSmoothSolution` of a smooth solution of the incompressible Navier–Stokes equations with viscosity ν; the breakdown predicates `BreakdownOnSpace` and `BreakdownOnTorus`; the self-similar residual and the existence predicates `PeriodicSimilarityProfileExists` (smooth profile) and `WeakPeriodicSimilarityProfileExists` (weak profile), with weak-gradient and test-field notions. Transcribed verbatim from `lean/Challenge.lean` (definitions only).
-- source:
--   Alpöge–Buckmaster, Finite-time blow-up for the Navier–Stokes equations (20 Nov 2026), https://github.com/tristanbuckmaster/navier-stokes, lean/Challenge.lean (definitions).

import Mathlib

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

abbrev Space := EuclideanSpace ℝ (Fin 3)

def unitVector (i : Fin 3) : Space := EuclideanSpace.single i 1

def divergenceAt (v : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ v x (unitVector i)) i

def sumSecondPartialsAt (v : Space → Space) (x : Space) : Space :=
  ∑ i : Fin 3, iteratedFDeriv ℝ 2 v x ![unitVector i, unitVector i]

def gradientAt (p : Space → ℝ) (x : Space) : Space :=
  ∑ i : Fin 3, fderiv ℝ p x (unitVector i) • unitVector i

def advectionAt (v : Space → Space) (x : Space) : Space :=
  fderiv ℝ v x (v x)

structure IsSmoothSolution (ν : ℝ) (u₀ : Space → Space)
    (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) : Prop where
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Set.Ici 0 ×ˢ Set.univ)
  smooth_pressure : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (Set.Ici 0 ×ˢ Set.univ)
  initial : ∀ x, u 0 x = u₀ x
  momentum : ∀ t > 0, ∀ x,
    deriv (fun τ => u τ x) t + advectionAt (u t) x = ν • sumSecondPartialsAt (u t) x - gradientAt (p t) x
  incompressible : ∀ t > 0, ∀ x, divergenceAt (u t) x = 0

def BreakdownOnSpace : Prop :=
  ∀ ν > 0, ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
    (∀ x, divergenceAt u₀ x = 0) ∧
    ¬ ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ), IsSmoothSolution ν u₀ u p ∧
      ∃ C : ℝ, ∀ t ≥ 0, ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) ≤ ENNReal.ofReal C

def BreakdownOnTorus : Prop :=
  ∀ ν > 0, ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧
    (∀ i x, u₀ (x + unitVector i) = u₀ x) ∧ (∀ x, divergenceAt u₀ x = 0) ∧
    ¬ ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ), IsSmoothSolution ν u₀ u p ∧
      ∀ t ≥ 0, ∀ i x, u t (x + unitVector i) = u t x

def SimilarityResidual (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (s : ℝ) (y : Space) : Space :=
  deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y + (1 / 2 : ℝ) • fderiv ℝ (W s) y y
    - sumSecondPartialsAt (W s) y + advectionAt (W s) y + gradientAt (q s) y

def PeriodicSimilarityProfileExists : Prop :=
  ∃ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (C : ℝ),
    0 < P ∧
    ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2) ∧
    ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) ∧
    (∀ s y, SimilarityResidual W q s y = 0) ∧
    (∀ s y, divergenceAt (W s) y = 0) ∧
    (∀ s y, W (s + P) y = R (W s (R.symm y))) ∧
    (∃ s y, W s y ≠ 0) ∧
    (∀ s y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W s) y‖ ≤ C / (1 + ‖y‖) ^ (j + 1)) ∧
    (∀ s y, ‖fderiv ℝ (q s) y‖ ≤ C / (1 + ‖y‖) ^ 3)

def IsTestFunction (φ : Space → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

def IsWeakGradient (f : Space → Space) (g : Space → (Space →L[ℝ] Space)) : Prop :=
  LocallyIntegrable f ∧ LocallyIntegrable g ∧
    ∀ φ, IsTestFunction φ → ∀ i : Fin 3,
      ∫ y, φ y • g y (unitVector i) = -∫ y, fderiv ℝ φ y (unitVector i) • f y

def IsSpaceTimeTestField (φ : ℝ → Space → Space) : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2) ∧
    HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2) ∧ ∀ s y, divergenceAt (φ s) y = 0

def weakSimilarityIntegrand (W : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  -inner ℝ (W z.1 z.2) (deriv (fun σ => φ σ z.2) z.1)
    - inner ℝ (W z.1 z.2) (φ z.1 z.2)
    - (1 / 2 : ℝ) * inner ℝ (W z.1 z.2) (fderiv ℝ (φ z.1) z.2 z.2)
    + ∑ i : Fin 3, inner ℝ (G z.1 z.2 (unitVector i)) (fderiv ℝ (φ z.1) z.2 (unitVector i))
    - ∑ i : Fin 3, (W z.1 z.2) i * inner ℝ (W z.1 z.2) (fderiv ℝ (φ z.1) z.2 (unitVector i))

def WeakPeriodicSimilarityProfileExists : Prop :=
  ∃ (W : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (C : ℝ),
    0 < P ∧
    AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume ∧
    (∀ s y, W (s + P) y = R (W s (R.symm y))) ∧
    (∀ s, IsWeakGradient (W s) (G s)) ∧
    (∀ᵐ s, ∀ j : Fin 3, IsWeakGradient (fun y => G s y (unitVector j))
      (fun y => (H s y).flip (unitVector j))) ∧
    (∀ s, ∀ᵐ y, ∑ i : Fin 3, (G s y (unitVector i)) i = 0) ∧
    (∀ s, ∫⁻ y, ENNReal.ofReal (‖W s y‖ ^ 6) ≤ ENNReal.ofReal C) ∧
    (∀ s, ∫⁻ y, ENNReal.ofReal (‖G s y‖ ^ 2) ≤ ENNReal.ofReal C) ∧
    (∫⁻ s in Set.Icc 0 P, ∫⁻ y, ENNReal.ofReal (‖H s y‖ ^ 2)) < ⊤ ∧
    (∀ φ, IsSpaceTimeTestField φ →
      Integrable (weakSimilarityIntegrand W G φ) ∧ ∫ z, weakSimilarityIntegrand W G φ z = 0) ∧
    ¬ (∀ᵐ z : ℝ × Space, W z.1 z.2 = 0)

end Breakdown


