-- Prove2me | Definitions.Def_DKFAsymptotics_Densities
-- name    : DKFAsymptotics_Densities
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-15T20:51:19.406484+00:00
-- url     : https://prove2.me/theorems/20e83b40-915a-44ad-a8fb-ba657a1693b4
-- title:
--   Lebesgue densities, Gaussian PDFs, and weak convergence
-- statement:
--   States are real vectors of finite dimension and covariances are real square matrices. The multivariate Gaussian density is the standard determinant-and-quadratic-form expression. Probability density validity requires almost-everywhere nonnegativity, integrability and integral one. A Gaussian PDF additionally has an almost-everywhere representation with a positive-definite covariance. The density measure is obtained from Lebesgue measure by its nonnegative density. The $L^1$ norm and distance are extended nonnegative integrals. Weak convergence is expressed by convergence of integrals of every bounded continuous real function over these density measures. The definitions themselves are total; their probability and Gaussian interpretations use the explicit validity predicates in the theorem hypotheses.
-- source:
--   M. C. Burkhart, D. M. Brandman, B. Franco, L. R. Hochberg and M. T. Harrison, The Discriminative Kalman Filter for Bayesian Filtering with Nonlinear and Nongaussian Observation Models, Neural Computation 32(5), 969–1017 (2020), doi:10.1162/neco_a_01275; https://burkh4rt.github.io/pubs/Burkhart-et-al-2020-Neural-Comput.pdf; Appendix B, p. 1003; Gaussian notation in Section 2, p. 972.

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.PNat.Basic

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics

abbrev State (d : ℕ) := Fin d → ℝ
abbrev Covariance (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev Density (d : ℕ) := State d → ℝ

variable {d : ℕ}

def gaussianPDF (m : State d) (C : Covariance d) (z : State d) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ d * C.det))⁻¹ *
    Real.exp (-((z - m) ⬝ᵥ (C⁻¹ *ᵥ (z - m))) / 2)

def IsPDF (f : Density d) : Prop :=
  (∀ᵐ z ∂volume, 0 ≤ f z) ∧ Integrable f volume ∧ (∫ z, f z ∂volume) = 1

def IsGaussianPDF (f : Density d) : Prop :=
  IsPDF f ∧ ∃ (m : State d) (C : Covariance d), C.PosDef ∧
    f =ᵐ[volume] gaussianPDF m C

def densityMeasure (f : Density d) : Measure (State d) :=
  volume.withDensity (fun z => ENNReal.ofReal (f z))

def l1Norm (f : Density d) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal |f z| ∂volume

def l1Distance (f g : Density d) : ℝ≥0∞ := l1Norm (f - g)

def Weakly (f : ℕ+ → Density d) (P : Measure (State d)) : Prop :=
  ∀ g : BoundedContinuousFunction (State d) ℝ,
    Tendsto (fun n => ∫ z, g z ∂densityMeasure (f n)) atTop (𝓝 (∫ z, g z ∂P))

end DKFAsymptotics


