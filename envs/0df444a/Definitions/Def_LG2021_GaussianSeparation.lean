-- Prove2me | Definitions.Def_LG2021_GaussianSeparation
-- name    : LG2021_GaussianSeparation
-- status  : Definition
-- author  : @sim2000dg
-- created : 2026-11-14T15:07:14.898204+00:00
-- url     : https://prove2.me/theorems/d38b1421-fd49-49b2-bdf7-9d4a48297b72
-- title:
--   Gaussian separation objects
-- statement:
--   Concrete standard Gaussian, normalized Gaussian sphere law, Gaussian surrogate, centered curvature matrix, and explicit radius and Lipschitz parameters for formalized convex-bandit separation.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, Lemma 5 and Appendix E. Separation argument adapted for formalization.

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Gaussian objects for stochastic convex-bandit separation

These concrete Euclidean Gaussian quantities formalize the separation argument
for Lattimore–György (COLT 2021), Sections 4–5 and Appendix E.
The curvature matrix is expressed using the centered Hermite score `x xᵀ - I`.
-/

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def gaussian (d : ℕ) : Measure (Space d) := stdGaussian (Space d)

instance (d : ℕ) : IsProbabilityMeasure (gaussian d) := by
  unfold gaussian
  infer_instance

instance (d : ℕ) : IsGaussian (gaussian d) := by
  unfold gaussian
  infer_instance

def gaussianMean {d : ℕ} (f : Space d → ℝ) : ℝ := ∫ x, f x ∂gaussian d

def surrogate {d : ℕ} (lambda : ℝ) (f : Space d → ℝ) (z : Space d) : ℝ :=
  gaussianMean f +
    ((∫ x, f ((1 - lambda) • x + lambda • z) ∂gaussian d) - gaussianMean f) / lambda

/-- The uniform sphere law, represented concretely by normalizing a standard Gaussian.
The origin is mapped to zero; in positive dimension this exceptional input has Gaussian mass zero.
-/
def sphereMeasure (d : ℕ) (R : ℝ) : Measure (Space d) :=
  (gaussian d).map (fun x => (R / ‖x‖) • x)

/-- The isotropic Gaussian Lebesgue density with standard deviation `s > 0`. -/
def gaussianDensity {d : ℕ} (s : ℝ) (x : Space d) : ℝ :=
  ((Real.sqrt (2 * Real.pi) * s)⁻¹) ^ d * Real.exp (-‖x‖ ^ 2 / (2 * s ^ 2))

/-- The Hermite-score curvature matrix `E[(XXᵀ - I) f(X)]`. -/
def curvatureMatrix {d : ℕ} (f : Space d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ x, (x i * x j - if i = j then 1 else 0) * f x ∂gaussian d

def quadraticForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (z : Space d) : ℝ :=
  ∑ i, ∑ j, z i * M i j * z j

def gaussianGap {d : ℕ} (r : ℝ) (f : Space d → ℝ) : ℝ :=
  gaussianMean f - sInf (f '' Metric.closedBall (0 : Space d) r)

def paperRadius (d : ℕ) (L : ℝ) : ℝ := 10 ^ 5 * (d : ℝ) ^ 2 * Real.sqrt (2 * L)

def paperLambda (d : ℕ) (L : ℝ) : ℝ := 1 / (4 * 10 ^ 5 * (d : ℝ) * L)

def paperLipschitz (d : ℕ) (D L : ℝ) : ℝ := (d : ℝ) * D / paperRadius d L

end LG2021


