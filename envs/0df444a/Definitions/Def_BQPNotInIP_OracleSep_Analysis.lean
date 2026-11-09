-- Prove2me | Definitions.Def_BQPNotInIP_OracleSep_Analysis
-- name    : BQPNotInIP_OracleSep_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:45:45.08419+00:00
-- url     : https://prove2.me/theorems/1ffd49fe-7bf0-49f4-a8c5-b6d4b69727c0
-- title:
--   Coordinate derivatives, Gaussian laws, and smoothed signs
-- statement:
--   For $F:\mathbb R^m\to\mathbb R$, define the two entrywise norms by
--   $$
--   \|\nabla F(x)\|_1=\sum_i|\partial_i F(x)|,
--   \qquad
--   \|\nabla^2F(x)\|_1=\sum_{i,j}|\partial_{ij}F(x)|.
--   $$
--   The derivatives are Fréchet derivatives evaluated on coordinate unit vectors. The cube is the set of vectors with $|x_i|\le1$ in every coordinate. Sign rounding applies the real sign function coordinatewise.
--
--   Write $\Phi$ for the standard Gaussian CDF. The scalar and vector smoothings are computed as
--   $$
--   h_{a,\delta,i}(t)=2\Phi\!\left(\frac{a_i+\sqrt{1-\delta^2}\,t}{\delta}\right)-1,
--   \qquad
--   h_{a,\delta}(x)_i=h_{a,\delta,i}(x_i).
--   $$
--   They are defined by the CDF, independently of any expectation identity. Centered Gaussian laws are Mathlib’s multivariate Gaussians transported to ordinary real coordinates; pairs use product measures to encode independence. The interpolation is $G(t)=\sqrt t Z+\sqrt{1-t}D$. A final helper abbreviates the printed comparison error $400L\delta\sqrt{\ln(2m)}+\beta K/(4\delta^2)+4/m^{48}$. These definitions supply a common analytic interface for the proof chain.
--
--   Differences from the source:
--   - encoding: real vectors, smooth functions, Gaussian expectations and suprema of derivative norms → coordinates indexed by Fin m, C∞ expressed as ContDiff ℝ (⊤ : ℕ∞), entrywise sums of coordinate derivatives, and pointwise bounds on the stated domains; reason: these are the same finite-dimensional objects and avoid default-valued real suprema
--   - encoding: independent centered Gaussian vectors with the stated covariances → the product of their canonical Gaussian laws, with positive-semidefinite covariance explicitly required; reason: expectations depend only on these laws; positive semidefiniteness is implied by being a covariance, and singular covariances remain allowed
--   - encoding: Gaussian sign rounding → Real.sign, with sign zero equal to zero; reason: every rounded coordinate has positive variance, so zero has probability zero
-- source:
--   Adam Bouland, Andrew Huang, Anand Natarajan, Itay Shalit, Avishay Tal, BQP ⊆ IP Does Not Relativize, STOC 2027 submission #156 (October 2026), §4 and §6.2, PDF p. 16 (printed p. 14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/156.pdf#page=16

import Mathlib

set_option autoImplicit false

namespace BQPNotInIP.OracleSep

open MeasureTheory ProbabilityTheory
open scoped BigOperators
abbrev RVec (m : ℕ) := Fin m → ℝ

def cube (m : ℕ) : Set (RVec m) := {x | ∀ i, |x i| ≤ 1}

noncomputable def coordDeriv {m : ℕ} (F : RVec m → ℝ) (i : Fin m) (x : RVec m) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

noncomputable def partial₂ {m : ℕ} (F : RVec m → ℝ) (i j : Fin m) (x : RVec m) : ℝ :=
  coordDeriv (coordDeriv F j) i x

noncomputable def gradientL1 {m : ℕ} (F : RVec m → ℝ) (x : RVec m) : ℝ :=
  ∑ i, |coordDeriv F i x|

noncomputable def hessianL1 {m : ℕ} (F : RVec m → ℝ) (x : RVec m) : ℝ :=
  ∑ i, ∑ j, |partial₂ F i j x|

noncomputable def signs {m : ℕ} (x : RVec m) : RVec m := fun i => Real.sign (x i)

noncomputable def smoothSign (a δ t : ℝ) : ℝ :=
  2 * cdf (gaussianReal 0 1) ((a + Real.sqrt (1-δ^2)*t)/δ) - 1

noncomputable def smoothSigns {m : ℕ} (a : RVec m) (δ : ℝ) (x : RVec m) : RVec m :=
  fun i => smoothSign (a i) δ (x i)

/-- Gaussian law on ordinary coordinates, transported from Mathlib's Euclidean space. -/
noncomputable def gaussian (m : ℕ) (cov : Matrix (Fin m) (Fin m) ℝ) : Measure (RVec m) :=
  (multivariateGaussian 0 cov).map (fun x : EuclideanSpace ℝ (Fin m) => fun i => x i)

/-- Product law is the independence convention throughout the interpolation statements. -/
noncomputable def gaussianPair {m : ℕ} (covZ covD : Matrix (Fin m) (Fin m) ℝ) :=
  (gaussian m covZ).prod (gaussian m covD)

noncomputable def interpolate {m : ℕ} (t : ℝ) (z : RVec m × RVec m) : RVec m :=
  Real.sqrt t • z.1 + Real.sqrt (1-t) • z.2

noncomputable def comparisonError (m : ℕ) (L K β δ : ℝ) : ℝ :=
  400*L*δ*Real.sqrt (Real.log (2*m)) + β*K/(4*δ^2) + 4/(m:ℝ)^48

end BQPNotInIP.OracleSep


