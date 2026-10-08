-- Prove2me | Definitions.Def_SmoothedSimplex_TwoPhase_gaussianInput
-- name    : SmoothedSimplex_TwoPhase_gaussianInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:02:01.851993+00:00
-- url     : https://prove2.me/theorems/5dd5c037-8254-4079-8680-7b8fb4f398d3
-- title:
--   Gaussian perturbation and independent sampling laws
-- statement:
--   A constraint vector in $\mathbb R^d$ has independent real Gaussian coordinates with prescribed means and common standard deviation $\sigma$. The $n$ constraint vectors and the $n$ right-hand sides are mutually independent. The joint input law is the product of these $n(d+1)$ Gaussian laws, each with variance $\sigma^2$.
--
--   The algorithm draws $N=\lceil3nd\ln n\rceil$ independent, uniform $d$-subsets of $[n]$, with replacement. Its coefficient vector is uniform on the truncated simplex
--   $$A_\delta=\{\alpha\in\mathbb R^d:\sum_i\alpha_i=1,\ \alpha_i\ge\delta\},\qquad \delta=d^{-2}.$$
--   The uniform law is represented by normalizing independent rate-one exponential weights, then shifting and scaling the resulting simplex vector. This representation is reusable for the paper's random-basis argument.
--
--   **Formalization Note** Indices use `Fin n` and `Fin d`; $N$ is rounded upward because the printed $3nd\ln n$ is generally not an integer. The Gaussian constructor takes variance, so the code passes $\sigma^2$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, §2.4, printed p. 19, PDF p. 19; algorithm, printed p. 35, PDF p. 35; §5.2, printed p. 68, PDF p. 68

import Mathlib

namespace SmoothedSimplex.TwoPhase

/-- The Euclidean vector carrier of Spielman–Teng, arXiv:cs/0111050v7, §2.1,
printed p. 13, PDF p. 13. Coordinates are indexed from zero in Lean. -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A Gaussian vector with independent coordinates of standard deviation `σ`, centered
at `c` (Spielman–Teng, §2.4, printed p. 19, PDF p. 19). The variance parameter of
`gaussianReal` is `σ²`. -/
noncomputable def gaussianVector {d : ℕ} (c : Point d) (σ : ℝ) : MeasureTheory.Measure (Point d) :=
  (MeasureTheory.Measure.pi (fun k : Fin d =>
    ProbabilityTheory.gaussianReal (c k) ⟨σ ^ 2, sq_nonneg σ⟩)).map (WithLp.toLp 2)

/-- The independent family of perturbed constraint vectors (Spielman–Teng,
§2.4, printed p. 19, PDF p. 19). -/
noncomputable def gaussianFamily {n d : ℕ} (c : Fin n → Point d) (σ : ℝ) :
    MeasureTheory.Measure (Fin n → Point d) :=
  MeasureTheory.Measure.pi (fun i : Fin n => gaussianVector (c i) σ)

/-- Independent Gaussian vectors obtained from linear images of standard Gaussian
vectors. A lower and upper singular-value bound on each `Lᵢ` is equivalent to the
covariance eigenvalue bounds of Corollary 4.3.3, printed p. 56, PDF p. 56. -/
noncomputable def affineGaussianFamily {n d : ℕ} (c : Fin n → Point d)
    (L : Fin n → Point d →ₗ[ℝ] Point d) : MeasureTheory.Measure (Fin n → Point d) :=
  MeasureTheory.Measure.pi (fun i : Fin n =>
    (ProbabilityTheory.stdGaussian (Point d)).map (fun g => c i + L i g))

/-- Independent rate-one exponentials. Restriction to any `d` selected coordinates,
followed by normalization, gives the uniform simplex law in §5.2,
printed p. 68, PDF p. 68. -/
noncomputable def exponentialWeights (n : ℕ) : MeasureTheory.Measure (Fin n → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.expMeasure 1)

/-- Independent Gaussian perturbations of the constraint vectors and right-hand sides
(Spielman–Teng, Theorem 5.0.1, printed p. 59, PDF p. 59). -/
noncomputable def gaussianInput {n d : ℕ} (c : Fin n → Point d) (b : Fin n → ℝ)
    (σ : ℝ) : MeasureTheory.Measure ((Fin n → Point d) × (Fin n → ℝ)) :=
  (gaussianFamily c σ).prod
    (MeasureTheory.Measure.pi (fun i : Fin n =>
      ProbabilityTheory.gaussianReal (b i) ⟨σ ^ 2, sq_nonneg σ⟩))

/-- Number of independently sampled `d`-subsets. The paper's `3nd ln n` is rounded
up to the next integer (Spielman–Teng, algorithm on printed p. 35, PDF p. 35). -/
noncomputable def sampleCount (n d : ℕ) : ℕ :=
  Nat.ceil (3 * (n : ℝ) * (d : ℝ) * Real.log n)

/-- The space of `d`-subsets of `[n]` (Spielman–Teng, §5.1, printed p. 60,
PDF p. 60). -/
abbrev DSet (n d : ℕ) := {I : Finset (Fin n) // I.card = d}

/-- Independent uniform draws with replacement from the `d`-subsets of `[n]`.
Spielman–Teng, algorithm on printed p. 35, PDF p. 35; the use of independent draws
is visible in the proof of Corollary 5.1.2, printed p. 61, PDF p. 61. -/
noncomputable def sampleLaw (n d : ℕ) :
    MeasureTheory.Measure (Fin (sampleCount n d) → DSet n d) :=
  MeasureTheory.Measure.pi (fun _ : Fin (sampleCount n d) =>
    (1 / (Nat.choose n d : ENNReal)) • (MeasureTheory.Measure.count :
      MeasureTheory.Measure (DSet n d)))

/-- Exponential weights, normalized and shifted, give the uniform law on the
simplex `A_δ = {α : ∑ αᵢ = 1, αᵢ ≥ δ}` for `0 ≤ δ ≤ 1/d`.
Spielman–Teng, definition of `A_δ`, printed p. 68, PDF p. 68. The all-zero
weight vector is null under this law; Lean's zero division selects zero there. -/
noncomputable def simplexCoefficient {d : ℕ} (δ : ℝ) (w : Fin d → ℝ) : Fin d → ℝ :=
  fun i => δ + (1 - (d : ℝ) * δ) * w i / (∑ j, w j)

/-- The uniform law on `A_δ`, represented as normalized independent rate-one
exponentials; the shift and dilation in `simplexCoefficient` preserve normalized
simplex volume. Spielman–Teng, printed p. 68, PDF p. 68. -/
noncomputable def simplexLaw (d : ℕ) (δ : ℝ) : MeasureTheory.Measure (Fin d → ℝ) :=
  (exponentialWeights d).map
    (simplexCoefficient δ)

end SmoothedSimplex.TwoPhase


