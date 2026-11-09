-- Prove2me | Definitions.Def_SpectralSharpness_NormalWindow_BandLimited
-- name    : SpectralSharpness_NormalWindow_BandLimited
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:40.875105+00:00
-- url     : https://prove2.me/theorems/9f1f52a7-403e-41b5-b797-c7b2e2a46337
-- title:
--   Band-limited real trigonometric polynomials on $\mathbb T^n$ with spectrum in the ball $B_d$ or the cube
-- statement:
--   Points of the torus $\mathbb T^n=[-\pi,\pi)^n$ are represented by points $x\in\mathbb R^n$, and frequencies are integer vectors $k\in\mathbb Z^n$, paired with points by $k\cdot x=\sum_{i=1}^n k_i x_i$.
--
--   1. **Spectrum in a set.** For $S\subseteq\mathbb Z^n$, a real-valued function $f:\mathbb R^n\to\mathbb R$ has *spectrum in $S$* if there are a finite set $F\subseteq S$ and complex coefficients $\hat f(k)$ with
--   $$
--   f(x)=\sum_{k\in F}\hat f(k)\,e^{\,i\,k\cdot x}\qquad\text{for all }x\in\mathbb R^n .
--   $$
--   Such an $f$ is $2\pi$-periodic in every coordinate, i.e. it is a real trigonometric polynomial on $\mathbb T^n$.
--
--   2. **Euclidean ball.** $B_d=\{k\in\mathbb Z^n:\|k\|_2\le d\}$, where $\|k\|_2=\big(\sum_i k_i^2\big)^{1/2}$. A function is *band-limited with spectrum in $B_d$* if it has spectrum in $B_d$.
--
--   3. **Cube.** $\{k\in\mathbb Z^n:\|k\|_\infty\le d\}$, i.e. $|k_i|\le d$ for every $i$. A function is *band-limited with spectrum in the cube* if it has spectrum in this set.
--
--   These are the classifiers of §9 of the source: the Euclidean-ball spectrum is the hypothesis of Lemma 9.1 and Theorem 9.3, and the cube spectrum appears in the last sentence of Lemma 9.1, where the directional derivative bound acquires the factor $\|v\|_1\le\sqrt n$.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin n)` and frequencies `Fin n → ℤ`; `freqDot k x` is $k\cdot x$. `HasSpectrumIn S f` asks for a `Finset` of frequencies contained in `S` and coefficients `c : (Fin n → ℤ) → ℂ` with `(f x : ℂ) = ∑ k ∈ F, c k * exp (I * (k·x))` for all `x`. Real-valuedness is carried by the type of `f`; no symmetry condition on the coefficients is imposed (it is implied). The radius `d` is a real number; theorems using these predicates assume `0 ≤ d`.
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript (STOC 2027 submission #122; SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, §9 Setup and Lemma 9.1, p. 27 (B_d = {k ∈ Z^n : ∥k∥₂ ≤ d}; cube {k : ∥k∥∞ ≤ d}); §2, p. 6 (T = [−π, π))

import Mathlib

namespace SpectralSharpness.NormalWindow

/-- The pairing `k · x = ∑ᵢ kᵢ xᵢ` of an integer frequency vector `k ∈ ℤⁿ` with a point
`x ∈ ℝⁿ` (a point of the torus `𝕋ⁿ = [-π, π)ⁿ`, read through its representative in `ℝⁿ`). -/
noncomputable def freqDot {n : ℕ} (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, (k i : ℝ) * x i

/-- A real-valued function on `ℝⁿ` is a trigonometric polynomial on `𝕋ⁿ` with spectrum in
`S ⊆ ℤⁿ` if it is a finite exponential sum `f(x) = ∑_{k ∈ F} c_k e^{i k·x}` with complex
coefficients `c_k` and a finite set of frequencies `F ⊆ S`. Such an `f` is `2π`-periodic in
every coordinate, i.e. it is a function on `𝕋ⁿ`. -/
def HasSpectrumIn {n : ℕ} (S : Set (Fin n → ℤ)) (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ (F : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ), (↑F : Set (Fin n → ℤ)) ⊆ S ∧
    ∀ x, (f x : ℂ) = ∑ k ∈ F, c k * Complex.exp (Complex.I * (freqDot k x : ℂ))

/-- The Euclidean frequency ball `B_d = {k ∈ ℤⁿ : ‖k‖₂ ≤ d}`. -/
def euclidBall (n : ℕ) (d : ℝ) : Set (Fin n → ℤ) :=
  {k | Real.sqrt (∑ i, ((k i : ℝ)) ^ 2) ≤ d}

/-- The frequency cube `{k ∈ ℤⁿ : ‖k‖_∞ ≤ d}`. -/
def supCube (n : ℕ) (d : ℝ) : Set (Fin n → ℤ) :=
  {k | ∀ i, |(k i : ℝ)| ≤ d}

/-- `f` is band-limited with spectrum in the Euclidean ball `B_d`. -/
def IsBandLimitedBall {n : ℕ} (d : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  HasSpectrumIn (euclidBall n d) f

/-- `f` is band-limited with spectrum in the cube `{k : ‖k‖_∞ ≤ d}`. -/
def IsBandLimitedCube {n : ℕ} (d : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  HasSpectrumIn (supCube n d) f

end SpectralSharpness.NormalWindow


