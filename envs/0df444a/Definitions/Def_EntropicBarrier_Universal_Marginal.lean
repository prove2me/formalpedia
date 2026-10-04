-- Prove2me | Definitions.Def_EntropicBarrier_Universal_Marginal
-- name    : EntropicBarrier_Universal_Marginal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:42:39.865851+00:00
-- url     : https://prove2.me/theorems/bfd6f494-0a5f-4bbe-816a-2e43badde67f
-- title:
--   $n$-concavity, section marginal $\lambda$, density $\rho$ of $\langle\theta/\|\theta\|,X\rangle$, and the constant $c(\varepsilon)$ of Lemma 4
-- statement:
--   1. A function $\varphi$ is **$n$-concave** on a set $s\subseteq\mathbb R$ if $\varphi^{1/n}$ is concave on $s$.
--   2. For a convex body $\mathcal K\subset\mathbb R^n$ and $\theta\ne0$, the **one-dimensional marginal** of the uniform measure on $\mathcal K$ in the direction $\theta/\|\theta\|$ is
--   $$\lambda(y)=\frac{\mathrm{Vol}_{n-1}\left(\mathcal K\cap\{y\theta/\|\theta\|+\theta^\perp\}\right)}{\mathrm{Vol}(\mathcal K)},\qquad y\in\mathbb R.$$
--   3. The density of $Y=\langle\theta/\|\theta\|,X\rangle$ with $X\sim p_\theta$ is
--   $$\rho(y)=\frac{\lambda(y)\exp(y\|\theta\|)}{\int_{\mathbb R}\lambda(s)\exp(s\|\theta\|)\,ds}.$$
--   4. For $0<\varepsilon<1$,
--   $$c(\varepsilon)=\left(1+\frac{2}{\log(1/\varepsilon)}\right)^3\left(1+\frac{2}{\log(1/\varepsilon)}+\frac{2}{\log^2(1/\varepsilon)}\right).$$
--
--   These are the objects of the variance bound in the proof of Theorem 1: $\lambda$ is $n$-concave by the Brunn–Minkowski inequality, and $\rho$ is the density whose local sub-Gaussian shape (Lemma 3) controls $\mathrm{Var}(Y)$.
--
--   **Formalization Note** $\mathrm{Vol}_{n-1}$ of the section $\mathcal K\cap\{x:\langle\theta/\|\theta\|,x\rangle=y\}$ is Mathlib's $(n-1)$-dimensional Hausdorff measure, which is unnormalized: on a hyperplane of $\mathbb R^n$ it is a fixed positive multiple of the $(n-1)$-dimensional volume. Positive constant multiples preserve $n$-concavity and cancel in $\rho$, so $\rho$ is exactly the paper's density. $\lambda$ and $\rho$ are these fixed pointwise versions, not almost-everywhere defined densities, because Lemma 3 evaluates $\rho$ at points and at a maximizer.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), pp. 7-9, §4, eq. (8), Lemma 4 and proof of Lemma 3

import Mathlib

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

/-- **`n`-concavity** (§4, p. 9): `φ` is `n`-concave on `s` when `φ^{1/n}` is concave on `s`. -/
def IsNConcaveOn (n : ℝ) (s : Set ℝ) (φ : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ s (fun x => φ x ^ (1 / n))

/-- `(n-1)`-dimensional (Hausdorff) measure of the hyperplane section
`K ∩ {x : ⟪u, x⟫ = y}`. Mathlib's Hausdorff measure is unnormalized, so this is a fixed
positive multiple of `Vol_{n-1}`; the multiple cancels in `projDensity`. -/
noncomputable def sectionVol {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) (y : ℝ) : ℝ :=
  (Measure.hausdorffMeasure ((n : ℝ) - 1) (K ∩ {x | ⟪u, x⟫ = y})).toReal

/-- The one-dimensional marginal of the uniform measure on `K` in the direction `θ/‖θ‖`
(§4, p. 8): `λ(y) = Vol_{n-1}(K ∩ {yθ/‖θ‖ + θ^⊥}) / Vol(K)` (up to the Hausdorff
normalization constant). -/
noncomputable def marginalDensity {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) (y : ℝ) : ℝ :=
  sectionVol K (‖θ‖⁻¹ • θ) y / (volume K).toReal

/-- The density `ρ` of `Y = ⟪θ/‖θ‖, X⟫`, `X ∼ p_θ` (§4, eq. (8), p. 7, and p. 8):
`ρ(y) = λ(y) exp(y‖θ‖) / ∫_ℝ λ(s) exp(s‖θ‖) ds`, this fixed version. -/
noncomputable def projDensity {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) (y : ℝ) : ℝ :=
  marginalDensity K θ y * Real.exp (y * ‖θ‖) /
    ∫ s, marginalDensity K θ s * Real.exp (s * ‖θ‖)

/-- The constant of Lemma 4 (p. 8):
`c(ε) = (1 + 2/log(1/ε))³ (1 + 2/log(1/ε) + 2/log²(1/ε))`. -/
noncomputable def lemma4Const (ε : ℝ) : ℝ :=
  (1 + 2 / Real.log (1 / ε)) ^ 3 *
    (1 + 2 / Real.log (1 / ε) + 2 / Real.log (1 / ε) ^ 2)

end EntropicBarrier.Universal


