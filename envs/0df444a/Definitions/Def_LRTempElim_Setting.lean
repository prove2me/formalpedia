-- Prove2me | Definitions.Def_LRTempElim_Setting
-- name    : LRTempElim_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:50.89743+00:00
-- url     : https://prove2.me/theorems/8a5a57b2-f267-47a9-b1f8-3d532922d91b
-- title:
--   Gaussian endpoints $N(\mp a/2,1)$, mixture $\nu_a$, linear bridge, features $(1,x,x^2)$ and function risk
-- statement:
--   For a separation parameter $a\in\mathbb R$ the two endpoint laws are
--   $$
--   Q_a=N(-a/2,1),\qquad P_a=N(a/2,1),
--   $$
--   and function risk is measured under the mixture $\nu_a=\tfrac12(P_a+Q_a)$. One sampling unit is an independent endpoint pair $W=(X_0,X_1)$ with $X_0\sim Q_a$ and $X_1\sim P_a$, i.e. $W\sim Q_a\otimes P_a$. The independent linear bridge is
--   $$
--   X_t(W)=(1-t)X_0+tX_1,\qquad 0\le t\le 1 .
--   $$
--   The feature maps are $\phi(x)=(1,x)^\top$ (used in Proposition A.2) and $\phi(x)=(1,x,x^2)^\top$, and the calibrated target coefficient is $\theta^\star_a=(0,a,0)^\top$, so that $\phi(x)^\top\theta^\star_a=\ell^\star(x)=ax$. For a feature map $\phi$ and a measure $\mu$, $\Sigma=\mathbb E_\mu[\phi\phi^\top]$ is the feature second-moment matrix. The function risk of a coefficient vector $\theta\in\mathbb R^3$ is
--   $$
--   R_a(\theta)=\|\phi^\top\theta-\ell^\star\|^2_{L^2(\nu_a)}=\int(\phi(x)^\top\theta-ax)^2\,d\nu_a(x).
--   $$
--
--   These objects fix the Gaussian weak-overlap family of §4.1 on which both estimators of the mission are compared.
--
--   **Formalization Note** Vectors of $\mathbb R^k$ are functions `Fin k → ℝ`, indexed from $0$: index $0$ is the constant feature, index $1$ is $x$, index $2$ is $x^2$. $\nu_a$ is the measure $2^{-1}(P_a+Q_a)$ and the pair law is the product measure on $\mathbb R\times\mathbb R$ with first coordinate $X_0$.
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §2.2 eq. (1), p.4 (pdf p.6); §4.1 and eq. (10), p.7 (pdf p.9); §A.2.3, p.20 (pdf p.22)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LRTempElim

/-!
# The Gaussian endpoint family of §4.1 and the function risk (10)

W. Chen, Y. Wu, J. Yang, D. Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic
Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee65139…),
§2.2 (p.4, pdf p.6), §4.1 and eq. (10) (p.7, pdf p.9), §A.2.3 (p.20, pdf p.22).

"Consider `Q_a = N(−a/2, 1)` and `P_a = N(a/2, 1)`, with `ν_a = (P_a + Q_a)/2` and `ℓ⋆(x) = ax`.
Both estimators fit `ϕ(x) = (1, x, x²)⊤` from n independent endpoint pairs" (p.7). "Each sampling
unit is an independent endpoint pair `W = (X₀, X₁)`, with `X₀ ∼ Q_a`, `X₁ ∼ P_a`" (p.20).
"`X_t(W_n) = (1 − t)X_{0,n} + tX_{1,n}`" (eq. (1), p.4). "`Σ_{ν_a} = E_{ν_a}[ϕϕ⊤]`" (p.7).

**Formalization Note.**
* Vectors of `ℝᵏ` are `Fin k → ℝ`, 0-based: for `phi3`, index 0 is the constant feature `1`,
  index 1 is `x`, index 2 is `x²`; `phi2 x = (1, x)`.
* `nu a = (1/2)(P_a + Q_a)` as a measure; `pairLaw a = Q_a ⊗ P_a` on `ℝ × ℝ`, so `W.1 = X₀ ∼ Q_a`
  and `W.2 = X₁ ∼ P_a`.
* `secondMoment ϕ μ = E_μ[ϕϕ⊤]` entrywise (Bochner integrals).
* `risk a θ = ‖ϕ⊤θ − ℓ⋆‖²_{L²(ν_a)} = ∫ (ϕ(x)⊤θ − ax)² dν_a(x)` with `ϕ = (1, x, x²)`.
-/

/-- `Q_a = N(−a/2, 1)`, the denominator endpoint law (§4.1, p.7). -/
noncomputable def endpointQ (a : ℝ) : Measure ℝ := gaussianReal (-a / 2) 1

/-- `P_a = N(a/2, 1)`, the numerator endpoint law (§4.1, p.7). -/
noncomputable def endpointP (a : ℝ) : Measure ℝ := gaussianReal (a / 2) 1

/-- The query law `ν_a = (P_a + Q_a)/2` under which function risk is measured (§4.1, p.7). -/
noncomputable def nu (a : ℝ) : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (endpointP a + endpointQ a)

/-- The law of one sampling unit `W = (X₀, X₁)`, `X₀ ∼ Q_a` and `X₁ ∼ P_a` independent
(§A.2.3, p.20). -/
noncomputable def pairLaw (a : ℝ) : Measure (ℝ × ℝ) := (endpointQ a).prod (endpointP a)

/-- The independent linear bridge `X_t(W) = (1 − t)X₀ + tX₁` (eq. (1), p.4). -/
def bridge (t : ℝ) (W : ℝ × ℝ) : ℝ := (1 - t) * W.1 + t * W.2

/-- The two-dimensional feature map `ϕ(x) = (1, x)⊤` of Proposition A.2 (p.15). -/
def phi2 (x : ℝ) : Fin 2 → ℝ := ![1, x]

/-- The quadratic feature map `ϕ(x) = (1, x, x²)⊤` of §4.1 (p.7); index 0 is the constant. -/
def phi3 (x : ℝ) : Fin 3 → ℝ := ![1, x, x ^ 2]

/-- The calibrated target coefficient `θ⋆_a = (0, a, 0)⊤`, so that `ϕ⊤θ⋆_a = ℓ⋆ = ax`
(§A.2.3, p.20; Proposition A.2, p.15). -/
def thetaStar (a : ℝ) : Fin 3 → ℝ := ![0, a, 0]

/-- The feature second-moment matrix `Σ = E_μ[ϕϕ⊤]` (p.7: `Σ_{ν_a} = E_{ν_a}[ϕϕ⊤]`). -/
noncomputable def secondMoment {X : Type*} [MeasurableSpace X] {k : ℕ} (ϕ : X → Fin k → ℝ)
    (μ : Measure X) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∫ x, ϕ x i * ϕ x j ∂μ

/-- The function risk of a coefficient vector, `‖ϕ⊤θ − ℓ⋆‖²_{L²(ν_a)}` with `ϕ = (1, x, x²)` and
`ℓ⋆(x) = ax` (eq. (10), p.7). -/
noncomputable def risk (a : ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  ∫ x, (phi3 x ⬝ᵥ θ - a * x) ^ 2 ∂(nu a)

end LRTempElim


