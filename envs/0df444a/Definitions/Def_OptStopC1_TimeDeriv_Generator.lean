-- Prove2me | Definitions.Def_OptStopC1_TimeDeriv_Generator
-- name    : OptStopC1_TimeDeriv_Generator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:32.370419+00:00
-- url     : https://prove2.me/theorems/d9817e36-5b28-4d17-bdf3-4fdd2258e4ce
-- title:
--   (2.14), p. 7 and (5.10)–(5.11), p. 20 — the generator 𝕃_X, the C^{1,2} condition, and H̃ = G_t + 𝕃_X G + H
-- statement:
--   This file defines the infinitesimal generator (2.14) acting in the space variable, the regularity condition (5.10) on the gain function, and the function $\tilde H$ of (5.11).
--
--   **Coefficients.** For $x\in\mathbb R^{d-1}$ let $\sigma(x)=(\sigma_{ij}(x))$ be a symmetric positive semi-definite matrix (the diffusion coefficient), $\mu(x)=(\mu_i(x))$ a vector (the drift coefficient), and $\nu(x,dy)$ a non-negative measure on $\mathbb R^{d-1}\setminus\{0\}$ (the compensator of the measure of jumps).
--
--   **Derivatives.** $G_t=\partial_tG$ is the time derivative on $[0,T]$, one-sided at $t=0$ and $t=T$, and $\partial G/\partial x_i$, $\partial^2G/\partial x_i\partial x_j$ are the spatial partial derivatives.
--
--   **Condition (5.10).** $(t,x)\mapsto G(t,x)$ is once continuously differentiable in $t$ and twice continuously differentiable in $x$ on $[0,T]\times\mathbb R^{d-1}$. That is, $\partial_tG$ exists on $[0,T]\times\mathbb R^{d-1}$ and is continuous there, $x\mapsto G(t,x)$ is $C^2$ for each $t\in[0,T]$, and the first and second spatial derivatives are jointly continuous in $(t,x)$.
--
--   **Generator (2.14).** With the killing rate $\lambda(t,x)$ of the problem,
--   $$\mathbb L_XG(t,x)=\frac12\sum_{i,j}\sigma_{ij}(x)\frac{\partial^2G}{\partial x_i\partial x_j}(t,x)+\sum_i\mu_i(x)\frac{\partial G}{\partial x_i}(t,x)-\lambda(t,x)G(t,x)+\int\Big(G(t,y)-G(t,x)-\sum_i(y_i-x_i)\frac{\partial G}{\partial x_i}(t,x)\Big)\,\nu(x,dy).$$
--   $G$ is in the domain of $\mathbb L_X$ when the jump integrand is $\nu(x,\cdot)$-integrable at every $(t,x)\in[0,T]\times\mathbb R^{d-1}$.
--
--   **The function of (5.11).**
--   $$\tilde H(t,x)=(G_t+\mathbb L_XG+H)(t,x).$$
--
--   These are the quantities in the hypotheses (5.11)–(5.13) of Theorem 15.
--
--   **Formalization Note** The measure $\nu(x,\cdot)$ is a measure on $\mathbb R^{d-1}$ with no mass at $0$. The jump integrand is kept exactly as printed in (2.14), $F(y)-F(x)-\sum_i(y_i-x_i)\partial_iF(x)$. The generator enters Theorem 15 only through hypotheses, so the theorem is true under any fixed reading. The time derivative is the derivative of $s\mapsto G(s,x)$ within $[0,T]$. The spatial derivatives are Fréchet derivatives of $y\mapsto G(t,y)$ evaluated on the coordinate vectors. The coefficients depend on $x$ only, matching the time-independent spatial flow; only $\lambda$ depends on $t$. The generic name `timeDeriv` is also applied to $V$ in the theorems.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 7, (2.14); p. 20, Theorem 15, (5.10), (5.11)

import Mathlib
import Definitions.Def_OptStopC1_TimeDeriv_Flow

namespace OptStopC1.TimeDeriv

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

variable {m : ℕ}

/-- The coefficients of the infinitesimal generator (2.14) acting in the space variable
`x ∈ ℝ^{d−1}`: a symmetric positive semi-definite diffusion matrix `σ(x)`, a drift vector `μ(x)`,
and a non-negative measure `ν(x, dy)` on `ℝ^{d−1} \ {0}` (the compensator of the jump measure),
encoded as a measure on `ℝ^{d−1}` with no mass at `0`. -/
structure GenCoeffs (m : ℕ) where
  σ : Space m → Matrix (Fin m) (Fin m) ℝ
  μ : Space m → Space m
  ν : Space m → Measure (Space m)
  σ_posSemidef : ∀ x, (σ x).PosSemidef
  ν_zero : ∀ x, ν x {0} = 0

/-- The time derivative `∂_t f(t, x)` on `[0, T]`, one-sided at `t = 0` and `t = T`:
the derivative of `s ↦ f(s, x)` within `[0, T]` at `t`. -/
noncomputable def timeDeriv (T : ℝ) (f : ℝ × Space m → ℝ) (p : ℝ × Space m) : ℝ :=
  derivWithin (fun s => f (s, p.2)) (Set.Icc 0 T) p.1

/-- The spatial partial derivative `∂f/∂x_i (t, x)` (coordinate `i : Fin m`). -/
noncomputable def spacePartial (f : ℝ × Space m → ℝ) (p : ℝ × Space m) (i : Fin m) : ℝ :=
  fderiv ℝ (fun y => f (p.1, y)) p.2 (EuclideanSpace.single i 1)

/-- The second spatial partial derivative `∂²f/∂x_i∂x_j (t, x) = ∂_{x_i}(∂_{x_j} f)(t, x)`. -/
noncomputable def spacePartial2 (f : ℝ × Space m → ℝ) (p : ℝ × Space m) (i j : Fin m) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ (fun y' => f (p.1, y')) y (EuclideanSpace.single j 1)) p.2
    (EuclideanSpace.single i 1)

/-- Condition (5.10): `(t, x) ↦ G(t, x)` is once continuously differentiable in `t` and twice
continuously differentiable in `x` on `[0, T] × ℝ^{d−1}`. Explicitly: `t ↦ G(t, x)` is
differentiable within `[0, T]` and `∂_t G` is continuous on `[0, T] × ℝ^{d−1}`; for each
`t ∈ [0, T]`, `x ↦ G(t, x)` is `C²`; and the first and second spatial derivatives are jointly
continuous on `[0, T] × ℝ^{d−1}`. -/
def IsC12On (T : ℝ) (G : ℝ × Space m → ℝ) : Prop :=
  (∀ p ∈ domain m T, DifferentiableWithinAt ℝ (fun s => G (s, p.2)) (Set.Icc 0 T) p.1) ∧
  ContinuousOn (timeDeriv T G) (domain m T) ∧
  (∀ t ∈ Set.Icc 0 T, ContDiff ℝ 2 (fun y => G (t, y))) ∧
  ContinuousOn (fun p : ℝ × Space m => fderiv ℝ (fun y => G (p.1, y)) p.2) (domain m T) ∧
  ContinuousOn
    (fun p : ℝ × Space m => fderiv ℝ (fun y => fderiv ℝ (fun y' => G (p.1, y')) y) p.2)
    (domain m T)

/-- The integrand of the jump part of (2.14), exactly as printed:
`F(y) − F(x) − Σ_i (y_i − x_i) ∂F/∂x_i (x)`, applied to `F = G(t, ·)`. -/
noncomputable def jumpIntegrand (G : ℝ × Space m → ℝ) (p : ℝ × Space m) (y : Space m) : ℝ :=
  G (p.1, y) - G p - ∑ i, (y i - p.2 i) * spacePartial G p i

/-- `G` is in the domain of `𝕃_X` (p. 7, "for any function F from its domain"), in the sense used
here: the jump integrand of (2.14) is `ν(x, ·)`-integrable at every `(t, x) ∈ [0, T] × ℝ^{d−1}`. -/
def InGenDomain (c : GenCoeffs m) (T : ℝ) (G : ℝ × Space m → ℝ) : Prop :=
  ∀ p ∈ domain m T, Integrable (jumpIntegrand G p) (c.ν p.2)

/-- The infinitesimal generator (2.14) of the spatial process applied to `G(t, ·)`, with the
killing rate `λ(t, x)` of the problem:
`𝕃_X G(t, x) = ½ Σ_{i,j} σ_{ij}(x) ∂²G/∂x_i∂x_j (t, x) + Σ_i μ_i(x) ∂G/∂x_i (t, x) − λ(t, x) G(t, x)
 + ∫ (G(t, y) − G(t, x) − Σ_i (y_i − x_i) ∂G/∂x_i (t, x)) ν(x, dy)`. -/
noncomputable def genX (c : GenCoeffs m) (lam G : ℝ × Space m → ℝ) (p : ℝ × Space m) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, c.σ p.2 i j * spacePartial2 G p i j
    + ∑ i, c.μ p.2 i * spacePartial G p i
    - lam p * G p
    + ∫ y, jumpIntegrand G p y ∂(c.ν p.2)

/-- `H̃ := G_t + 𝕃_X G + H` of (5.11). -/
noncomputable def Htilde (c : GenCoeffs m) (T : ℝ) (lam G H : ℝ × Space m → ℝ)
    (p : ℝ × Space m) : ℝ :=
  timeDeriv T G p + genX c lam G p + H p

end OptStopC1.TimeDeriv


