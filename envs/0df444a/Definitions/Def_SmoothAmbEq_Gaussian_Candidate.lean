-- Prove2me | Definitions.Def_SmoothAmbEq_Gaussian_Candidate
-- name    : SmoothAmbEq_Gaussian_Candidate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:15.845598+00:00
-- url     : https://prove2.me/theorems/1a0b8b4b-dd2a-4d42-aaf0-218d8f2adc09
-- title:
--   (5.8)–(5.12), (5.16)–(5.18) — a₁, a₂, the ODE systems, α*, ψ, Ψ, the candidate g^z and π*, and the closed-form m₁, m₄, m₅, m₆
-- statement:
--   This file defines the closed-form candidate of §5.2–§5.3 (pp. 16–18).
--
--   1. **Coefficients.** Six functions $m_1,\dots,m_6$ on $[0,T]$, and
--   $$a_1(t,m_2,m_3)=\frac{(1+\zeta(t)m_2)(\zeta(t)^{-1}+\alpha m_2)}{\zeta(t)^{-1}-\alpha m_3},\qquad a_2(t,m_2,m_3)=\frac{\alpha(1+\zeta(t)m_2)}{\zeta(t)^{-1}-\alpha m_3}.$$
--   2. **ODE system (5.10).** With $A_i(t)=a_i(t,m_2(t),m_3(t))$, $\zeta=\zeta(t)$:
--   $$\begin{aligned}\sigma^2m_1'&=2\zeta m_1-A_1^2,&\sigma^2m_2'&=(1+\zeta m_2)A_1+\zeta m_2,\\ \sigma^2m_3'&=-2\zeta m_2-\zeta^2m_2^2,&\sigma^2m_4'&=\zeta m_4-A_1A_2m_5-r\zeta m_1,\\ \sigma^2m_5'&=(1+\zeta m_2)A_2m_5-r(1+\zeta m_2),&\sigma^2m_6'&=-\tfrac12A_2^2m_5^2+\tfrac12r^2-\tfrac12\zeta^2m_1-r\zeta m_4,\end{aligned}$$
--   with $m_1(T)=\dots=m_6(T)=0$; the reduced system (5.16) consists of the $m_2,m_3$ equations with $m_2(T)=m_3(T)=0$.
--   3. **Critical exponent (5.17).** $\alpha^*<0$ with $\big(1+\sigma_0^{-2}\sigma^2T^{-1}\big)\int_0^\infty e^{-x}(1+(1-\alpha^*)x)^{\frac{\alpha^*}{1-\alpha^*}}dx=1$.
--   4. **ψ and Ψ** (p. 18): $\psi(x)=e^{\frac{x}{1-x}}(1-x)^{\frac{\alpha-2}{\alpha-1}}(1-\alpha x)^{\frac{\alpha}{\alpha-1}}$ and $\Psi(x)=\int_0^x\frac{ds}{\psi(s)}$ on $[0,1/(\alpha\vee1))$.
--   5. **Candidate** (5.8)–(5.9), (5.12):
--   $$g^z(t,x,\beta)=-\frac1k\exp\big\{-ke^{r(T-t)}x+f^z(t,\beta)\big\},\quad f^z(t,\beta)=\tfrac12m_1\beta^2+m_2\beta z+\tfrac12m_3z^2+m_4\beta+m_5z+m_6,$$
--   $$\pi^*(t,x,\beta)=\frac{e^{-r(T-t)}}{k\sigma^2}\big\{a_1(t,m_2(t),m_3(t))+\zeta(t)m_1(t)\big\}(\beta-r).$$
--   6. **Closed form (5.18).** From $(m_2,m_3)$: $m_1(t)=\sigma^{-2}\zeta(t)^{-2}\int_t^T\zeta^2A_1^2\,ds$, $m_4=-rm_1-rm_2$, $m_5=-rm_2-rm_3$, $m_6(t)=\sigma^{-2}\int_t^T\big[\tfrac12A_2^2m_5^2-\tfrac12r^2+\tfrac12\zeta^2m_1+r\zeta m_4\big]ds$.
--
--   These are the explicit objects of Lemma 5.3, Proposition 5.4 and Theorem 5.5.
--
--   **Formalization Note** A solution of (5.10) or (5.16) is a function with, at each $t\in[0,T]$, the prescribed derivative within $[0,T]$ (one-sided at the endpoints), and it is required to keep the denominator $\zeta(t)^{-1}-\alpha m_3(t)$ positive on $[0,T]$: without this, a function crossing a zero of the denominator would solve the system with Lean's $x/0=0$. Proposition 5.4 proves this positivity for the true solution, and Lemma 5.3 assumes it. The predicate for $\alpha^*$ includes $\alpha^*<0$, where the integrand is bounded by $e^{-x}$.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, pp. 16–18, (5.8)–(5.10), (5.12), (5.16)–(5.18)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model

open MeasureTheory Set

namespace SmoothAmbEq.Gaussian

/-- The six coefficient functions `m₁, …, m₆ : [0, T] → ℝ` of the ansatz (5.9), p. 16. -/
structure Coeffs where
  m₁ : ℝ → ℝ
  m₂ : ℝ → ℝ
  m₃ : ℝ → ℝ
  m₄ : ℝ → ℝ
  m₅ : ℝ → ℝ
  m₆ : ℝ → ℝ

/-- `a₁(t, m₂, m₃) = (1 + ζ(t)m₂)(ζ(t)⁻¹ + αm₂) / (ζ(t)⁻¹ - αm₃)`, p. 16. -/
noncomputable def a₁ (M : Model) (t m₂ m₃ : ℝ) : ℝ :=
  (1 + M.ζ t * m₂) * ((M.ζ t)⁻¹ + M.α * m₂) / ((M.ζ t)⁻¹ - M.α * m₃)

/-- `a₂(t, m₂, m₃) = α(1 + ζ(t)m₂) / (ζ(t)⁻¹ - αm₃)`, p. 16. -/
noncomputable def a₂ (M : Model) (t m₂ m₃ : ℝ) : ℝ :=
  M.α * (1 + M.ζ t * m₂) / ((M.ζ t)⁻¹ - M.α * m₃)

/-- `(m₁, …, m₆)` solves the ODE system (5.10), p. 16, on `[0, T]`: each `mᵢ` has, at every
`t ∈ [0, T]`, the derivative within `[0, T]` prescribed by (5.10) (written as `σ² mᵢ'(t) = …`),
`mᵢ(T) = 0`, and the denominator `ζ(t)⁻¹ - αm₃(t)` of `a₁`, `a₂` is positive on `[0, T]`. -/
def SolvesODE510 (M : Model) (c : Coeffs) : Prop :=
  (∀ t ∈ Icc 0 M.T, 0 < (M.ζ t)⁻¹ - M.α * c.m₃ t) ∧
  (∀ t ∈ Icc 0 M.T, HasDerivWithinAt c.m₁
    ((2 * M.ζ t * c.m₁ t - (a₁ M t (c.m₂ t) (c.m₃ t)) ^ 2) / M.σ ^ 2) (Icc 0 M.T) t) ∧
  (∀ t ∈ Icc 0 M.T, HasDerivWithinAt c.m₂
    (((1 + M.ζ t * c.m₂ t) * a₁ M t (c.m₂ t) (c.m₃ t) + M.ζ t * c.m₂ t) / M.σ ^ 2)
    (Icc 0 M.T) t) ∧
  (∀ t ∈ Icc 0 M.T, HasDerivWithinAt c.m₃
    ((-2 * M.ζ t * c.m₂ t - M.ζ t ^ 2 * c.m₂ t ^ 2) / M.σ ^ 2) (Icc 0 M.T) t) ∧
  (∀ t ∈ Icc 0 M.T, HasDerivWithinAt c.m₄
    ((M.ζ t * c.m₄ t - a₁ M t (c.m₂ t) (c.m₃ t) * a₂ M t (c.m₂ t) (c.m₃ t) * c.m₅ t
      - M.r * M.ζ t * c.m₁ t) / M.σ ^ 2) (Icc 0 M.T) t) ∧
  (∀ t ∈ Icc 0 M.T, HasDerivWithinAt c.m₅
    (((1 + M.ζ t * c.m₂ t) * a₂ M t (c.m₂ t) (c.m₃ t) * c.m₅ t
      - M.r * (1 + M.ζ t * c.m₂ t)) / M.σ ^ 2) (Icc 0 M.T) t) ∧
  (∀ t ∈ Icc 0 M.T, HasDerivWithinAt c.m₆
    ((-(1 / 2) * (a₂ M t (c.m₂ t) (c.m₃ t)) ^ 2 * c.m₅ t ^ 2 + 1 / 2 * M.r ^ 2
      - 1 / 2 * M.ζ t ^ 2 * c.m₁ t - M.r * M.ζ t * c.m₄ t) / M.σ ^ 2) (Icc 0 M.T) t) ∧
  c.m₁ M.T = 0 ∧ c.m₂ M.T = 0 ∧ c.m₃ M.T = 0 ∧ c.m₄ M.T = 0 ∧ c.m₅ M.T = 0 ∧ c.m₆ M.T = 0

/-- `(m₂, m₃)` solves the reduced system (5.16), p. 17, on `[0, T]` (the second and third
equations of (5.10) with `m₂(T) = m₃(T) = 0`), with `ζ(t)⁻¹ - αm₃(t) > 0` on `[0, T]`. -/
def SolvesODE516 (M : Model) (m₂ m₃ : ℝ → ℝ) : Prop :=
  (∀ t ∈ Icc 0 M.T, 0 < (M.ζ t)⁻¹ - M.α * m₃ t) ∧
  (∀ t ∈ Icc 0 M.T, HasDerivWithinAt m₂
    (((1 + M.ζ t * m₂ t) * a₁ M t (m₂ t) (m₃ t) + M.ζ t * m₂ t) / M.σ ^ 2) (Icc 0 M.T) t) ∧
  (∀ t ∈ Icc 0 M.T, HasDerivWithinAt m₃
    ((-2 * M.ζ t * m₂ t - M.ζ t ^ 2 * m₂ t ^ 2) / M.σ ^ 2) (Icc 0 M.T) t) ∧
  m₂ M.T = 0 ∧ m₃ M.T = 0

/-- `a` is a critical exponent `α*` of Proposition 5.4: `a < 0` and (5.17), p. 17,
`(1 + σ₀⁻²σ²T⁻¹) ∫₀^∞ e^{-x}(1 + (1 - a)x)^{a/(1-a)} dx = 1`. -/
def IsAlphaStar (M : Model) (a : ℝ) : Prop :=
  a < 0 ∧
  (1 + M.σ ^ 2 / (M.σ₀ ^ 2 * M.T)) *
    (∫ x in Ioi (0 : ℝ), Real.exp (-x) * (1 + (1 - a) * x) ^ (a / (1 - a))) = 1

/-- `ψ(x) = e^{x/(1-x)} (1 - x)^{(α-2)/(α-1)} (1 - αx)^{α/(α-1)}`, `x ∈ [0, 1/(α ∨ 1))`,
p. 18 (used for `α ∉ {0, 1}`). -/
noncomputable def ψ (M : Model) (x : ℝ) : ℝ :=
  Real.exp (x / (1 - x)) * (1 - x) ^ ((M.α - 2) / (M.α - 1)) * (1 - M.α * x) ^ (M.α / (M.α - 1))

/-- `Ψ(x) = ∫₀^x 1/ψ(s) ds`, p. 18. -/
noncomputable def Ψ (M : Model) (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, 1 / ψ M s

/-- The quadratic form (5.9), p. 16:
`f^z(t, β) = ½m₁(t)β² + m₂(t)βz + ½m₃(t)z² + m₄(t)β + m₅(t)z + m₆(t)`. -/
noncomputable def fz (c : Coeffs) (z t β : ℝ) : ℝ :=
  1 / 2 * c.m₁ t * β ^ 2 + c.m₂ t * β * z + 1 / 2 * c.m₃ t * z ^ 2 + c.m₄ t * β + c.m₅ t * z
    + c.m₆ t

/-- The candidate equilibrium value function (5.8), p. 16:
`g^z(t, x, β) = -(1/k) exp{-k e^{r(T-t)} x + f^z(t, β)}`. -/
noncomputable def gz (M : Model) (c : Coeffs) (z t x β : ℝ) : ℝ :=
  -(1 / M.k) * Real.exp (-M.k * Real.exp (M.r * (M.T - t)) * x + fz c z t β)

/-- The candidate equilibrium strategy (5.12), p. 17:
`π*(t, x, β) = e^{-r(T-t)}/(kσ²) · {a₁(t, m₂(t), m₃(t)) + ζ(t)m₁(t)} · (β - r)`. -/
noncomputable def piStar (M : Model) (c : Coeffs) (t _x β : ℝ) : ℝ :=
  Real.exp (-M.r * (M.T - t)) / (M.k * M.σ ^ 2)
    * (a₁ M t (c.m₂ t) (c.m₃ t) + M.ζ t * c.m₁ t) * (β - M.r)

/-- The coefficients `m₁, m₄, m₅, m₆` of (5.18), p. 18, built from `(m₂, m₃)`, with
`Aᵢ(t) = aᵢ(t, m₂(t), m₃(t))`:
`m₁(t) = σ⁻²ζ(t)⁻² ∫_t^T ζ²(s)A₁²(s) ds`, `m₄ = -rm₁ - rm₂`, `m₅ = -rm₂ - rm₃`,
`m₆(t) = σ⁻² ∫_t^T [½A₂²(s)m₅²(s) - ½r² + ½ζ²(s)m₁(s) + rζ(s)m₄(s)] ds`. -/
noncomputable def coeffs518 (M : Model) (m₂ m₃ : ℝ → ℝ) : Coeffs :=
  let A₁ : ℝ → ℝ := fun s => a₁ M s (m₂ s) (m₃ s)
  let A₂ : ℝ → ℝ := fun s => a₂ M s (m₂ s) (m₃ s)
  let m₁ : ℝ → ℝ := fun t =>
    (M.σ ^ 2)⁻¹ * (M.ζ t ^ 2)⁻¹ * ∫ s in t..M.T, M.ζ s ^ 2 * A₁ s ^ 2
  let m₄ : ℝ → ℝ := fun t => -M.r * m₁ t - M.r * m₂ t
  let m₅ : ℝ → ℝ := fun t => -M.r * m₂ t - M.r * m₃ t
  { m₁ := m₁, m₂ := m₂, m₃ := m₃, m₄ := m₄, m₅ := m₅
    m₆ := fun t => (M.σ ^ 2)⁻¹ * ∫ s in t..M.T,
      (1 / 2 * A₂ s ^ 2 * m₅ s ^ 2 - 1 / 2 * M.r ^ 2 + 1 / 2 * M.ζ s ^ 2 * m₁ s
        + M.r * M.ζ s * m₄ s) }

end SmoothAmbEq.Gaussian


