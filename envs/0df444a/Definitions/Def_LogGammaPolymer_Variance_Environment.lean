-- Prove2me | Definitions.Def_LogGammaPolymer_Variance_Environment
-- name    : LogGammaPolymer_Variance_Environment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:15.940669+00:00
-- url     : https://prove2.me/theorems/cc0a3fe8-7610-4f00-aac4-adbf2e42f5a8
-- title:
--   Sec. 2, (2.3)–(2.6), (3.17) — inverse-gamma environment with parameters θ, μ − θ, μ; Ψ₀, Ψ₁; L(θ, x); annealed measure; rectangle conditions (2.6), (4.9)
-- statement:
--   This file fixes the random environment of the log-gamma polymer with boundary conditions and the quantities attached to it.
--
--   1. **Digamma and trigamma.** $\Psi_0=(\log\Gamma)'$ and $\Psi_1=\Psi_0'$ on $(0,\infty)$ (p. 6).
--   2. **The function $L$.** For $\theta,x>0$,
--   $$L(\theta,x)=\int_0^x\bigl(\Psi_0(\theta)-\log y\bigr)x^{-\theta}y^{\theta-1}e^{x-y}\,dy \qquad (3.17).$$
--   3. **Assumption (2.4).** Let $0<\theta<\mu$. On a probability space $(\Omega,\mathcal F,\mathbb P)$, the weights $\{U_{i,0},V_{0,j},Y_{i,j}: i,j\in\mathbb N\}$ are independent with
--   $$U_{i,0}^{-1}\sim\mathrm{Gamma}(\theta,1),\qquad V_{0,j}^{-1}\sim\mathrm{Gamma}(\mu-\theta,1),\qquad Y_{i,j}^{-1}\sim\mathrm{Gamma}(\mu,1),$$
--   where $\mathrm{Gamma}(a,r)$ has density $\Gamma(a)^{-1}r^ax^{a-1}e^{-rx}$ on $\mathbb R_+$.
--   4. **Free energy and annealed measure.** $\log Z_{m,n}$ is a random variable; the annealed measure is $P_{m,n}(A)=\mathbb E[Q^\omega_{m,n}(A)]$ and the annealed expectation is $E_{m,n}[f]=\mathbb E\bigl[\sum_xQ^\omega_{m,n}(x)f(x,\omega)\bigr]$ (p. 7).
--   5. **Rectangle conditions.** With a real scaling parameter $N$, condition (2.6) is
--   $$|m-N\Psi_1(\mu-\theta)|\le\gamma N^{2/3}\quad\text{and}\quad|n-N\Psi_1(\theta)|\le\gamma N^{2/3},$$
--   and (4.9) is the same with a number $\kappa_N$ in place of $\gamma N^{2/3}$.
--
--   The point $(\Psi_1(\mu-\theta),\Psi_1(\theta))$ is the characteristic direction of the polymer: along it the boundary weights produce fluctuations of order $N^{1/3}$ for $\log Z_{m,n}$.
--
--   **Formalization Note** `Env θ μ P` bundles the weight family `Y : ℕ × ℕ → Ω → ℝ`, its measurability, the mutual independence of all weights off the origin (`iIndepFun`), and the three laws as `P.map (fun ω => (Y p ω)⁻¹) = gammaMeasure a 1` (Mathlib's shape–rate parametrization). The constraints $0<\theta<\mu$ and `IsProbabilityMeasure P` are hypotheses of each theorem. Positivity of the weights is not assumed pointwise: it holds almost surely under the laws. $\Psi_0,\Psi_1$ are defined by `deriv` and used only at positive arguments.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Sec. 2, (2.3)–(2.6), p. 6, annealed measure p. 7; (3.17), p. 15; (4.9), p. 21

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths

namespace LogGammaPolymer.Variance

open MeasureTheory ProbabilityTheory

/-! The random environment of assumption (2.4), the digamma and trigamma functions, the function
`L(θ, x)` of (3.17), the annealed measure (p. 7) and the rectangle condition (2.6) of Seppäläinen,
arXiv:0911.2446v4. -/

/-- The digamma function `Ψ₀ = (log Γ)'` (p. 6), used at positive arguments only. -/
noncomputable def Psi0 (s : ℝ) : ℝ :=
  deriv (fun t => Real.log (Real.Gamma t)) s

/-- The trigamma function `Ψ₁ = Ψ₀'` (p. 6), used at positive arguments only. -/
noncomputable def Psi1 (s : ℝ) : ℝ :=
  deriv Psi0 s

/-- `L(θ, x) = ∫₀ˣ (Ψ₀(θ) − log y) x^{−θ} y^{θ−1} e^{x−y} dy` of (3.17), used for `θ, x > 0`. -/
noncomputable def Lfun (θ x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, (Psi0 θ - Real.log y) * x ^ (-θ) * y ^ (θ - 1) * Real.exp (x - y)

/-- Assumption (2.4) on a probability space `(Ω, P)`: the weights
`{U_{i,0} = Y_{i,0}, V_{0,j} = Y_{0,j}, Y_{i,j} : i, j ≥ 1}` (every site except the unused origin) are
independent random variables with `U_{i,0}^{-1} ∼ Gamma(θ, 1)`, `V_{0,j}^{-1} ∼ Gamma(μ − θ, 1)` and
`Y_{i,j}^{-1} ∼ Gamma(μ, 1)`. `Gamma(a, r)` is Mathlib's `gammaMeasure a r` (shape `a`, rate `r`). -/
structure Env (θ μ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The weights `Y_{i,j}(ω)`; the value at the origin is never used. -/
  Y : ℕ × ℕ → Ω → ℝ
  meas : ∀ p, Measurable (Y p)
  indep : iIndepFun (fun p : {p : ℕ × ℕ // p ≠ (0, 0)} => Y p.1) P
  lawU : ∀ i : ℕ, 1 ≤ i → P.map (fun ω => (Y (i, 0) ω)⁻¹) = gammaMeasure θ 1
  lawV : ∀ j : ℕ, 1 ≤ j → P.map (fun ω => (Y (0, j) ω)⁻¹) = gammaMeasure (μ - θ) 1
  lawY : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → P.map (fun ω => (Y (i, j) ω)⁻¹) = gammaMeasure μ 1

variable {θ μ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The weight configuration `ω = (Y_{i,j}(ω))` of the environment at the sample point `ω`. -/
def Env.conf (E : Env θ μ P) (ω : Ω) : ℕ × ℕ → ℝ := fun p => E.Y p ω

/-- The free energy `log Z_{m,n}` as a random variable. -/
noncomputable def logZ (E : Env θ μ P) (m n : ℕ) (ω : Ω) : ℝ :=
  Real.log (Z (E.conf ω) m n)

/-- The annealed probability `P_{m,n}(A) = 𝔼[Q^ω_{m,n}(A)]` of an event `A ⊆ Π_{m,n}` (p. 7). -/
noncomputable def Pann (E : Env θ μ P) (m n : ℕ) (A : Steps m n → Prop) : ℝ :=
  ∫ ω, Q (E.conf ω) m n A ∂P

/-- The integrand `ω ↦ E^{Q^ω_{m,n}}[f(x, ω)] = Σ_x Q^ω_{m,n}(x) f(x, ω)` of an annealed expectation. -/
noncomputable def quenchedMean (E : Env θ μ P) (m n : ℕ) (f : Steps m n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ s : Steps m n, Qpt (E.conf ω) m n s * f s ω

/-- The annealed expectation `E_{m,n}[f] = 𝔼[E^{Q^ω_{m,n}} f]` of a function `f(x, ω)` of the path and
the environment (p. 7). -/
noncomputable def Eann (E : Env θ μ P) (m n : ℕ) (f : Steps m n → Ω → ℝ) : ℝ :=
  ∫ ω, quenchedMean E m n f ω ∂P

/-- The rectangle condition (2.6): `|m − NΨ₁(μ − θ)| ≤ γN^{2/3}` and `|n − NΨ₁(θ)| ≤ γN^{2/3}`. -/
def InRect (θ μ γ N : ℝ) (m n : ℕ) : Prop :=
  |(m : ℝ) - N * Psi1 (μ - θ)| ≤ γ * N ^ ((2 : ℝ) / 3) ∧
    |(n : ℝ) - N * Psi1 θ| ≤ γ * N ^ ((2 : ℝ) / 3)

/-- The rectangle condition (4.9) at one value `κ = κ_N`: `|m − NΨ₁(μ − θ)| ≤ κ` and
`|n − NΨ₁(θ)| ≤ κ`. -/
def InRectK (θ μ κ N : ℝ) (m n : ℕ) : Prop :=
  |(m : ℝ) - N * Psi1 (μ - θ)| ≤ κ ∧ |(n : ℝ) - N * Psi1 θ| ≤ κ

end LogGammaPolymer.Variance


