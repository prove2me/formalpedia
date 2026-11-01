-- Prove2me | Definitions.Def_FisherInfoIneq_fisherInfo
-- name    : FisherInfoIneq_fisherInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:31.161428+00:00
-- url     : https://prove2.me/theorems/ef19091b-4c03-4bfe-ad38-dc01d8a2caa6
-- title:
--   Fisher information $J(\mu)=\int f'^2/f$ of a law on $\mathbb R$, valued in $[0,\infty]$
-- statement:
--   For a probability law $\mu$ on $\mathbb R$ with an absolutely continuous density $f$ and derivative $f'$, the **Fisher information** (with respect to a translation parameter) is
--   $$J(\mu)=\int_{\mathbb R}\frac{f'(x)^2}{f(x)}\,dx=\mathbb E\big[\rho(X)^2\big],\qquad \rho=f'/f,\ X\sim\mu,$$
--   a number in $[0,\infty]$. If $\mu$ has no absolutely continuous density, $J(\mu)=+\infty$. The Fisher information of a real random variable $X$ is $J(X)=J(\text{law of }X)$; it depends on the law only.
--
--   This is the paper's $J(X)=J(\theta+X;\theta)=\mathrm{COV}\{\rho_X(X)\}$ of eq. (2), with the score $\rho_X$ of eq. (3); since the score has mean zero (eq. (30)), the covariance is the second moment. It is the quantity in the Fisher information inequality.
--
--   **Formalization Note** Lean takes the infimum of $\int f'^2/f$ over all representations $(f,f')$; all representations give the same value, so the infimum is that value, and the infimum over no representation is $+\infty$. On $\{f=0\}$ the integrand is $0$ (Lean's $x/0=0$), which agrees with the classical convention since $f'=0$ almost everywhere there. Sanity checks (proved, not uploaded): $J(N(0,v))=1/v$, $J(\text{Unif}[0,1])=+\infty$, $J(\delta_c)=+\infty$.
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, eq. (2) and (3), p.1; eq. (30), p.5

import Mathlib
import Definitions.Def_FisherInfoIneq_IsACDensity

open MeasureTheory
open scoped ENNReal

namespace FisherInfoIneq

/-- **Fisher information (with respect to a translation parameter)** of a law `μ` on `ℝ`:
$$J(\mu)=\int_{\mathbb R}\frac{f'(x)^2}{f(x)}\,dx=\mathbb E\big[\rho(X)^2\big],\qquad \rho=f'/f,$$
where `f` is an absolutely continuous density of `μ` with derivative `f′ = g`
(`IsACDensity μ f g`). The value lies in `[0, ∞]`. The Fisher information of a random variable `X`
on `(Ω, P)` is `fisherInfo (P.map X)`.

Liu–Viswanath, arXiv:cs/0604028v1, eq. (2), p.1: "J(X) := J(θ + X; θ) = COV{ρ_X(X)}", with the
score function ρ_X of (3); "this special form of the Fisher information matrix is a function of the
probability density of the random vector alone". The paper uses `J(X) = E[ρ_X²(X)]` in (30), p.5
("score functions always have zero mean").

**Formalization Note**
1. `COV{ρ_X(X)}` is read as `E[ρ_X(X)²] = ∫ f′²/f`; the two agree because the score has mean
   zero (eq. (30), p.5) whenever `J` is finite, and both are `+∞` otherwise.
2. `J` is valued in `ℝ≥0∞`. A law with no absolutely continuous density gets `J = +∞` (the infimum
   over an empty set of representations is `⊤`); this is the standard convention under which the
   Fisher information inequality holds for all independent pairs.
3. The infimum ranges over all representations `(f, g)`, but the value does not depend on the
   choice: the absolutely continuous version `f` is unique and `g` is unique Lebesgue-a.e.
4. On `{f = 0}` the integrand is `g²/0 = 0` in Lean; there `g = 0` a.e. anyway, since a
   nonnegative absolutely continuous function has zero derivative a.e. on its zero set. -/
noncomputable def fisherInfo (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (f : ℝ → ℝ) (g : ℝ → ℝ) (_ : IsACDensity μ f g), ∫⁻ x, ENNReal.ofReal (g x ^ 2 / f x)

end FisherInfoIneq


