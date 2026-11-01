-- Prove2me | Definitions.Def_FisherInfoIneq_score
-- name    : FisherInfoIneq_score
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:54.750678+00:00
-- url     : https://prove2.me/theorems/c5299f7e-b377-4c99-9824-7daa4b04e17a
-- title:
--   Score function $\rho_\mu=f'/f$ of a law on $\mathbb R$
-- statement:
--   For a law $\mu$ on $\mathbb R$ with an absolutely continuous density $f$ and derivative $f'$, the **score function** is
--   $$\rho_\mu(x)=\frac{\partial}{\partial x}\ln f(x)=\frac{f'(x)}{f(x)} .$$
--   The score of a random variable $X$ is $\rho_X=\rho_{\text{law of }X}$, evaluated at $X$ in eq. (6).
--
--   **Formalization Note** A representation $(f,f')$ is chosen; since $f$ is unique and $f'$ is unique Lebesgue-a.e., $\rho_\mu$ is determined $\mu$-almost everywhere, and statements use it only up to null sets. Where $f=0$ (a $\mu$-null set) Lean's quotient is $0$. If $\mu$ has no absolutely continuous density the score is undefined and the function is the placeholder $0$; statements about it assume such a density.
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, eq. (3), p.1

import Mathlib
import Definitions.Def_FisherInfoIneq_IsACDensity

open MeasureTheory

namespace FisherInfoIneq

open Classical in
/-- **Score function** of a law `μ` on `ℝ`: `ρ(x) = f′(x)/f(x) = ∂/∂x ln f(x)`, computed from a
chosen absolutely continuous density `f` of `μ` with derivative `g = f′` (`IsACDensity μ f g`).
If `μ` has no absolutely continuous density the score is undefined and this returns the
placeholder `0`.

Liu–Viswanath, arXiv:cs/0604028v1, eq. (3), p.1: "the score function ρ_X is defined as
ρ_X(x) := ∂/∂x ln f(x), and f(x) is the probability density function of the random vector X".
The score of a random variable `X` on `(Ω, P)` is `score (P.map X)`.

**Formalization Note** The representation `(f, g)` is chosen with `Classical.choose`. The
continuous density `f` is unique and `g` is unique Lebesgue-a.e., so `score μ` is determined
Lebesgue-a.e., hence `μ`-a.e. (as `μ` has a density); statements use it only up to null sets. Where
`f = 0` the quotient is `g/0 = 0` in Lean, a `μ`-null set. -/
noncomputable def score (μ : Measure ℝ) : ℝ → ℝ :=
  if h : ∃ f g : ℝ → ℝ, IsACDensity μ f g then
    fun x => h.choose_spec.choose x / h.choose x
  else fun _ => 0

end FisherInfoIneq


