-- Prove2me | Definitions.Def_FisherInfoIneq_IsACDensity
-- name    : FisherInfoIneq_IsACDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:55:52.737252+00:00
-- url     : https://prove2.me/theorems/e108389d-e98f-4ae4-8f5e-2a3eb1a93581
-- title:
--   Absolutely continuous density $f$ of a law on $\mathbb R$ with derivative $g$
-- statement:
--   Let $\mu$ be a measure on the real line and $f, g:\mathbb R\to\mathbb R$. The pair $(f,g)$ is an **absolutely continuous density of $\mu$ with derivative $g$** when
--
--   1. $f(x)\ge 0$ for every $x$;
--   2. $f$ is a density of $\mu$ with respect to Lebesgue measure: $\mu(A)=\int_A f(x)\,dx$ for every Borel set $A$;
--   3. $g$ is integrable on every bounded interval;
--   4. $f$ is the integral of $g$: for all $x, y$,
--   $$f(y)-f(x)=\int_x^y g(t)\,dt .$$
--
--   This is the setting in which the score function $\rho_X(x)=\frac{\partial}{\partial x}\ln f(x)=f'(x)/f(x)$ of eq. (3) makes sense: $f$ is the probability density of $X$ and $g=f'$ its derivative.
--
--   **Formalization Note** The continuous version $f$ of a density is unique when it exists, and $g$ is then unique Lebesgue-almost everywhere (both facts are proved in the mission's sanity checks), so nothing depends on the choice of representation.
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, eqs. (2)–(3), p.1

import Mathlib

open MeasureTheory

namespace FisherInfoIneq

/-- **Absolutely continuous density with derivative.** For a measure `μ` on `ℝ` and functions
`f g : ℝ → ℝ`, `IsACDensity μ f g` says that `f` is a probability density function of `μ` which is
(locally) absolutely continuous with derivative `g`:

1. `f x ≥ 0` for every `x`;
2. `μ = volume.withDensity (ofReal ∘ f)`, i.e. `μ(A) = ∫_A f(x) dx`;
3. `g` is integrable on every bounded interval;
4. `f(y) − f(x) = ∫_x^y g(t) dt` for all `x, y`.

Liu–Viswanath, *Two Proofs of the Fisher Information Inequality via Data Processing Arguments*,
arXiv:cs/0604028v1, eqs. (2)–(3), p.1: "the score function ρ_X is defined as
ρ_X(x) := ∂/∂x ln f(x), and f(x) is the probability density function of the random vector X".
The pair `(f, g)` is the density and its derivative `f′` used in `∂/∂x ln f = f′/f`.

**Formalization Note** The density in (3) must be differentiated; the predicate asks for an
absolutely continuous version of it, with `g` its derivative in the sense of the fundamental theorem
of calculus. Such a version is unique when it exists (a continuous function that agrees with
another continuous function Lebesgue-a.e. agrees everywhere), and then `g` is unique Lebesgue-a.e.
The paper's random vectors are scalar throughout §2; only the real-line case is formalized. -/
def IsACDensity (μ : Measure ℝ) (f g : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    (∀ x y : ℝ, IntervalIntegrable g volume x y) ∧ (∀ x y : ℝ, f y - f x = ∫ t in x..y, g t)

end FisherInfoIneq


