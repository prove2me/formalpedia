-- Prove2me | Definitions.Def_FisherInfoIneq_mmse
-- name    : FisherInfoIneq_mmse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:55:54.753258+00:00
-- url     : https://prove2.me/theorems/9c75b959-38a9-4b50-875b-421979dab11d
-- title:
--   Conditional variance $\mathrm{VAR}[W\mid X]=\mathbb E[(W-\mathbb E[W\mid X])^2]$
-- statement:
--   Let $W$ be a real random variable and $X$ a random variable with values in any measurable space, on a probability space $(\Omega,P)$. The **conditional variance** (minimum mean-square error of estimating $W$ from $X$) is the number
--   $$\mathrm{VAR}[W\mid X]=\mathbb E\big[(W-\mathbb E[W\mid X])^2\big]\in[0,\infty],$$
--   where $\mathbb E[W\mid X=x]=\int w\,P_{W\mid X=x}(dw)$ is the mean of the (regular) conditional distribution of $W$ given $X=x$, evaluated at $x=X$. For two observations, $\mathrm{VAR}[W\mid X_1,X_2]$ conditions on the pair $(X_1,X_2)$.
--
--   It is a number, not the conditional-variance random variable $\mathbb E[(W-\mathbb E[W|X])^2\mid X]$; it is the quantity in the data-processing inequality (13), in Lemma 1 and in (24)–(28).
--
--   **Formalization Note** The value is a lower Lebesgue integral in $[0,\infty]$, so no square-integrability is needed for it to be meaningful. The conditional mean is the mean of the conditional law (`condDistrib`), as in the paper's $\mathbb E[N\mid X=x]$ (eq. (33)); it needs no integrability of $W$ and agrees almost surely with the conditional expectation $P[W\mid\sigma(X)]$ when $W$ is integrable. Where a conditional law is not integrable its Bochner mean is $0$, but there $\mathbb E[W^2\mid X=x]=\infty$ too, so the value is $\infty$ whenever this happens with positive probability.
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, the sentence after eq. (13), p.3

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FisherInfoIneq

/-- **Conditional variance `VAR[W|X]` (minimum mean-square error).** For a real random variable
`W` and a random variable `X` with values in any measurable space `β` on a probability space
`(Ω, P)`,
$$\mathrm{VAR}[W\mid X]=\mathbb E\big[(W-\mathbb E[W\mid X])^2\big]\in[0,\infty],$$
where the conditional mean `E[W | X = x] = ∫ w d(P_{W|X=x})(w)` is the mean of the conditional law
of `W` given `X = x` (`condDistrib W X P`, the regular conditional distribution), evaluated at
`x = X`. This is a **number** (the expected conditional variance), not the conditional-variance
random variable. For two variables, `VAR[W|X₁, X₂]` is `mmse P W (fun ω => (X₁ ω, X₂ ω))`.

Liu–Viswanath, arXiv:cs/0604028v1, the sentence after eq. (13), p.3:
"where VAR[W|X] := E[(W − E[W|X])²]"; the paper writes the conditional mean as
`E[N|X = x]` (eq. (33), p.5).

**Formalization Note**
1. The value is an `ℝ≥0∞` lower integral, so no square-integrability is needed for it to be
   meaningful.
2. The conditional mean is the mean of the conditional law, as in the paper's `E[N|X = x]`; it
   needs no integrability of `W` itself (e.g. for Cauchy `N` and Gaussian `W`, the conditional law
   of `N` given `N + W = x` has Gaussian tails). When `W` is integrable it agrees `P`-a.e. with
   Mathlib's conditional expectation `P[W | σ(X)]` (`condExp_ae_eq_integral_condDistrib'`).
   Where a conditional law is not integrable the Bochner integral is `0`; there
   `E[W² | X = x] = ∞` as well, so `VAR` is `∞` whenever that happens on a set of positive
   probability, the classical value. -/
noncomputable def mmse {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsFiniteMeasure P] (W : Ω → ℝ) (X : Ω → β) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((W ω - ∫ w, w ∂(condDistrib W X P (X ω))) ^ 2) ∂P

end FisherInfoIneq


