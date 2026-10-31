-- Prove2me | Definitions.Def_FDivToolkit_WeibullTail
-- name    : FDivToolkit_WeibullTail
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:09.710995+00:00
-- url     : https://prove2.me/theorems/8428d77c-f8f8-41b7-9f9d-61d9ec7fecae
-- title:
--   The Weibull-type tail $\varphi\in\Theta(x^k)$
-- statement:
--   With $\varphi=-\log f$, the assumption $\varphi\in\Theta(x^k)$ means
--   $$
--   0<\liminf_{x\to\infty}\frac{\varphi(x)}{x^k}\le\limsup_{x\to\infty}\frac{\varphi(x)}{x^k}<\infty.
--   $$
--
--   It covers Weibull distributions with shape $k$, including the heavy-tailed case $k<1$, as well as exponential and Gaussian tail behaviour, and it needs no closed form for the density.
--
--   **Formalization Note** The paper's $\varphi$ is $+\infty$ where $f=0$, whereas `Real.log 0 = 0`. Finiteness of the lim sup forces $f(x)>0$ for large $x$, which is written out, and the two limits become bounds with constants.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), §3.1, p.12, and footnote 12

import Mathlib

open Filter

namespace FDivToolkit

/-- The Weibull-type tail assumption `ϕ ∈ Θ(x^k)` with `ϕ = −log f`, Kruse, Schneider & Schweizer,
SSRN 3680475 (Aug 25, 2020), §3.1, p.12, and footnote 12:
`0 < lim inf_{x→∞} ϕ(x)/x^k ≤ lim sup_{x→∞} ϕ(x)/x^k < ∞`.

**Formalization Note.** The paper's `ϕ` is `+∞` where `f = 0`, whereas `Real.log 0 = 0`. A finite
lim sup forces `f x > 0` eventually, so that positivity is written out. The two bounds with
constants `c₁ > 0` and `c₂` are the lim inf and lim sup conditions. -/
def WeibullTail (f : ℝ → ℝ) (k : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ᶠ x in atTop,
    0 < f x ∧ c₁ * x ^ k ≤ -Real.log (f x) ∧ -Real.log (f x) ≤ c₂ * x ^ k

end FDivToolkit


