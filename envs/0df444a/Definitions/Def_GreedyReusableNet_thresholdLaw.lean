-- Prove2me | Definitions.Def_GreedyReusableNet_thresholdLaw
-- name    : GreedyReusableNet_thresholdLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:01.237032+00:00
-- url     : https://prove2.me/theorems/ae14d937-d2f8-49cc-8bb3-cbe7a24a5bf9
-- title:
--   Random-threshold law $G(x)=\frac{1+\ln(x/a)}{1+\ln(b/a)}$
-- statement:
--   For $0<a\le b$, the **threshold law** is the probability distribution on $[a,b]$ with distribution function
--   $$G(x)=\frac{1+\ln(x/a)}{1+\ln(b/a)},\qquad x\in[a,b],$$
--   equal to $0$ below $a$ and $1$ from $b$ on. It has an atom of mass $1/(1+\ln(b/a))$ at $a$ and density $1/((1+\ln(b/a))\,x)$ on $(a,b]$. With $a=r_{\min}$, $b=r_{\max}$ it is the law $G$ of Algorithm 3; with $a=\bar r_{\min}$, $b=\bar r_{\max}$ the law $\bar G$ of Algorithm 4.
--
--   **Formalization Note** Defined as atom plus density; the mission's verification file proves that it is a probability measure whose distribution function is $G$ on $[a,b]$.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.1, Algorithms 3 and 4, step 1, p.17

import Mathlib

open MeasureTheory

namespace GreedyReusableNet

/-- **The random-threshold law** with cumulative distribution function
`G(x) = (1 + ln(x/a))/(1 + ln(b/a))` for `x ∈ [a, b]` (Simchi-Levi, Zheng & Zhu, SSRN 3981123,
Algorithm 3 step 1, p.17, with `a = r_min`, `b = r_max`, `b/a = R`; Algorithm 4 step 1 with
`a = r̄_min`, `b = r̄_max`).

It is `G(x) = 0` below `a` and `1` from `b` on, so the law is an atom of mass
`G(a) = 1/(1 + ln(b/a))` at `a` plus the density `G'(x) = 1/((1 + ln(b/a)) x)` on `(a, b]`.

**Formalization Note** Written as atom plus density rather than through a Stieltjes function;
for `0 < a ≤ b` it is a probability measure with distribution function `G` on `[a, b]` (checked
in the mission's verification file). If `a = b` it is the point mass at `a`. -/
noncomputable def thresholdLaw (a b : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / (1 + Real.log (b / a))) • Measure.dirac a +
    (volume.restrict (Set.Ioc a b)).withDensity
      (fun x => ENNReal.ofReal (1 / ((1 + Real.log (b / a)) * x)))

end GreedyReusableNet


