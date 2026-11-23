-- Prove2me | Definitions.Def_LargeBSP_Homog_Supplement_Extremes
-- name    : LargeBSP_Homog_Supplement_Extremes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T16:54:10.775799+00:00
-- url     : https://prove2.me/theorems/d20cf1e6-aabd-46ea-8bff-bca368a4014a
-- title:
--   Appendix B and Lemma B1, p. A13 — endpoint η_F, slowly varying tail, a_N, upper order statistics, limit law
-- statement:
--   Extreme-value objects for valuations with distribution function $F_X$ and finite upper endpoint.
--
--   1. **Endpoint.** $\eta_F=\sup\{x:F_X(x)<1\}$.
--   2. **Slow variation.** $L$ is slowly varying if $L(tx)/L(x)\to1$ as $x\to\infty$ for every $t>0$.
--   3. **Endpoint tail.** $\alpha>0$, $L$ is slowly varying, and for all large $x$
--   $$1-F_X(\eta_F-1/x)=x^{-\alpha}L(x).$$
--   4. **Scale.** $a_N=\eta_F-F_X^{-1}(1-1/N)$.
--   5. **Order statistic.** $X_{(N-k)}$ is the $(k+1)$-st largest of the first $N$ valuations, for $k<N$.
--   6. **Limit law.** With $\Psi_\alpha(x)=e^{-(-x)^\alpha}$ for $x\le0$, $\Psi_\alpha(x)=1$ for $x>0$, and $\Gamma_{m}(y)=\frac1{(m-1)!}\int_y^\infty e^{-t}t^{m-1}dt$, it is the distribution function $x\mapsto\Gamma_{k+1}(-\log\Psi_\alpha(x))$.
--
--   These are the normalization and limit in Lemma B1 and the standing tail assumption of Theorem B1.
--
--   **Formalization Note** The order statistic is read off the item rank of the bundle-size pricing model and is $0$ for $k\ge N$, which is irrelevant as $N\to\infty$. Slow variation is the paper's ratio condition, with no positivity requirement.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, Appendix B and Lemma B1, p. A13

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- The finite upper endpoint. Used only with a nonempty bounded defining set. -/
noncomputable def endpoint (ν : Measure ℝ) : ℝ := sSup {x : ℝ | cdf ν x < 1}

/-- The normalization in Lemma B1; only the eventual N>k matters. -/
noncomputable def extremeScale (ν : Measure ℝ) (N : ℕ) : ℝ :=
  endpoint ν - quantile (cdf ν) (1 - 1 / (N : ℝ))

/-- The (k+1)st largest item. This sum has exactly one summand when k<N.
The default outside that range is zero; k is fixed and N tends to infinity. -/
noncomputable def upperOrder (x : ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∑ i ∈ (Finset.range N).filter (fun i => rank x N i = k), x i

/-- Upper incomplete gamma tail of integer order k+1, written with the source's integral. -/
noncomputable def gammaTail (k : ℕ) (y : ℝ) : ℝ :=
  (1 / (Nat.factorial k : ℝ)) * ∫ t in Set.Ioi y, Real.exp (-t) * t ^ k

/-- Reversed Weibull cdf. -/
noncomputable def reversedWeibull (α x : ℝ) : ℝ :=
  if x ≤ 0 then Real.exp (-((-x) ^ α)) else 1

/-- Gamma transform Γ_(k+1)(-log Ψ_α(x)), with the value 0 at Ψ_α=0.
For finite x, α>0, Ψ_α is positive; at x≥0 the cdf is 1. -/
noncomputable def extremeCdf (α : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  gammaTail k (-Real.log (reversedWeibull α x))

/-- A slowly varying function (Appendix B, p. A13): `L(tx)/L(x) → 1` as `x → ∞` for every `t > 0`.
No sign or regularity condition is part of the page's definition. -/
def SlowlyVarying (L : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → Tendsto (fun x : ℝ => L (t * x) / L x) atTop (𝓝 1)

/-- Appendix B's endpoint regular variation, required eventually (near the endpoint). -/
def EndpointTail (ν : Measure ℝ) (α : ℝ) (L : ℝ → ℝ) : Prop :=
  0 < α ∧ SlowlyVarying L ∧
  ∀ᶠ x : ℝ in atTop, 1 - cdf ν (endpoint ν - 1 / x) = x ^ (-α) * L x

end LargeBSP.Homog.Supplement


