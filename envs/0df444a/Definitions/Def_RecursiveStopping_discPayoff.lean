-- Prove2me | Definitions.Def_RecursiveStopping_discPayoff
-- name    : RecursiveStopping_discPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:00.560876+00:00
-- url     : https://prove2.me/theorems/319cda20-04fa-43bf-b82f-956f9f5531dd
-- title:
--   Discounted payoff $e^{-r\tau}G(X^x_\tau)$ with value $0$ on $\{\tau=\infty\}$
-- statement:
--   Given a discount rate $r$, a gain $G:S\to[0,\infty]$, a flow $X$, a starting point $x$ and a random time $\tau:\Omega\to[0,\infty]$, the **discounted payoff** is
--
--   $$
--   e^{-r\tau}G(X^x_\tau)(\omega):=\begin{cases}e^{-r\tau(\omega)}\,G\big(X^x_{\tau(\omega)}(\omega)\big),&\tau(\omega)<\infty,\\[2pt]0,&\tau(\omega)=\infty.\end{cases}
--   $$
--
--   The value on $\{\tau=\infty\}$ is the paper's convention $G(X^x_\tau)\mathbf 1_{\{\tau=\infty\}}=\limsup_{t\to\infty}G(X^x_t)$ multiplied by the vanishing discount factor. This is the reward inside the stopping problems (3) and (15).
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2, p.6 (convention at τ = ∞); (3), p.7; (15), p.10

import Mathlib

open scoped NNReal ENNReal

namespace RecursiveStopping

/-- The discounted payoff `e^{−rτ} G(X^x_τ)` of stopping the flow started at `x` at the random
time `τ` (Colaneri & De Angelis, arXiv:1905.02650v4, (3), p.7 and (15), p.10), valued in
`[0, ∞]`.

On `{τ = ∞}` the value is `0`: the paper's convention (p.6) sets `G(X^x_τ)1_{τ=∞} =
lim sup_{t→∞} G(X^x_t)` and the discount factor `e^{−rτ}` vanishes at `τ = ∞`.

**Formalization Note** The gain `G` is `[0, ∞]`-valued, so the payoff is a non-negative
extended real and its expectation is a `lintegral`. -/
noncomputable def discPayoff {S Ω : Type*} (r : ℝ) (G : S → ℝ≥0∞) (X : S → ℝ≥0 → Ω → S)
    (x : S) (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  if τ ω = ⊤ then 0
  else ENNReal.ofReal (Real.exp (-r * (τ ω).toReal)) * G (X x (τ ω).toNNReal ω)

end RecursiveStopping


