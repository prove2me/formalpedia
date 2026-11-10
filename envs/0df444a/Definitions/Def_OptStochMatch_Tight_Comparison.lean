-- Prove2me | Definitions.Def_OptStochMatch_Tight_Comparison
-- name    : OptStochMatch_Tight_Comparison
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:54:19.880346+00:00
-- url     : https://prove2.me/theorems/254a41d1-a928-46b7-9e9b-404e882e632e
-- title:
--   The comparison policy value $q(t,h)$
-- statement:
--   From time $t$, with $h$ units of work done and an $\mathrm{Exp}(1)$ residual demand $E$, serve a job at rate $x'=x+1$ until the deadline or completion. With $\psi$ the solution of $\psi'=\psi+1$, $\psi(t)=h$, the additional work is $\min(E,\psi(1)-h)$ and $q(t,h)=\mathbb E[\min(E,\psi(1)-h)]$.
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), §4.2, p. 15 (PDF 16)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Laws

/-!
Dütting, Feldman, Molina, *Optimal Online Stochastic Matching*, arXiv:2610.19866
(sha256 0458ce2e…), §4.2, p. 15 (PDF 16).

**The one-job comparison policy.** "Consider a job `i ∈ [m]` that is unfinished at time `t`,
after receiving `h` units of work. From this time onward, serve it at a rate
`s_i(t) = x_i'(t) = x_i(t) + 1`, until either the deadline or its completion. […] Let `q(t, h)`
denote the expected additional work processed by time 1 under this policy. […] The remaining
demand is unit exponential."

The work trajectory `ψ` solves `ψ' = ψ + 1`, `ψ(t) = h` (a linear ODE with a unique solution);
without the demand limit it adds `ψ(1) − h` units of work on `[t, 1]`. With a residual demand
`E ∼ Exp(1)`, the additional work is `min(E, ψ(1) − h)`, and `q(t, h) = E[min(E, ψ(1) − h)]`.
-/

namespace OptStochMatch.Tight

open MeasureTheory ProbabilityTheory

/-- The comparison work trajectory from state `(t, h)`: the solution of `ψ' = ψ + 1` with
`ψ(t) = h` (chosen by `Classical.epsilon`; the solution exists and is unique). -/
noncomputable def compTraj (t h : ℝ) : ℝ → ℝ :=
  Classical.epsilon fun ψ : ℝ → ℝ => ψ t = h ∧ ∀ v, HasDerivAt ψ (ψ v + 1) v

/-- `q(t, h)`: the expected additional work by time `1` of the comparison policy started at
time `t` with `h` units of work already processed, the residual demand being `Exp(1)`. -/
noncomputable def qComp (t h : ℝ) : ℝ :=
  ∫ e, min e (compTraj t h 1 - h) ∂expOne

end OptStochMatch.Tight


