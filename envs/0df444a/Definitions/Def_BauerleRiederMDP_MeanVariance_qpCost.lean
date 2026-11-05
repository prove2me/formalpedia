-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanVariance_qpCost
-- name    : BauerleRiederMDP_MeanVariance_qpCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:55.173877+00:00
-- url     : https://prove2.me/theorems/dacb396a-e4ca-4688-8921-c2cd352aafbd
-- title:
--   Expected cost $\mathbb E^{\pi}_{nx}[(X_N-b)^2]$ of the auxiliary problem $QP(b)$
-- statement:
--   In the market of §4.6, a Markov portfolio policy $\pi=(f_n,\dots,f_{N-1})$ chooses at time $k$ the amounts $f_k(X_k)\in\mathbb R^d$ invested in the $d$ risky assets as a function of the current wealth $X_k$; the wealth then evolves by
--
--   $$X_{k+1}=(1+i_{k+1})\big(X_k+f_k(X_k)\cdot R_{k+1}\big),\qquad k=n,\dots,N-1,$$
--
--   where $i_{k+1}$ is the deterministic interest rate and $R_{k+1}$ the relative risk of period $k+1$. For a target $b\in\mathbb R$, a time $n\le N$ and an initial wealth $X_n=x$, the cost of $\pi$ is
--
--   $$\mathbb E^{\pi}_{nx}\big[(X_N-b)^2\big],$$
--
--   the expected squared distance of the terminal wealth from $b$. This is the objective of the auxiliary problem $QP(b)$ into which the mean-variance problem is embedded.
--
--   **Formalization Note** The terminal wealth is computed pathwise from the wealth recursion (the platform's `MVMarket.terminalWealth`) and the expectation is a Bochner integral; it is only used for policies admissible from $(n,x)$, whose terminal wealth is square integrable.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.6, problem QP(b), p.120 (PDF p.134), and its cost-minimizing MDP form, p.121 (PDF p.135)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.MeanVariance

open MDPFinance.MeanVariance

/-- The expected cost of the auxiliary problem `QP(b)` (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §4.6, p.120, PDF p.134, and p.121, PDF p.135):
for a target `b ∈ ℝ`, a time `n ≤ N`, a wealth `x ∈ E = ℝ` and a Markov policy
`π = (f_n, …, f_{N-1})`, the quantity `𝔼^π_{nx}[(X_N - b)^2]`, the expected squared distance
of the terminal wealth from `b` when the wealth at time `n` is `x` and the wealth evolves by
`X_{k+1} = (1 + i_{k+1})(X_k + f_k(X_k) · R_{k+1})`.

**Formalization Note.** The terminal wealth is the platform's `MVMarket.terminalWealth`, the
wealth recursion evaluated pathwise on the probability space `(Ω, measIP)` carrying the
independent relative risks `R_1, …, R_N`; `𝔼` is the Bochner integral. It is used only for
policies that are admissible from `(n, x)` (`MVMarket.IsAdmissibleFrom`: measurable decision
rules and a square-integrable terminal wealth), for which this integral is the true
expectation. -/
noncomputable def qpCost {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (b : ℝ)
    (n : ℕ) (x : ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) : ℝ :=
  ∫ ω, (M.terminalWealth π (M.N - n) n x ω - b) ^ 2 ∂M.measIP

end BauerleRiederMDP.MeanVariance


