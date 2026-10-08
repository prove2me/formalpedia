-- Prove2me | Definitions.Def_ShapiroSDDP_Convergence_Sampling
-- name    : ShapiroSDDP_Convergence_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:26.662761+00:00
-- url     : https://prove2.me/theorems/7cbf52e3-1835-4fa4-bcdb-6a5409fc8e14
-- title:
--   The subsampling procedure of the forward step: i.i.d. uniform draws from the SAA scenarios
-- statement:
--   In the forward step of SDDP applied to the SAA problem, the scenarios are drawn from the scenarios of the SAA problem "with replacement" (p. 4) and "independently of each other" (p. 11).
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $M\ge1$ the number of forward scenarios per iteration. A family $X_{k,i}:\Omega\to\mathcal S$, $k\in\mathbb N$, $i=1,\dots,M$, of random scenarios, where $\mathcal S$ is the finite set of the $N$ SAA scenarios, follows the **subsampling procedure** if
--
--   1. each $X_{k,i}$ is measurable;
--   2. the whole family $(X_{k,i})_{(k,i)}$ is mutually independent;
--   3. each $X_{k,i}$ is uniformly distributed: $P(X_{k,i}=s)=1/N$ for every scenario $s$.
--
--   This is the sampling hypothesis of Proposition 3.1.
--
--   **Formalization Note** The scenario set carries its (discrete) product σ-algebra. The draws are indexed by the pairs $(k,i)\in\mathbb N\times\{0,\dots,M-1\}$ and independence is `iIndepFun` over that index. Uniformity is the paper's empirical distribution with equal weights $1/N=\prod_t 1/N_t$.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, p. 4 (sampling with replacement), p. 8 (M random realizations), p. 11 (independent forward scenarios)

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model

open MeasureTheory ProbabilityTheory

namespace ShapiroSDDP.Convergence

/-- The subsampling procedure of the forward step (p. 4, p. 8, p. 11): on a probability space
`(Ω, P)`, the `M` forward scenarios `X k i`, `i < M`, of every iteration `k` are random variables
with values in the scenarios of the SAA problem (with the discrete σ-algebra), mutually independent
over all pairs `(k, i)` (sampling with replacement, independently of each other), and each uniformly
distributed: every scenario has probability `1 / N`, where `N` is the number of scenarios. -/
def IsUniformIID (I : Instance) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {M : ℕ}
    (X : ℕ → Fin M → Ω → Scen I) : Prop :=
  (∀ k i, Measurable (X k i)) ∧
    iIndepFun (fun p : ℕ × Fin M => X p.1 p.2) P ∧
    ∀ k i (s : Scen I), P {w | X k i w = s} = (Fintype.card (Scen I) : ENNReal)⁻¹

end ShapiroSDDP.Convergence


