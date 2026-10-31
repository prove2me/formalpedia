-- Prove2me | Definitions.Def_DynTradeFinance_Clocks
-- name    : DynTradeFinance_Clocks
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:23.269139+00:00
-- url     : https://prove2.me/theorems/2411caf6-dc04-454f-95e3-dc87a3eb1cb5
-- title:
--   The independent exponential clocks $\tilde T_1\sim\mathrm{Exp}(1)$, $\tilde T_2\sim\mathrm{Exp}(\mu)$, $\tilde d\sim\mathrm{Exp}(\lambda)$
-- statement:
--   Given the model parameters, three real random variables $\tilde T_1,\tilde T_2,\tilde d$ on a probability space $(\Omega,\mathbb P)$ are **the model's clocks** if
--
--   1. the Step-1 duration $\tilde T_1$ is exponentially distributed with rate $1$;
--   2. the Step-2 duration $\tilde T_2$ is exponentially distributed with rate $\mu$;
--   3. the information-verification delay $\tilde d$ is exponentially distributed with rate $\lambda$;
--   4. $\tilde T_1,\tilde T_2,\tilde d$ are mutually independent.
--
--   The order passes Step 1 at time $\tilde T_1$, completes at $\tilde T_1+\tilde T_2$, and the bank verifies that Step 1 was passed at $\tilde T_1+\tilde d$. Every expectation in the mission is taken with respect to these clocks.
--
--   **Formalization Note** The laws are stated with Mathlib's `HasLaw` and `expMeasure r` (the exponential law with rate $r$), independence with `iIndepFun` of the triple. The passing of Steps 1 and 2 is not modelled by random variables: as in the paper's formulas, the passing probabilities $p_1,p_2$ enter as weights, which is legitimate because passing is independent of the durations.
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), §3, pp. 8–9 (duration uncertainty, information delay)

import Mathlib
import Definitions.Def_DynTradeFinance_Params

open MeasureTheory ProbabilityTheory

namespace DynTradeFinance

/-- **The three random clocks of the model**, Lee, Tang, Yang, Zhang, SSRN 3632563, §3, pp. 8–9:
on a probability space `(Ω, P)`, the Step-1 duration `T₁ ∼ Exp(1)` (rate normalized to 1), the
Step-2 duration `T₂ ∼ Exp(μ)`, and the information-verification delay `d ∼ Exp(λ)`, mutually
independent ("duration uncertainty and passing uncertainty are assumed to be independent", p. 8;
"information delay is assumed to be independent of processing time", p. 9).

**Formalization Note.** The clocks live on an arbitrary measurable space with laws given by
`HasLaw` (Mathlib's `expMeasure r` is the exponential law with rate `r`) and joint independence
`iIndepFun` of the triple. The passing events of Steps 1 and 2 are not random variables here:
they enter the model's formulas as the probability weights `p₁`, `p₂`, exactly as in the
paper's displays (3)–(5), (8), (58), which is legitimate because passing is independent of the
durations. -/
structure Clocks (θ : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T₁ T₂ d : Ω → ℝ) : Prop where
  law₁ : HasLaw T₁ (expMeasure 1) P
  law₂ : HasLaw T₂ (expMeasure θ.μ) P
  lawd : HasLaw d (expMeasure θ.lam) P
  indep : iIndepFun ![T₁, T₂, d] P

end DynTradeFinance


