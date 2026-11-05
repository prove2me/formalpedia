-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_twAdmissible
-- name    : BauerleRiederMDP_PartialObs_twAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:03:14.820932+00:00
-- url     : https://prove2.me/theorems/c5617beb-906b-4d8d-aa21-2eaed6ce38af
-- title:
--   Admissible strategies of the terminal wealth problem (6.2)
-- statement:
--   In the terminal wealth problem (6.2) with horizon $N$, initial wealth $x$ and constant interest rate $i$, a portfolio strategy $\varphi=(\varphi_0,\dots,\varphi_{N-1})$ is admissible if
--
--   1. each $\varphi_n$ is a measurable function of the observed returns $(R_1,\dots,R_n)$, i.e. $\varphi$ is adapted to $\mathcal F^S_n=\sigma(R_1,\dots,R_n)$;
--   2. the terminal wealth satisfies $X^\varphi_N\in\operatorname{dom}U$ almost surely, under the market law in which $Y_0\sim Q_0$.
--
--   No Markov or filter structure is required of $\varphi$.
-- source:
--   Bäuerle & Rieder (2011), §6.1, (6.2), p.176 (PDF 189)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_returnLaw
import Definitions.Def_BauerleRiederMDP_PartialObs_wealth

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **Admissible strategies of the terminal wealth problem (6.2).**
Bäuerle & Rieder (2011), §6.1, p.176 (PDF 189): the portfolio strategy `φ` is `(F_n)`-adapted,
`F_n = F^S_n = σ(R_1, …, R_n)`, and `X^φ_N ∈ dom U` IP-a.s.

`twAdmissible M i domU N x φ`: each `φ_n`, `n < N`, is a measurable function of the observed
returns `(R_1, …, R_n)`, and the terminal wealth `X^φ_N` from initial wealth `x` and constant
interest rate `i` lies in `domU` almost surely under the market law `M.returnLaw M.Q0 N` (hidden
state started from the prior `Q_0`). -/
def twAdmissible {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) (i : ℝ)
    (domU : Set ℝ) (N : ℕ) (x : ℝ) (φ : (n : ℕ) → (Fin n → Fin d → ℝ) → Fin d → ℝ) : Prop :=
  (∀ n < N, Measurable (φ n)) ∧
    ∀ᵐ r ∂M.returnLaw M.Q0 N, wealth (fun _ => i) x φ N r ∈ domU

end BauerleRiederMDP.PartialObs


