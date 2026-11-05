-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanVariance_qpValue
-- name    : BauerleRiederMDP_MeanVariance_qpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:24.482068+00:00
-- url     : https://prove2.me/theorems/b6a0575b-2c6a-4b08-bf2f-8e51d1d0115f
-- title:
--   Value functions $V_n$ of the auxiliary problem $QP(b)$
-- statement:
--   For a target $b\in\mathbb R$, the value functions of the cost-minimizing Markov decision problem $QP(b)$ of §4.6 are
--
--   $$V_n(x):=\inf_{\pi}\ \mathbb E^{\pi}_{nx}\big[(X_N-b)^2\big],\qquad x\in\mathbb R,\ 0\le n\le N,$$
--
--   the infimum being taken over all Markov portfolio policies $\pi=(f_n,\dots,f_{N-1})$ with measurable decision rules $f_k:\mathbb R\to\mathbb R^d$ (every investment is allowed, $D_k(x)=\mathbb R^d$), starting with wealth $x$ at time $n$. $V_0(x_0)$ is the value of $QP(b)$.
--
--   **Formalization Note** The infimum runs over the policies admissible from $(n,x)$, i.e. those with measurable decision rules and a square-integrable terminal wealth. This set always contains the policy that invests nothing, and every cost is nonnegative, so the real infimum is a genuine infimum. A policy with infinite cost cannot lower the infimum, so excluding it changes no value.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.6, p.121 (PDF p.135); definition of the value function V_n and of an optimal policy, §2.1, p.18 (PDF p.33)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_BauerleRiederMDP_MeanVariance_qpCost

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.MeanVariance

open MDPFinance.MeanVariance

/-- The value functions `V_n` of the auxiliary problem `QP(b)` (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), §4.6, p.121, PDF p.135; the book treats
`QP(b)` "as a cost minimizing problem"): `V_n(x) := inf_π 𝔼^π_{nx}[(X_N - b)^2]`, the minimal
expected squared distance of the terminal wealth from `b` over all Markov policies
`π = (f_n, …, f_{N-1})`, starting with wealth `x` at time `n`.

**Formalization Note.** The infimum runs over the *subtype* of policies admissible from
`(n, x)` (measurable decision rules `ℝ → ℝ^d`, every action allowed since `D_n(x) = ℝ^d`, and a
square-integrable terminal wealth). This subtype is never empty (the policy that invests nothing
is admissible: its terminal wealth is deterministic) and the costs are `≥ 0`, so the real
infimum is the genuine infimum and no junk value of `⨅` on an empty or unbounded set arises.
A policy whose terminal wealth is not square integrable has cost `+∞` in the book and therefore
never lowers the infimum, so leaving it out changes no value. -/
noncomputable def qpValue {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (b : ℝ)
    (n : ℕ) (x : ℝ) : ℝ :=
  ⨅ π : {π : ℕ → ℝ → (Fin d → ℝ) // M.IsAdmissibleFrom n x π}, qpCost M b n x π.1

end BauerleRiederMDP.MeanVariance


