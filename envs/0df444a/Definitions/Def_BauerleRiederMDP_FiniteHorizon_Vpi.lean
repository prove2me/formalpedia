-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_Vpi
-- name    : BauerleRiederMDP_FiniteHorizon_Vpi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:08.189003+00:00
-- url     : https://prove2.me/theorems/1d2ddf9e-983c-455c-af20-bacfce4978ab
-- title:
--   Expected total reward $V_{n\pi}(x)$ of a policy
-- statement:
--   For $n=0,\dots,N$, a policy $\pi=(f_0,\dots,f_{N-1})$ and $x\in E$,
--
--   $$V_{n\pi}(x)=\mathbb E^\pi_{nx}\Big[\sum_{k=n}^{N-1} r_k\big(X_k,f_k(X_k)\big)+g_N(X_N)\Big].$$
--
--   This is the expected total reward from time $n$ on, when $\pi$ is used and the state at time $n$ is $x$.
--
--   **Formalization Note.** The expectation is taken against the path law `pathKernel`, the regular version of $\mathbb P^\pi(\cdot\mid X_n=x)$. It is `erealIntegral`, the difference of the Lebesgue integrals of the positive and negative parts, with values in `EReal`. Under $(A_N)$ the positive part has a finite integral, so the value lies in $[-\infty,\infty)$. $V_{n\pi}$ is not defined by the recursion of Theorem 2.3.4.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.18

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_markovRule

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel Hist erealIntegral)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- The expected total reward `V_{nπ}(x) = 𝔼^π_{nx}[∑_{k=n}^{N-1} r_k(X_k, f_k(X_k)) + g_N(X_N)]`
of the policy `π` from state `x` at time `n` (Bäuerle & Rieder (2011), p.18, PDF 33).

**Formalization Note.** `𝔼^π_{nx}` is the expectation under the law `pathKernel` of the process
started in `x` at time `n` and run to time `N` (the conditional law `ℙ^π(· | X_n = x)` of p.17,
as a regular version). `V_{nπ}` is defined from that law and is not a recursion in `T_{nf}`; the
recursion is Theorem 2.3.4. The value lies in `[-∞, ∞)` under (A_N): `erealIntegral` is
`∫ Y⁺ − ∫ Y⁻` with both parts Lebesgue integrals, never a Bochner integral, and (A_N) makes the
first finite. Only `n ≤ N` is meaningful. -/
noncomputable def Vpi {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (π : Policy M) (n : ℕ) (x : E) : EReal :=
  erealIntegral (pathKernel M n 0 (markovRule π n) (N - n) x)
    (fun h => (pathReward M.r M.g n 0 (N - n) h : EReal))

end BauerleRiederMDP.FiniteHorizon


