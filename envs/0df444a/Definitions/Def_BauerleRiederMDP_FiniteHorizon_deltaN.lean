-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_deltaN
-- name    : BauerleRiederMDP_FiniteHorizon_deltaN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:05.955616+00:00
-- url     : https://prove2.me/theorems/06af88c2-d689-4d2d-bef2-471ea2cf3a39
-- title:
--   Maximal expected positive reward $\delta^N_n(x)$
-- statement:
--   For $n=0,\dots,N$ and $x\in E$,
--
--   $$\delta^N_n(x)=\sup_\pi\mathbb E^\pi_{nx}\Big[\sum_{k=n}^{N-1} r_k^+\big(X_k,f_k(X_k)\big)+g_N^+(X_N)\Big],$$
--
--   where $y^+=\max\{0,y\}$.
--
--   This quantity dominates $V_n$ and is the object of the Integrability Assumption.
--
--   **Formalization Note.** The integrand is nonnegative, so the expectation is a Lebesgue integral with values in $[0,\infty]$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.17

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
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- `δ^N_n(x) := sup_π 𝔼^π_{nx}[∑_{k=n}^{N-1} r_k⁺(X_k, f_k(X_k)) + g_N⁺(X_N)]` (Bäuerle & Rieder
(2011), p.17, PDF 32), the largest expected total positive reward from state `x` at time `n`.

**Formalization Note.** The integrand is nonnegative, so the expectation is a Lebesgue integral
with values in `[0, ∞]`, and the supremum is taken there. -/
noncomputable def deltaN {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (n : ℕ) (x : E) : ENNReal :=
  ⨆ π : Policy M, ∫⁻ h, ENNReal.ofReal
    (pathReward (fun k xa => max (M.r k xa) 0) (fun y => max (M.g y) 0) n 0 (N - n) h)
    ∂(pathKernel M n 0 (markovRule π n) (N - n) x)

end BauerleRiederMDP.FiniteHorizon


