-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_VHist
-- name    : BauerleRiederMDP_FiniteHorizon_VHist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:01.219192+00:00
-- url     : https://prove2.me/theorems/84da721f-7a00-4895-b29a-484cd9a00422
-- title:
--   Value $V_{n\pi}(h_n)$ of a history-dependent policy
-- statement:
--   For a history-dependent policy $\pi\in\Pi_N$ and a history $h_n=(x_0,a_0,x_1,\dots,x_n)\in H_n$, $V_{n\pi}(h_n)$ is the conditional expectation of the total reward in $[n,N]$ given $h_n$:
--
--   $$V_{n\pi}(h_n)=\mathbb E^\pi\Big[\sum_{k=n}^{N-1} r_k(X_k,A_k)+g_N(X_N)\,\Big|\,H_n=h_n\Big].$$
--
--   **Formalization Note.** The book gives no formula. The conditional law is the continuation of $h_n$ under $\pi$ given by `pathKernel`. Rewards earned before time $n$ are not counted.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.18

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_histRule

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel Hist HistPolicy erealIntegral)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- `V_{nπ}(h_n)` for a history-dependent policy `π ∈ Π_N` (Bäuerle & Rieder (2011), p.18, PDF 33):
"the conditional expectation of the total reward in `[n, N]`, given the history `h_n ∈ H_n`".

**Formalization Note.** The book gives no formula. The conditional law given `h_n` is taken to be
the `pathKernel` continuation of `h_n` under `π`, the regular version the construction of p.17
provides; the total reward counts the times `n, …, N-1` and the terminal reward at `N`, and not
the rewards earned before `n`. -/
noncomputable def VHist {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (π : HistPolicy M) (n : ℕ) (h : Hist E A n) : EReal :=
  erealIntegral (pathKernel M n n (histRule π n) (N - n) h)
    (fun p => (pathReward M.r M.g n n (N - n) p : EReal))

end BauerleRiederMDP.FiniteHorizon


