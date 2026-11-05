-- Prove2me | Definitions.Def_BauerleRiederMDP_Stopping_IsOptimalUpTo
-- name    : BauerleRiederMDP_Stopping_IsOptimalUpTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:44.754357+00:00
-- url     : https://prove2.me/theorems/0c1ba738-1719-40a8-a23b-4404f4081ea1
-- title:
--   Optimality for the $N$-stage stationary stopping problem
-- statement:
--   A stopping time $\tau$ is optimal for the $N$-stage stationary stopping problem if $\tau\le N$ and, for all $x\in E$,
--
--   $$
--   \mathbb E_x[R_\tau]=J_N(x):=\sup_{\tau'\le N}\mathbb E_x\Big[\sum_{k=0}^{\tau'-1}\beta^kc(X_k)+\beta^{\tau'}g(X_{\tau'})\Big].
--   $$
--
--   This is the finite-horizon notion of optimality used by Theorems 10.1.5 and 10.2.7.
--
--   **Formalization Note** The bound $\tau\le N$ holds on every path, not just almost surely. Replacing $\tau$ by $\tau\wedge N$ changes no reward, so the values are the same.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §10.1, eq. (10.1), p.304, and p.307

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory
open MDPFinance.OptimalStopping

namespace BauerleRiederMDP.Stopping

/-- `τ` is **optimal for the `N`-stage stationary stopping problem**: a stopping time with `τ ≤ N`
and `J_N(x) = sup_{τ' ≤ N} 𝔼_x[R_{τ'}] = 𝔼_x[R_τ]` for all `x`. Bäuerle & Rieder, Markov Decision
Processes with Applications to Finance (2011), §10.1, pp.304 and 307 (PDF 312 and 315).

**Formalization Note.** `τ ≤ N` holds everywhere rather than `ℙ_x`-a.s. for all `x` as on the page;
`τ ∧ N` is a stopping time with the same rewards, so the two classes give the same values. -/
def IsOptimalUpTo {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (N : ℕ) (tau : (ℕ → E) → ℕ∞) : Prop :=
  IsStopTime tau ∧ (∀ w, tau w ≤ (N : ℕ∞)) ∧
    ∀ x : E, P.EReward Pr tau x = P.valueUpTo Pr N x

end BauerleRiederMDP.Stopping


