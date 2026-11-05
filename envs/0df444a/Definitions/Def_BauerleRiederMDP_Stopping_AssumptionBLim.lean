-- Prove2me | Definitions.Def_BauerleRiederMDP_Stopping_AssumptionBLim
-- name    : BauerleRiederMDP_Stopping_AssumptionBLim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:36.601194+00:00
-- url     : https://prove2.me/theorems/df8a2894-1975-4f77-b578-bbc36663dfb7
-- title:
--   Assumption (B) in the limit form of Remark 10.2.1 a)
-- statement:
--   For all $x\in E$: the first part of Assumption (B),
--
--   $$
--   \sup_{\tau<\infty}\mathbb E_x\Big[\sum_{k=0}^{\tau-1}\beta^kc^+(X_k)+\beta^\tau g^+(X_\tau)\Big]<\infty,
--   $$
--
--   together with
--
--   $$
--   \lim_{n\to\infty}\mathbb E_x[R_{\tau\wedge n}]=\mathbb E_x[R_\tau]\qquad\text{for all }\tau<\infty.
--   $$
--
--   Remark 10.2.1 a) of the book states this as equivalent to Assumption (B), whose second part has only $\liminf_n\mathbb E_x[R_{\tau\wedge n}]\ge\mathbb E_x[R_\tau]$. It is strictly stronger; this condition is what the book's proofs of the optimality of stationary stopping rules actually use.
--
--   **Formalization Note** Stated as (B) conjoined with the limit identity, which is the same condition since the identity implies the $\liminf$ inequality.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 10.2.1 a), p.310

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology
open MDPFinance.OptimalStopping

namespace BauerleRiederMDP.Stopping

/-- The **limit form of Assumption (B)** printed in Bäuerle & Rieder, Markov Decision Processes
with Applications to Finance (2011), Remark 10.2.1 a), p.310 (PDF 318): the first part of (B), and
`lim_{n→∞} 𝔼_x[R_{τ∧n}] = 𝔼_x[R_τ]` for all `τ < ∞`.

**Formalization Note.** The Remark calls this equivalent to (B). It is strictly stronger: see the
Differences section of Theorem 10.2.7. Stated as (B) plus the limit identity; the identity implies
the `liminf` inequality of (B), so this is exactly the Remark's condition. As in the platform's (B),
`τ` is finite `ℙ_x`-a.s. for the `x` at hand; a stopping time with this property agrees `ℙ_x`-a.s.
with one finite under every `ℙ_y` (set it to `0` where `y ↦ ℙ_y(τ < ∞) ≠ 1` at `X_0`). -/
def AssumptionBLim {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) : Prop :=
  P.AssumptionB Pr ∧
    ∀ (x : E) (tau : (ℕ → E) → ℕ∞), IsStopTime tau → Pr x {w | tau w = ⊤} = 0 →
      Tendsto (fun n : ℕ => P.EReward Pr (truncTime tau n) x) atTop (𝓝 (P.EReward Pr tau x))

end BauerleRiederMDP.Stopping


