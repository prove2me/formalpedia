-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_relaxedStage
-- name    : BauerleRiederMDP_PDMDP_JumpModel_relaxedStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:53.818298+00:00
-- url     : https://prove2.me/theorems/0cb1ec8c-ee7c-4a79-a6f8-095888ab6fba
-- title:
--   The embedded models $(E,A,D,Q',r')$ with and without relaxed controls, $J_\infty$ and $J^{rel}_\infty$
-- statement:
--   For $x\in E$ and $\alpha\in\mathcal R$,
--   $$
--   r'(x,\alpha)=\int_0^\infty e^{-(\beta+\lambda)t}\int r(\varphi^\alpha_t(x),u)\,\alpha_t(du)\,dt,
--   $$
--   $$
--   Q'(B|x,\alpha)=\lambda\int_0^\infty e^{-(\beta+\lambda)t}\int Q(B|\varphi^\alpha_t(x),u)\,\alpha_t(du)\,dt.
--   $$
--   On deterministic controls these are (8.4) and (8.5). The module defines the two embedded models, and
--   $$
--   J_\infty(x)=\sup_{(f_n)}J_\infty(f_n)(x),\qquad J^{rel}_\infty(x)=\sup_{(f_n)}J_\infty(f_n)(x),
--   $$
--   the first over policies $f_n:E\to A$, the second over relaxed policies $f_n:E\to\mathcal R$. The discrete-time discount factor is $1$, and the cemetery state is skipped.
--
--   The maximal reward operator $T$ of the book is the operator of these models.
--
--   **Formalization Note** The integrals are written with the discounted occupation measure of the flow on $E\times U$. The sanity file proves the display for $Q'$ from it.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), (8.4)–(8.5), p.247, p.248, (8.7), p.250, and p.251

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel

open MeasureTheory ProbabilityTheory
open MDPFinance.PDMDP (erealIntegral)

namespace BauerleRiederMDP.PDMDP

namespace JumpModel

variable {E U : Type*} [TopologicalSpace E] [MeasurableSpace E] [MeasurableSpace U]

/-- The discounted occupation measure of the flow from `x` under `α ∈ R`, on `E × U`:
`B ↦ ∫_0^∞ e^{-(β+λ)t} ∫_U 1_B(φ^α_t(x), u) α_t(du) dt`. It is a notation for the integrals of
Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), (8.4), (8.5) and (8.7). -/
noncomputable def occupation (M : JumpModel E U) (x : E) (α : RelaxedControl U) : Measure (E × U) :=
  (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun t =>
      ENNReal.ofReal (Real.exp (-(M.β + M.lam) * t))).compProd α.1).map
    fun p => (M.flow α x p.1, p.2)

/-- The embedded discrete-time model with relaxed controls (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), (8.7), p.250, PDF 261):
`r'(x,α) = ∫_0^∞ e^{-(β+λ)t} ∫ r(φ^α_t(x),u) α_t(du) dt` and
`Q'(B|x,α) = λ ∫_0^∞ e^{-(β+λ)t} ∫ Q(B|φ^α_t(x),u) α_t(du) dt`, with discount factor `β' = 1`
and the cemetery state skipped. -/
noncomputable def relaxedStage (M : JumpModel E U) : StageModel E (RelaxedControl U) where
  rew x α := erealIntegral (M.occupation x α) fun p => ((M.r p : ℝ) : EReal)
  kern x α := ENNReal.ofReal M.lam • (M.occupation x α).bind M.Q

/-- The embedded discrete-time model `(E, A, D, Q', r')` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), (8.4)–(8.5), p.247, PDF 258):
the model `relaxedStage` restricted to deterministic controls, for which `α_t` is a one-point
measure, so that `Q'(B|x,α) = λ ∫_0^∞ e^{-(λ+β)t} Q(B|φ^α_t(x),α_t) dt` and
`r'(x,α) = ∫_0^∞ e^{-(β+λ)t} r(φ^α_t(x),α_t) dt`. -/
noncomputable def stage (M : JumpModel E U) : StageModel E (ControlFn U) where
  rew x α := M.relaxedStage.rew x α.toRelaxed
  kern x α := M.relaxedStage.kern x α.toRelaxed

/-- `J_∞(x) = sup_{(f_n)} J_∞(f_n)(x)` of the embedded model (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.248, PDF 259), the supremum
over the Markov policies `(f_n)`, `f_n : E → A`. -/
noncomputable def Jinf (M : JumpModel E U) (x : E) : EReal :=
  ⨆ f : ℕ → DecisionRule E U, M.stage.Jinf (fun n => (f n).control) x

/-- `J^{rel}_∞`, the value function of the embedded model with relaxed controls (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.251,
PDF 262), the supremum over the policies `(f_n)`, `f_n : E → R`. -/
noncomputable def JinfRelaxed (M : JumpModel E U) (x : E) : EReal :=
  ⨆ f : ℕ → RelaxedDecisionRule E U, M.relaxedStage.Jinf (fun n => (f n).control) x

end JumpModel

end BauerleRiederMDP.PDMDP


