-- Prove2me | Definitions.Def_RobustFcstAgg_SatisfiesCondition1
-- name    : RobustFcstAgg_SatisfiesCondition1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:49:59.660398+00:00
-- url     : https://prove2.me/theorems/c9c38fda-447d-47fe-a000-93973690298b
-- title:
--   Condition 1: a query is a Borel function of the scored conditional law
-- statement:
--   For every instance $\mathcal D$ there is a Borel-measurable function $\gamma$ on distributions such that
--   $$Q(S_i,\mathcal D)=\gamma\bigl(\mathcal L_{\mathcal D}(\mathcal R\mid S_i)\bigr)\quad\text{a.s.,}$$
--   where $\mathcal L_{\mathcal D}(\mathcal R\mid S_i)$ is the conditional distribution of the variables being scored.
--
--   The source imposes this regularity throughout Sections 4.2-4.3; it is what ties the answers to the posterior belief of the answering expert, and it is satisfied by standard strictly proper scoring rules such as the Brier score.
--
--   **Formalization Note** The domain of $\gamma$ is the space of all measures with the Giry $\sigma$-algebra; $\mathcal P(\mathbb R^m)$ is a measurable subset of it, so a Borel $\gamma$ on it extends by a constant. The condition is attached to the variables scored on the graph's edges rather than to every finite set of variables against which $Q$ is elicitable.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Condition 1, p.25; p.14

import Mathlib
import Definitions.Def_RobustFcstAgg_condLaw
import Definitions.Def_RobustFcstAgg_InfoStruct_agentLaw
import Definitions.Def_RobustFcstAgg_Query
open MeasureTheory

namespace RobustFcstAgg

/-- **Condition 1 for a query and its scored variables.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Condition 1, p.25: "there exists a
Borel-measurable function `γ : P(ℝ^m) → ℝ` such that `Q(S_i, D) = γ(L_D(R | S_i))` a.s."

**Formalization Note.** `γ` may depend on `D`, as printed. Its domain is `Measure (N → ℝ)` with the Giry
σ-algebra; `P(ℝ^m)` is a measurable subset, so a Borel `γ` on it extends by a constant. The condition is applied
to the scored variables of the DAG's edges (`IsDAGElicits`), not to every finite set of variables against which
the query is elicitable; this is weaker on the class. -/
def SatisfiesCondition1 {n : ℕ} (q : Query n) {N : Type} (R : InfoStruct n → N → Signals n → ℝ) : Prop :=
  ∀ D : InfoStruct n, ∃ γ : Measure (N → ℝ) → ℝ, Measurable γ ∧
    ∀ᵐ s ∂D.agentLaw q.agent, q.eval D s = γ (condLaw D q.agent (R D) s)

end RobustFcstAgg


