-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_Policy
-- name    : MDPFinance_StructuredModels_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:33:48.761757+00:00
-- url     : https://prove2.me/theorems/76fb6253-8862-4294-b38e-e88be29e040c
-- title:
--   Decision rules (restated)
-- statement:
--   A **decision rule at time $n$** for a Markov Decision Model $M$ is a measurable map $f : E
--   \to A$ with $f(x) \in D_n(x)$ for every state $x$.
--
--   **Formalization Note.** Restated from `MDPFinance.Bellman.IsDecisionRule` (chunk `02a`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 16, Definition 2.1.5

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- A decision rule at time `n` (Bäuerle–Rieder, Definition 2.1.5a, p. 16, PDF 31): a measurable
`f : E → A` with `f(x) ∈ D_n(x)` for all `x`. Restated from `MDPFinance.Bellman.IsDecisionRule`
(chunk `02a`); only this one clause of Def. 2.1.5 is needed in this chunk. -/
def IsDecisionRule (M : MarkovDecisionModel E A N) (n : ℕ) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D n

end MDPFinance.StructuredModels


