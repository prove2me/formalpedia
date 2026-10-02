-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_StructureAssumption
-- name    : MDPFinance_BayesianModels_StructureAssumption
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:20:09.570893+00:00
-- url     : https://prove2.me/theorems/31e58b37-0aa0-4fc0-b84d-95801e9b526f
-- title:
--   The Structure Assumption (SAN), stationary form
-- statement:
--   This definition restates the **Structure Assumption (SAN)** of Chapter 2 — the hypothesis
--   under which the Bellman equation holds and an optimal Markov policy exists — specialized to a
--   **stationary** model, i.e. with a single pair $(IM,\Delta)$ used at every stage rather than a
--   sequence $(IM_n,\Delta_n)$. This matches the goal Theorem 5.4.10's own statement, which speaks of
--   "the sets $IM$ and $\Delta$" for the (stationary) information-based model, not indexed sets.
--
--   Given raw data $(D,Q,r,g,\beta)$ on $E$, $(IM,\Delta)$ satisfy SAN if: $IM$ consists of
--   measurable, never-$+\infty$ functions; $\Delta$ consists of feasible decision rules; the terminal
--   reward $g$ lies in $IM$; $T$ maps $IM$ into itself; and every $v \in IM$ has a maximizer in
--   $\Delta$.
--
--   **Formalization Note.** Restated from `MDPFinance.Bellman.StructureAssumption` (chunk `02a`) /
--   `MDPFinance.StructuredModels.StructureAssumption` (chunk `02c`), specialized to a stationary
--   model exactly as `MDPFinance.BayesianModels.Top` restates the Bellman operators.
--
--   **Moderation note.** The terminal reward of the raw data is $[-\infty,\infty]$-valued (matching $\hat g$), so the clause is $g\in IM$ directly.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 23, p. 23 (unnumbered, stationary form)

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- The Structure Assumption (SAN) (Bäuerle–Rieder, p. 23, PDF 38, unnumbered), specialized to
a *stationary* model (the same `IM`, `Δ` at every stage, matching the goal Theorem 5.4.10's own
statement of a single `IM`/`Δ` pair rather than a sequence `IM_n`/`Δ_n`): `IM ⊆ IM(E)`, `Δ` a set
of decision rules, `g ∈ IM`, `T` maps `IM` into itself, and every `v ∈ IM` has a maximizer in
`Δ`. Restated from `MDPFinance.Bellman.StructureAssumption` (chunk `02a`) /
`MDPFinance.StructuredModels.StructureAssumption` (chunk `02c`). -/
def StructureAssumptionOf (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal)
    (g : E → EReal) (β : ℝ) (IM' : Set (E → EReal)) (Δ : Set (E → A)) : Prop :=
  IM' ⊆ IM E ∧
  Δ ⊆ {f | IsDecisionRuleOf D f} ∧
  g ∈ IM' ∧
  (∀ v ∈ IM', Top D Q r β v ∈ IM') ∧
  (∀ v ∈ IM', ∃ f ∈ Δ, IsMaximizerOf D Q r β v f)

end MDPFinance.BayesianModels


