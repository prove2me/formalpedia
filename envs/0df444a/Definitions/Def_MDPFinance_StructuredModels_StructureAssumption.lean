-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_StructureAssumption
-- name    : MDPFinance_StructuredModels_StructureAssumption
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:36:34.896986+00:00
-- url     : https://prove2.me/theorems/ecbb3fea-1eab-47e0-8190-91dab7a54520
-- title:
--   The Structure Assumption (SAN) (restated)
-- statement:
--   Families $(\mathrm{I\!M}_n)_{n \leq N} \subseteq \mathrm{I\!M}(E)$ and $(\Delta_n)_{n<N}$ of
--   decision rules satisfy the **Structure Assumption (SAN)** if $g_N \in \mathrm{I\!M}_N$; $v \in
--   \mathrm{I\!M}_{n+1}$ implies $T_n v \in \mathrm{I\!M}_n$; and every $v \in
--   \mathrm{I\!M}_{n+1}$ has a maximizer in $\Delta_n$, for every $n = 0,\dots,N-1$.
--
--   **Formalization Note.** Restated from `MDPFinance.Bellman.StructureAssumption` /
--   `MDPFinance.Semicontinuous.StructureAssumption` (chunks `02a`/`02b`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 23, PDF 38 (unnumbered display, Structure Assumption (SAN))

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- The Structure Assumption (SAN) (Bäuerle–Rieder, p. 23, PDF 38, unnumbered), restated from
`MDPFinance.Bellman.StructureAssumption` (chunk `02a`) / `MDPFinance.Semicontinuous.StructureAssumption`
(chunk `02b`): there exist sets `IM_n ⊆ IM(E)` and `Δ_n ⊆ F_n` such that (i) `g_N ∈ IM_N`, (ii)
if `v ∈ IM_{n+1}` then `T_n v ∈ IM_n`, and (iii) for all `v ∈ IM_{n+1}` there exists a maximizer
`f_n` of `v` with `f_n ∈ Δ_n`, for `n = 0, …, N-1`. Every result of this chunk exhibits concrete
`IM_n`, `Δ_n` satisfying this same predicate. -/
def StructureAssumption (M : MarkovDecisionModel E A N) (IMs : ℕ → Set (E → EReal))
    (Deltas : ℕ → Set (E → A)) : Prop :=
  (∀ n, IMs n ⊆ IM E) ∧
  (∀ n < N, Deltas n ⊆ {f | IsDecisionRule M n f}) ∧
  (fun x => (M.g x : EReal)) ∈ IMs N ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), T M n v ∈ IMs n) ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), ∃ f ∈ Deltas n, IsMaximizer M n v f)

end MDPFinance.StructuredModels


