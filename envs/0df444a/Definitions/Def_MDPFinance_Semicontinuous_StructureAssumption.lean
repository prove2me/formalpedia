-- Prove2me | Definitions.Def_MDPFinance_Semicontinuous_StructureAssumption
-- name    : MDPFinance_Semicontinuous_StructureAssumption
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:26:27.126858+00:00
-- url     : https://prove2.me/theorems/8a662120-f07d-4508-95bc-bcb6a62068bd
-- title:
--   The Structure Assumption (SAN)
-- statement:
--   The **Structure Assumption (SAN)** holds for a Markov Decision Model if there exist sets
--   $\mathrm{IM}_n \subseteq \mathrm{IM}(E)$ and $\Delta_n \subseteq F_n$, for $n = 0,\dots,N$, such
--   that: (i) $g_N \in \mathrm{IM}_N$; (ii) $v \in \mathrm{IM}_{n+1} \implies T_n v \in
--   \mathrm{IM}_n$ for $n < N$; (iii) every $v \in \mathrm{IM}_{n+1}$ has a maximizer $f_n \in
--   \Delta_n$ at time $n$, for $n < N$.
--
--   Every theorem in this mission (Theorem 2.4.6, Theorem 2.4.10, and the goal Theorem 2.4.13)
--   exhibits a concrete pair of sequences $(\mathrm{IM}_n)$, $(\Delta_n)$ — built from upper
--   semicontinuous, continuous, or merely measurable functions of bounded weighted growth — that
--   satisfies exactly this predicate, under successively weaker hypotheses on the model's data.
--   Once (SAN) holds, chunk `02a-model-bellman-equation`'s Theorem 2.3.8 (the Structure Theorem)
--   applies: the value function solves the Bellman equation and an optimal policy exists.
--
--   **Formalization Note.** Restated from `MDPFinance.Bellman.StructureAssumption` (chunk `02a`),
--   identically.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 23, unnumbered (the Structure Assumption)

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Semicontinuous

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- The Structure Assumption (SAN) (Bäuerle–Rieder, p. 23, PDF 38, unnumbered), restated from
`MDPFinance.Bellman.StructureAssumption` (chunk `02a`): there exist sets `IM_n ⊆ IM(E)` and
`Δ_n ⊆ F_n` such that (i) `g_N ∈ IM_N`, (ii) if `v ∈ IM_{n+1}` then `T_n v ∈ IM_n`, and (iii)
for all `v ∈ IM_{n+1}` there exists a maximizer `f_n` of `v` with `f_n ∈ Δ_n`, for
`n = 0, …, N-1`. This chunk's goal (Theorem 2.4.13) and its supporting milestones each exhibit
concrete `IM_n`, `Δ_n` satisfying this same predicate. -/
def StructureAssumption (M : MarkovDecisionModel E A N) (IMs : ℕ → Set (E → EReal))
    (Deltas : ℕ → Set (E → A)) : Prop :=
  (∀ n, IMs n ⊆ IM E) ∧
  (∀ n < N, Deltas n ⊆ {f | IsDecisionRule M n f}) ∧
  (fun x => (M.g x : EReal)) ∈ IMs N ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), T M n v ∈ IMs n) ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), ∃ f ∈ Deltas n, IsMaximizer M n v f)

end MDPFinance.Semicontinuous


