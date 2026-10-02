-- Prove2me | Definitions.Def_MDPFinance_Bellman_StructureAssumption
-- name    : MDPFinance_Bellman_StructureAssumption
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:10:08.126535+00:00
-- url     : https://prove2.me/theorems/8f75e466-2dda-40ba-b593-96accb5a8ec2
-- title:
--   The Structure Assumption (SAN)
-- statement:
--   The Structure Theorem (Theorem 2.3.8) is proved under one abstract hypothesis, the
--   **Structure Assumption (SAN)**, rather than a case-by-case argument for particular state and
--   action spaces. It postulates the existence of sets $\mathrm{IM}_n \subseteq \mathrm{IM}(E)$ and
--   $\Delta_n \subseteq F_n$, for $n = 0, \dots, N-1$ (with $\mathrm{IM}_N$ also given), such that:
--
--   1. $g_N \in \mathrm{IM}_N$;
--   2. if $v \in \mathrm{IM}_{n+1}$, then $T_n v$ is well-defined and $T_n v \in \mathrm{IM}_n$;
--   3. for every $v \in \mathrm{IM}_{n+1}$ there exists a maximizer $f_n$ of $v$ with
--      $f_n \in \Delta_n$.
--
--   Informally, $(\mathrm{IM}_n)$ names a class of "well-behaved" value candidates that is closed
--   under one application of the maximal reward operator $T_n$ and on which a measurable maximizing
--   selection always exists; $\Delta_n$ names the class those maximizers live in. Concrete sufficient
--   conditions for (SAN) — compactness of the action sets together with semicontinuity of the data —
--   are the subject of a later section of the chapter and are not part of this mission.
--
--   **Formalization Note.** The containments $\mathrm{IM}_n \subseteq \mathrm{IM}(E)$ and
--   $\Delta_n \subseteq F_n$ are recorded as explicit hypotheses (`∀ n, IMs n ⊆ IM E` and
--   `Deltas n ⊆ {f | IsDecisionRule M n f}`), matching the book's own two-step phrasing "there exist
--   sets $\mathrm{IM}_n \subset \mathrm{IM}(E)$ and $\Delta_n \subset F_n$ such that…" rather than
--   folding the ambient-set membership into the three numbered clauses.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 23, Structure Assumption (SAN), unnumbered

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- The Structure Assumption (SAN) (Bäuerle–Rieder, p. 23, PDF 38, unnumbered): there exist sets
`IM_n ⊆ IM(E)` and `Δ_n ⊆ F_n` such that (i) `g_N ∈ IM_N`, (ii) if `v ∈ IM_{n+1}` then
`T_n v ∈ IM_n`, and (iii) for all `v ∈ IM_{n+1}` there exists a maximizer `f_n` of `v` with
`f_n ∈ Δ_n`, for `n = 0, …, N-1`. `IMs : ℕ → Set (E → EReal)` and `Deltas : ℕ → Set (E → A)`
play the roles of `(IM_n)` and `(Δ_n)`; the containments `IM_n ⊆ IM(E)` and `Δ_n ⊆ F_n` are
recorded as explicit hypotheses rather than folded into the membership clauses, matching the
book's own two-step phrasing ("There exist sets `IM_n ⊂ IM(E)` and `Δ_n ⊂ F_n` such that…"). -/
def StructureAssumption (M : MarkovDecisionModel E A N) (IMs : ℕ → Set (E → EReal))
    (Deltas : ℕ → Set (E → A)) : Prop :=
  (∀ n, IMs n ⊆ IM E) ∧
  (∀ n < N, Deltas n ⊆ {f | IsDecisionRule M n f}) ∧
  (fun x => (M.g x : EReal)) ∈ IMs N ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), T M n v ∈ IMs n) ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), ∃ f ∈ Deltas n, IsMaximizer M n v f)

end MDPFinance.Bellman


