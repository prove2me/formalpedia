-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_StructureAssumption
-- name    : BauerleRiederMDP_FiniteHorizon_StructureAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:28.508195+00:00
-- url     : https://prove2.me/theorems/4365647a-f439-4979-9094-47a86194ed23
-- title:
--   Structure Assumption $(SA_N)$
-- statement:
--   Let $\mathbb M_n$, $n=0,\dots,N$, be sets of measurable functions $E\to[-\infty,\infty)$ and let $\Delta_n\subset F_n$, $n=0,\dots,N-1$. The **Structure Assumption** $(SA_N)$ for these sets requires, for all $n=0,\dots,N-1$:
--
--   1. $g_N\in\mathbb M_N$;
--   2. if $v\in\mathbb M_{n+1}$ then $T_nv$ is well defined and $T_nv\in\mathbb M_n$;
--   3. for all $v\in\mathbb M_{n+1}$ there exists a maximizer $f_n$ of $v$ with $f_n\in\Delta_n$.
--
--   It replaces any compactness or continuity condition by the two properties backward induction needs: staying in a class of measurable functions, and existence of measurable maximizers.
--
--   **Formalization Note.** The sets are arguments of the predicate, because the conclusion of the Structure Theorem refers to them; the book's "there exist" becomes a universally quantified hypothesis of that theorem.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Structure Assumption (SA_N), p.23

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_TWellDefined

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel IM IsDecisionRule IsMaximizer T)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- The Structure Assumption (SA_N) (Bäuerle & Rieder (2011), p.23, PDF 38) for given sets
`IM_n ⊂ IM(E)`, `n = 0, …, N`, and `Δ_n ⊂ F_n`, `n = 0, …, N-1`:
(i) `g_N ∈ IM_N`; (ii) if `v ∈ IM_{n+1}` then `T_n v` is well-defined and `T_n v ∈ IM_n`;
(iii) for all `v ∈ IM_{n+1}` there exists a maximizer `f_n` of `v` with `f_n ∈ Δ_n`.

**Formalization Note.** The sets are arguments: the book's "there exist sets" is a hypothesis of
the Structure Theorem, whose conclusion names them. Values of `IMs n` for `n > N` and of
`Deltas n` for `n ≥ N` do not enter. -/
def StructureAssumption {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (IMs : ℕ → Set (E → EReal)) (Deltas : ℕ → Set (E → A)) :
    Prop :=
  (∀ n ≤ N, IMs n ⊆ IM E) ∧
  (∀ n < N, Deltas n ⊆ {f | IsDecisionRule M n f}) ∧
  (fun x => (M.g x : EReal)) ∈ IMs N ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), TWellDefined M n v ∧ T M n v ∈ IMs n) ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), ∃ f ∈ Deltas n, IsMaximizer M n v f)

end BauerleRiederMDP.FiniteHorizon


