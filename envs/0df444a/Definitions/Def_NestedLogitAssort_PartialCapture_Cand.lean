-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_Cand
-- name    : NestedLogitAssort_PartialCapture_Cand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:44:30.622639+00:00
-- url     : https://prove2.me/theorems/3770e39f-777c-488a-940b-935909613cff
-- title:
--   Candidate collection $\{\hat S_i(\epsilon_i):\epsilon_i\in[0,\infty]\}\cup\{\{j\}:j\in N\}$
-- statement:
--   The candidate assortments of nest $i$ used in Theorem 10 are
--
--   $$
--   \mathcal C_i=\{\hat S_i(\epsilon):\epsilon\in[0,\infty]\}\cup\{\{j\}:j\in N\},
--   $$
--
--   the greedy knapsack assortments for every capacity together with all singletons.
--
--   **Formalization Note** The capacity $\epsilon=\infty$ is represented by the extra member $N$: with unlimited capacity every product is eligible and fits, so $\hat S_i(\infty)=N$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, p. 24 (unnumbered) and Theorem 10, p. 24

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_Shat

namespace NestedLogitAssort.PartialCapture

/-- **The candidate collection `{Ŝ_i(ϵ_i) : ϵ_i ∈ [0, ∞]} ∪ {{j} : j ∈ N}` of nest `i`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, p. 24 (unnumbered, and Theorem 10).

**Formalization Note.** `ϵ_i` ranges over the reals `ϵ ≥ 0`; the value `ϵ_i = ∞` is the extra
member `Finset.univ`: with unlimited capacity every product is eligible and fits, so
`ẑ_i(∞) = (1, …, 1)` and `Ŝ_i(∞) = N`. -/
noncomputable def Cand {M : Type*} {n : ℕ} (I : Instance M n) (i : M) : Set (Finset (Fin n)) :=
  {S | ∃ ε : ℝ, 0 ≤ ε ∧ S = Shat I i ε} ∪ {Finset.univ} ∪ {S | ∃ j : Fin n, S = {j}}

end NestedLogitAssort.PartialCapture


