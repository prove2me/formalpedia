-- Prove2me | Definitions.Def_NestedLogitAssort_DeltaGrid_CandGrid
-- name    : NestedLogitAssort_DeltaGrid_CandGrid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:08:28.505239+00:00
-- url     : https://prove2.me/theorems/0cf2f5b3-89f9-4c5e-a8ac-fd03c817c7bd
-- title:
--   Candidate collection $\{\hat S_{il}:l=l^L_i,\dots,l^U_i\}\cup\{\emptyset\}$
-- statement:
--   Fix $\delta>1$ and, for every nest $i$ and level $l$, an assortment $\hat S_{il}$. The candidate collection of nest $i$ used in Theorem 12 is
--
--   $$
--   \{\hat S_{il}:\ l=l^L_i,\dots,l^U_i\}\cup\{\emptyset\},
--   $$
--
--   where only levels at which problem (15) is feasible contribute an assortment.
--
--   **Formalization Note** The level range is the predicate `InLevelRange`. The paper's $\hat S_{il}$ exists only at levels where (15) is feasible (Proposition 15 assumes it), so the assortment chosen at a level with an empty window is not in the collection.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 6.2 and Theorem 12, p. 28

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_InLevelRange
import Definitions.Def_NestedLogitAssort_DeltaGrid_Feasible15

namespace NestedLogitAssort.DeltaGrid

/-- **The candidate collection `{Ŝ_{il} : l = l^L_i, …, l^U_i} ∪ {∅}` of nest `i`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 6.2 and Theorem 12, p. 28.

`Shat i l` is the assortment chosen for nest `i` at level `l`. The collection consists of `∅`
and of `Shat i l` for every level `l` in the range `l^L_i, …, l^U_i` (`InLevelRange`) at which
problem (15) is feasible.

**Formalization Note.** The paper's `Ŝ_{il}` exists only where (15) has a feasible solution
(Proposition 15, p. 51, assumes it), so levels with an empty window contribute no assortment. -/
def CandGrid {M : Type*} {n : ℕ} (I : Instance M n) (δ : ℝ) (Shat : M → ℤ → Finset (Fin n))
    (i : M) : Set (Finset (Fin n)) :=
  {S | S = ∅ ∨ ∃ l : ℤ, InLevelRange I δ i l ∧ Feasible15 I δ i l ∧ S = Shat i l}

end NestedLogitAssort.DeltaGrid


