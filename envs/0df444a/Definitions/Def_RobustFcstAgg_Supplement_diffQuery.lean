-- Prove2me | Definitions.Def_RobustFcstAgg_Supplement_diffQuery
-- name    : RobustFcstAgg_Supplement_diffQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:35:35.394534+00:00
-- url     : https://prove2.me/theorems/5502669b-b9bf-428b-9f67-653e92d56792
-- title:
--   Difference query $\mathrm{diff}(i_1,\dots,i_k)$
-- statement:
--   For a nonempty ordered list $L=(i_1,\dots,i_k)$ of experts (repetitions allowed), the **difference query** $\mathrm{diff}(L)$ is answered by the last expert $i_k$ and is defined by recursion on the length of the list:
--   $$
--   \mathrm{diff}(i_1)=\mathbb E[Y\mid S_{i_1}]=Y_{i_1},\qquad
--   \mathrm{diff}(i_1,\dots,i_k)=\mathbb E\Bigl[\,Y-\sum_{1\le j<k}\mathrm{diff}(i_1,\dots,i_{k-j})\;\Bigm|\;S_{i_k}\Bigr].
--   $$
--   The subtracted sum runs over the difference queries of all proper nonempty prefixes of $L$. Intuitively, expert $i_k$ is asked what they would add to the estimate already assembled by the earlier queries.
--
--   Difference queries are the building blocks of the difference aggregation rules, which recover $Y$ with only $n$ queries and attain the optimal error under a query budget.
--
--   **Formalization Note** The conditional expectation given $S_{i_k}=s$ is the integral over the signals hidden from $i_k$ (the base mission's `glue` and `InfoStruct.restLaw`), which is a version of the conditional expectation because the signals are independent. The source prints $S_k$ for $S_{i_k}$; Proposition 3 and the proof of Proposition 4 condition on $S_{i_k}$. The query is defined by this iteration, not by the closed form of Proposition 3.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 3.3, p.10

import Mathlib
import Definitions.Def_RobustFcstAgg_Y
import Definitions.Def_RobustFcstAgg_glue
import Definitions.Def_RobustFcstAgg_InfoStruct_restLaw
import Definitions.Def_RobustFcstAgg_Query_rv
open MeasureTheory

namespace RobustFcstAgg.Supplement

/-- **Difference query `diff(i₁, …, i_k)`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via
Additional Queries*, arXiv:2512.05271, Sec. 3.3, p.10: "`diff(i) := Y_i` and
`diff(i₁, …, i_k) := E[Y − Σ_{1≤j<k} diff(i₁, …, i_{k−j}) | S_k]`".

**Formalization Note.** The list `L = (i₁, …, i_k)` is nonempty and may repeat experts. The query is answered by its
last expert `i_k` (the printed `S_k` is `S_{i_k}`, as Proposition 3 and the proof of Proposition 4, p.23, read it).
The subtracted sum runs over the proper nonempty prefixes `L.take (j + 1)`, `j < k − 1`; for `k = 1` it is empty and
the query is `E[Y | S_{i₁}] = Y_{i₁}`. `E[· | S_i = s]` is the integral over the signals hidden from `i`, the base
mission's encoding (`glue`, `InfoStruct.restLaw`), valid because the signals are independent; a non-integrable
fibre gives Bochner `0`, which does not occur for the finite-variance instances of the model. The query depends on
`D`, which the experts know. Defined by the iterated conditional expectation, not by Proposition 3's closed form. -/
noncomputable def diffQuery {n : ℕ} (L : List (Fin n)) (hL : L ≠ []) : Query n :=
  ⟨L.getLast hL, fun D s =>
    ∫ y, (Y (glue (L.getLast hL) s y) -
        ∑ j : Fin (L.length - 1),
          (diffQuery (L.take (j.1 + 1))
            (by simp [List.take_eq_nil_iff, hL])).rv D (glue (L.getLast hL) s y))
      ∂(D.restLaw (L.getLast hL))⟩
termination_by L.length
decreasing_by
  simp only [List.length_take]
  have := j.2
  omega

end RobustFcstAgg.Supplement


