-- Prove2me | Definitions.Def_RobustFcstAgg_Supplement_qryErrorSet
-- name    : RobustFcstAgg_Supplement_qryErrorSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:38:17.770203+00:00
-- url     : https://prove2.me/theorems/d02d60e2-6588-4753-8a14-864daef66828
-- title:
--   Errors of $\mathcal A^{\mathrm{qry}}_d$
-- statement:
--   The set of worst-case errors
--   $$
--   \Bigl\{\mathrm{error}(A)=\sup_{\mathcal D}\frac{L_{\mathcal D}(A)}{\mathrm{Var}_{\mathcal D}(Y)}\;:\;A\in\mathcal A^{\mathrm{qry}}_d\Bigr\},
--   $$
--   the errors of the approximators implemented by DAG-elicitable randomized rules of query complexity at most $d$. Its least element, when it exists, is $\min_{A\in\mathcal A^{\mathrm{qry}}_d}\mathrm{error}(A)$.
--
--   **Formalization Note** The error is the base `RandRule.error`, valued in $[0,\infty]$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 4.1, p.11

import Mathlib
import Definitions.Def_RobustFcstAgg_Supplement_IsQueryLE
import Definitions.Def_RobustFcstAgg_RandRule_error
open scoped ENNReal

namespace RobustFcstAgg.Supplement

/-- **Errors of `A^qry_d`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*,
arXiv:2512.05271, Sec. 4.1, p.11: the worst-case errors (Eq. (2), base `RandRule.error`) of the approximators implemented by
DAG-elicitable randomized rules of query complexity at most `d`.

**Formalization Note.** `error(A)` depends only on the a.s. class of the rule's output, so `min_{A ∈ A^qry_d} error(A)` is
the least element of this set, mirroring the base `errorSet`. -/
def qryErrorSet (n d : ℕ) : Set ℝ≥0∞ :=
  {e | ∃ R : RandRule n, IsQueryLE R d ∧ R.error = e}

end RobustFcstAgg.Supplement


