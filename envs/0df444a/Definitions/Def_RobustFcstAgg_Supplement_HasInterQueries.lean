-- Prove2me | Definitions.Def_RobustFcstAgg_Supplement_HasInterQueries
-- name    : RobustFcstAgg_Supplement_HasInterQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:36:35.529066+00:00
-- url     : https://prove2.me/theorems/282dd26f-548f-4438-9bfc-8779d41733ad
-- title:
--   A rule whose queries are $\mathcal Q_{\mathrm{inter}(d)}$
-- statement:
--   A deterministic aggregation rule $R=(\mathcal Q,f)$ **has the intersection query collection of order $d$** if its indexed query collection is, up to relabelling the index, exactly
--   $$
--   \mathcal Q_{\mathrm{inter}(d)}=\bigl(\mathrm{inter}(S)\bigr)_{S\subseteq[n],\;1\le|S|\le d},\qquad \mathrm{inter}(S)=\sum_{T\supseteq S}X_T .
--   $$
--   Together with a Borel-measurable aggregation function $f$ (part of every rule) and DAG-elicitability, this is the paper's **intersection aggregation rule** (Definition 5).
--
--   **Formalization Note** The predicate is only the clause $\mathcal Q=\mathcal Q_{\mathrm{inter}(d)}$, as a bijection of the index with the base `InterIndex n d` under which each query is the base `interQuery`. DAG-elicitability is stated, with its witnessing DAG, in the theorem that asserts an intersection aggregation rule (Theorem 1).
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 5, p.9

import Mathlib
import Definitions.Def_RobustFcstAgg_Rule
import Definitions.Def_RobustFcstAgg_InterIndex
import Definitions.Def_RobustFcstAgg_interQuery

namespace RobustFcstAgg.Supplement

/-- **A rule whose query collection is `Q_inter(d)`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via
Additional Queries*, arXiv:2512.05271, Definition 5, p.9: "A (deterministic) intersection aggregation rule `R = (Q, f)` is a
DAG-elicitable rule with `Q := Q_inter(d)`, and `f(Q)` a Borel-measurable function of the collection of intersection
queries `Q`."

**Formalization Note.** This predicate is the clause `Q = Q_inter(d)`: the rule's queries are, up to a relabelling `e` of
the index, exactly the intersection queries `inter(S)`, `1 ≤ |S| ≤ d` (base `InterIndex`, `interQuery`). Borel `f` is
bundled in `Rule`. DAG-elicitability is stated separately, with the eliciting DAG, wherever an intersection aggregation
rule is asserted (Theorem 1). -/
def HasInterQueries {n : ℕ} (R : Rule n) (d : ℕ) : Prop :=
  ∃ e : R.ι ≃ InterIndex n d, ∀ j, R.Q j = interQuery (e j).1 (e j).2.1

end RobustFcstAgg.Supplement


