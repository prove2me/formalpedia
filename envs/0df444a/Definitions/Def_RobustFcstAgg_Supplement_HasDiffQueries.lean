-- Prove2me | Definitions.Def_RobustFcstAgg_Supplement_HasDiffQueries
-- name    : RobustFcstAgg_Supplement_HasDiffQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:37:17.31742+00:00
-- url     : https://prove2.me/theorems/cb26369f-0337-40df-a8ea-6f663662b120
-- title:
--   A rule whose queries are $\mathcal Q_{\mathrm{diff}(L)}$ for some list $L$
-- statement:
--   A deterministic aggregation rule $R=(\mathcal Q,f)$ **has a difference query collection** if there is an ordered list $L$ of experts such that its indexed query collection is, up to relabelling the index, exactly $\mathcal Q_{\mathrm{diff}(L)}=(\mathrm{diff}(i_1,\dots,i_k))_{k=1}^{|L|}$.
--
--   Together with a Borel-measurable aggregation function $f$ (part of every rule) and DAG-elicitability, this is the paper's **difference aggregation rule** (Definition 7).
--
--   **Formalization Note** The predicate is only the clause $\mathcal Q=\mathcal Q_{\mathrm{diff}(L)}$. DAG-elicitability is stated, with its witnessing DAG, in the theorem that asserts a difference aggregation rule (Theorem 2).
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 7, p.10

import Mathlib
import Definitions.Def_RobustFcstAgg_Rule
import Definitions.Def_RobustFcstAgg_Supplement_diffColl

namespace RobustFcstAgg.Supplement

/-- **A rule whose query collection is `Q_diff(L)` for some list `L`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast
Aggregation via Additional Queries*, arXiv:2512.05271, Definition 7, p.10: "A (deterministic) difference aggregation rule
`R = (Q, f)` is a DAG-elicitable rule with `Q = Q_diff(L)` for some ordered list of agents `L`, and `f(Q)` a
Borel-measurable function of the collection of difference queries."

**Formalization Note.** This predicate is the clause `Q = Q_diff(L)`: up to a relabelling `e` of the index, the rule's
queries are exactly the difference queries of the nonempty prefixes of `L`. Borel `f` is bundled in `Rule`.
DAG-elicitability is stated separately, with the eliciting DAG, wherever a difference aggregation rule is asserted
(Theorem 2). -/
def HasDiffQueries {n : ℕ} (R : Rule n) : Prop :=
  ∃ L : List (Fin n), ∃ e : R.ι ≃ Fin L.length, ∀ j, R.Q j = diffColl L (e j)

end RobustFcstAgg.Supplement


