-- Prove2me | Definitions.Def_RobustFcstAgg_Supplement_diffColl
-- name    : RobustFcstAgg_Supplement_diffColl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:36:09.476924+00:00
-- url     : https://prove2.me/theorems/51cbc26a-4701-4e98-bbe5-b734eb842e7b
-- title:
--   Difference query collection $\mathcal Q_{\mathrm{diff}(L)}$
-- statement:
--   For an ordered list $L=(i_1,\dots,i_d)$ of experts, the **difference query collection** is
--   $$
--   \mathcal Q_{\mathrm{diff}(L)}=\bigl(\mathrm{diff}(i_1,\dots,i_k)\bigr)_{k=1}^{d},
--   $$
--   one difference query for each nonempty prefix of $L$. It has exactly $|L|$ queries.
--
--   **Formalization Note** Indexed by $\{0,\dots,|L|-1\}$ (`Fin L.length`): index $j$ is the difference query of the prefix of length $j+1$. The empty list gives the empty collection.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 3.3, p.10

import Mathlib
import Definitions.Def_RobustFcstAgg_Supplement_diffQuery

namespace RobustFcstAgg.Supplement

/-- **Difference query collection `Q_diff(L)`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via
Additional Queries*, arXiv:2512.05271, Sec. 3.3, p.10: "`Q_diff(L) := (diff(i₁, …, i_k))_{k=1}^d`" for an ordered list
`L = (i₁, …, i_d)` of experts.

**Formalization Note.** Indexed by `Fin L.length`: index `j` is the difference query of the prefix of length `j + 1`.
The empty list gives the empty collection. -/
noncomputable def diffColl {n : ℕ} (L : List (Fin n)) : Fin L.length → Query n :=
  fun j => diffQuery (L.take (j.1 + 1)) (by
    simp only [ne_eq, List.take_eq_nil_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or]
    exact List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2))

end RobustFcstAgg.Supplement


