-- Prove2me | Definitions.Def_RobustFcstAgg_inter
-- name    : RobustFcstAgg_inter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:09.402586+00:00
-- url     : https://prove2.me/theorems/6d658425-4108-4e61-8ee4-63996b4925a1
-- title:
--   Intersection variable $\mathrm{inter}(S)=\sum_{T\supseteq S}X_T$
-- statement:
--   For a set of experts $S\subseteq[n]$, the **intersection variable** is
--   $$\mathrm{inter}(S)=\sum_{T\supseteq S}X_T,$$
--   the sum of the signals seen by every expert of $S$. It is the common value of the iterated expectations over the experts in $S$.
--
--   **Formalization Note** The set $S$ may be empty here, which gives $\mathrm{inter}(\emptyset)=Y$: this is the convention of the proof of Lemma 1, p.25. The collection $\mathcal Q_{\mathrm{inter}(d)}$ has $1\le|S|$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 3.1, p.9; p.25

import Mathlib
import Definitions.Def_RobustFcstAgg_Signals

namespace RobustFcstAgg

/-- **Intersection query as a random variable: `inter(S) = Σ_{T ⊇ S} X_T`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 3.1, p.9.

**Formalization Note.** `inter ∅ = Y` holds definitionally up to the filter, which is the convention
`inter(∅) := Y` of the proof of Lemma 1, p.25. The collection `Q_inter(d)` itself has `1 ≤ |S|`
(`InterIndex`). -/
def inter {n : ℕ} (S : Finset (Fin n)) (x : Signals n) : ℝ := ∑ T : Subs n with S ⊆ T.1, x T

end RobustFcstAgg


