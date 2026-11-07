-- Prove2me | Definitions.Def_RobustFcstAgg_InterIndex
-- name    : RobustFcstAgg_InterIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:41:14.198099+00:00
-- url     : https://prove2.me/theorems/56cf6ac6-b002-46d1-b2fc-8412057b5c5d
-- title:
--   Index of $\mathcal Q_{\mathrm{inter}(d)}$: subsets with $1\le|S|\le d$
-- statement:
--   The collection $\mathcal Q_{\mathrm{inter}(d)}=(\mathrm{inter}(S))_{1\le|S|\le d}$ is indexed by the subsets $S\subseteq[n]$ with $1\le|S|\le d$. Its size is $m_d=\sum_{k=1}^d\binom nk$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 3.1, p.9

import Mathlib

namespace RobustFcstAgg

/-- **Index of `Q_inter(d)`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 3.1, p.9: "`Q_inter(d) := (inter(S))_{1 ≤ |S| ≤ d}`, indexed by the
corresponding subsets `S`". -/
abbrev InterIndex (n d : ℕ) : Type := {S : Finset (Fin n) // S.Nonempty ∧ S.card ≤ d}

end RobustFcstAgg


