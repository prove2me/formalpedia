-- Prove2me | Definitions.Def_CanadaCTP_Supplement_Offline
-- name    : CanadaCTP_Supplement_Offline
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:35:48.994199+00:00
-- url     : https://prove2.me/theorems/077e74cb-dc84-44aa-839b-383f8b124e1d
-- title:
--   The offline optimum $\mathbb E[\mathrm{Off}]$
-- statement:
--   The **offline optimum** sees all edge weights upfront and walks a shortest $s$–$t$ path. On a disjoint-path instance with $k$ paths, where path $i$ has edges $j=1,\dots,m_i$ with realized weights $w_{i,j}$, its expected cost is
--   $$\mathbb E[\mathrm{Off}]=\mathbb E\Big[\min_{1\le i\le k}\sum_{j=1}^{m_i}w_{i,j}\Big].$$
--
--   The competitive ratio of Theorem 8 compares $\mathbb E[\mathrm{Opt}]$ with this quantity.
--
--   **Formalization Note** The expectation is the finite sum over joint realizations weighted by their probabilities; the minimum is an infimum in $[0,\infty]$ over the finite set of paths, attained since every CTP instance has a path.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Appendix B, p.31

import Mathlib
import Definitions.Def_CanadaCTP_Model

namespace CanadaCTP.Supplement

open CanadaCTP
open scoped ENNReal

/-- The expected cost `E[Off]` of the **offline optimum** (*Canada Retravelled*, manuscript,
sha256 8117348e…3a33, Appendix B, p.31): all edge weights are revealed upfront and the traveller
takes a shortest `s`–`t` path. On a disjoint-path instance the shortest path under realization `ι`
has length `minᵢ Σⱼ w(ι, i, j)`, so `E[Off] = Σ_ι P(ι) · minᵢ Σⱼ w(ι, i, j)`.

**Formalization Note.** The minimum over paths is an infimum in `ℝ≥0∞` over the finite type
`Fin I.k`, attained when `k ≥ 1` (it is `⊤` for `k = 0`, which no CTP instance has). -/
noncomputable def offCost (I : Inst) : ℝ≥0∞ :=
  ∑ ι : Realz I, I.P ι * ⨅ i : Fin I.k, ENNReal.ofReal (∑ j, I.w ι i j)

end CanadaCTP.Supplement


