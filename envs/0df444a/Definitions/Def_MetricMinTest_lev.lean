-- Prove2me | Definitions.Def_MetricMinTest_lev
-- name    : MetricMinTest_lev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:55.86186+00:00
-- url     : https://prove2.me/theorems/25fbbaad-833c-4522-bac8-4fd0959b8681
-- title:
--   Hierarchical level $\mathrm{lev}(x,y)$
-- statement:
--   On $V=\{0,\dots,b-1\}^m$, for distinct $x,y$, $\mathrm{lev}(x,y)=\max\{t : x_t\ne y_t\}\in\{1,\dots,m\}$, and $\mathrm{lev}(x,x)=0$. The block $B_t(x)=\{y : \mathrm{lev}(x,y)\le t\}$ has $b^t$ points.
--
--   **Formalization Note** Points are $\mathrm{Fin}\,m\to\mathrm{Fin}\,b$ with coordinates counted from $0$; the paper's 1-based level is kept, $\mathrm{lev}(x,y)=1+$ (largest 0-based coordinate where they differ).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §4.1, p.8

import Mathlib

namespace MetricMinTest

/-- **Hierarchical level** `lev(x, y)`. Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §4.1, p.8: on
`V = {0, …, b − 1}^m`, for distinct `x, y`, `lev(x, y) = max {t : x_t ≠ y_t} ∈ {1, …, m}`, and
`lev(x, x) = 0`.

**Formalization Note.** Points are `Fin m → Fin b` with 0-based coordinates `t`; the paper's
1-based level is kept, so `lev x y = 1 + (largest 0-based coordinate where x, y differ)`, and
`0` when `x = y` (the supremum of the empty set in `ℕ`). -/
def lev {m b : ℕ} (x y : Fin m → Fin b) : ℕ :=
  (Finset.univ.filter (fun t => x t ≠ y t)).sup (fun t => (t : ℕ) + 1)

end MetricMinTest


