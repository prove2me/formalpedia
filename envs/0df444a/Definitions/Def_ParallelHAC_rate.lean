-- Prove2me | Definitions.Def_ParallelHAC_rate
-- name    : ParallelHAC_rate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:33.674566+00:00
-- url     : https://prove2.me/theorems/d47a903d-de89-47eb-a89e-0ce5040947cc
-- title:
--   The rate $\tilde O((k\cdot c)^{O(k)})$ as $C(\log_2 n+1)^C(kc)^{Ck}$
-- statement:
--   For a constant $C$, a number of points $n$, a dimension $k$ and an approximation factor $c$,
--   $$\mathrm{rate}_C(n,k,c)=C\,(\log_2 n+1)^{C}\,(k\,c)^{C k}.$$
--
--   A bound "$\le\tilde O((k\cdot c)^{O(k)})$" in the paper is formalized as "there is a constant $C$, depending only on the fixed structural constants of the linkage, with $\le\mathrm{rate}_C(n,k,c)$". The factor $(\log_2 n+1)^C$ absorbs the $\mathrm{poly}(\log n)$ terms hidden by $\tilde O$ (footnote 5 of the paper).
--
--   **Formalization Note** Real powers; for $k\ge1$, $c\ge1$ both bases are at least $1$ (in Lean $\log_2 0=0$), so the rate is at least $C$ for every $n$.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), Theorem 3, p.7 (PDF p.10); footnote 5, p.3 (PDF p.6)

import Mathlib

namespace ParallelHAC

/-- The rate `Õ((k · c)^{O(k)})` of the paper, with its hidden constants pinned by one constant
`C`: `rate C n k c = C · (log₂ n + 1)^C · (k · c)^{C k}`.
Source: arXiv:2507.20047 (sha256 a21061c8…), Theorem 3, p.7; footnote 5, p.3 ("we use Õ notation
to hide poly(log n) terms").

**Formalization Note.** Real powers (`rpow`). For `k ≥ 1` and `c ≥ 1` the bases `log₂ n + 1` and
`k c` are `≥ 1` (`Real.logb 2 0 = 0`), so the rate is at least `C` for every `n`. A statement
"`… ≤ Õ((k·c)^{O(k)})`" is formalized as "there is `C`, depending only on the fixed structural
constants, with `… ≤ rate C n k c`". -/
noncomputable def rate (C : ℝ) (n k : ℕ) (c : ℝ) : ℝ :=
  C * (Real.logb 2 n + 1) ^ C * ((k : ℝ) * c) ^ (C * k)

end ParallelHAC


