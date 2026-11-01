-- Prove2me | Definitions.Def_AndOrSched_alphaPoint
-- name    : AndOrSched_alphaPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:54.632077+00:00
-- url     : https://prove2.me/theorems/42120b23-6e4d-418a-8e22-45e0cf10b1b5
-- title:
--   $\alpha$-points and $\alpha$-intervals
-- statement:
--   For $0<\alpha\le1$, the **$\alpha$-point** of job $j$ in a solution $\bar x$ of LP (1) is
--   $$t^\alpha_j:=\min\Bigl\{t\ \Big|\ \sum_{s=1}^{t}\bar x_{js}\ge\alpha\Bigr\},$$
--   the first integer time at which an $\alpha$-fraction of $j$ is completed. The same formula over the intervals of LP (5) is the **$\alpha$-interval** $l^\alpha_j$.
--
--   **Formalization Note** The minimum is the infimum of a set of natural numbers; for $0<\alpha\le1$ and a feasible solution it lies in $[1,T]$ (resp. $[1,L]$).
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7, "tαj := min{t | Σs x̄js ≥ α}"; p.9, "lαj = min{l | …}"

import Mathlib
import Definitions.Def_AndOrSched_cum
open scoped Classical NNReal

namespace AndOrSched

/-- The `α`-point `tⱼ^α := min{t | Σ_{s=1}^{t} x̄_{js} ≥ α}` of job `j` in a solution of LP (1)
(Happach, Schulz, arXiv:2001.07011v1, §2, p.7), "the first integer point in time when an α-fraction of j is completed". The same
formula over intervals is the `α`-interval `lⱼ^α := min{l | Σ_{k=1}^{l} x̄_{jk} ≥ α}` of LP (5)
(§2, p.9).

**Formalization Note** The minimum is `sInf` over `ℕ`. For `0 < α ≤ 1` and a feasible LP solution
the set contains the horizon (by (1b), resp. (5b)) and not `0`, so the minimum exists and lies in
`[1, T]` (resp. `[1, L]`). -/
noncomputable def alphaPoint {J : Type} (x : J → ℕ → ℝ) (j : J) (α : ℝ) : ℕ :=
  sInf {t : ℕ | α ≤ cum x j t}

end AndOrSched


