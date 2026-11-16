-- Prove2me | Definitions.Def_GaussianSweep_Supplement_bisectionWidth
-- name    : GaussianSweep_Supplement_bisectionWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:34:04.479837+00:00
-- url     : https://prove2.me/theorems/4d4e753e-15fe-4885-ba7a-7c0c0e1b7a4b
-- title:
--   Bisection width $\mathrm{bw}(G)$
-- statement:
--   The **bisection width** of a finite graph $G$ with $n$ vertices is the minimum of $e(X)$ over all $X \subseteq V(G)$ with $|X| = \lfloor n/2 \rfloor$:
--   $$
--   \mathrm{bw}(G) = \min\{ e(X) : X \subseteq V(G),\ |X| = \lfloor n/2 \rfloor \}.
--   $$
--   Since $e(X) = e(V(G)\setminus X)$, this is the minimum number of edges between the two sides of a partition of $V(G)$ into parts whose sizes differ by at most one.
--
--   **Formalization Note** $\lfloor n/2\rfloor$ is natural-number division; the set of admissible values is nonempty, so the infimum in $\mathbb N$ is a minimum.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_GaussianSweep_Supplement_edgeBoundary

namespace GaussianSweep.Supplement

/-- The bisection width `bw(G)` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14)): the
minimum of `e(X)` over all `X ⊆ V(G)` with `|X| = ⌊n/2⌋`.

**Formalization Note** `n = Fintype.card V` and `⌊n/2⌋` is natural-number division
`Fintype.card V / 2`. The set of admissible values is nonempty (some `X` has `⌊n/2⌋` elements),
so `sInf` in `ℕ` is its minimum. Since `e(X) = e(V ∖ X)`, this agrees with the introduction's
"partition into parts whose sizes differ by at most one" (p.1). -/
noncomputable def bisectionWidth {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ X : Set V, X.ncard = Fintype.card V / 2 ∧ edgeBoundary G X = k}

end GaussianSweep.Supplement


