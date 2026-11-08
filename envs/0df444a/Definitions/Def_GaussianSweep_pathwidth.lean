-- Prove2me | Definitions.Def_GaussianSweep_pathwidth
-- name    : GaussianSweep_pathwidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:47.817499+00:00
-- url     : https://prove2.me/theorems/e118d835-d69f-4a47-960d-1c4af9de6033
-- title:
--   Pathwidth $\mathrm{pw}(G)$
-- statement:
--   The **pathwidth** $\mathrm{pw}(G)$ of a finite graph $G$ is the minimum width of a path decomposition of $G$:
--   $$
--   \mathrm{pw}(G) = \min\Big\{\max_{1 \le i \le s} |W_i| - 1 \;:\; W_1, \dots, W_s \text{ a path decomposition of } G\Big\}.
--   $$
--   The empty graph has $\mathrm{pw} = -1$.
--
--   **Formalization Note** The value is an integer, taken as the infimum in $\mathbb Z$ of the set of widths; for a finite graph this set is nonempty (the single bag $V(G)$) and bounded below by $-1$, so the infimum is the minimum, and for the empty graph the decomposition with one empty bag gives $-1$. For an infinite vertex type the set may be empty and the value is the junk $0$; the mission uses finite graphs only.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14); Section 4.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_GaussianSweep_IsPathDecomposition

namespace GaussianSweep

/-- The pathwidth `pw(G)` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14); Section 4.1, p.22
(PDF p.24)): the minimum width `maxᵢ |Wᵢ| − 1` of a path decomposition of `G`.

**Formalization Note** Integer valued. For a finite graph the set of widths is nonempty (the
one-bag decomposition `[V]`) and bounded below by `−1`, so `sInf` is its minimum; the empty graph
has `pw = −1` (p.22) through the decomposition with one empty bag. For an infinite vertex type the
set can be empty and `sInf` returns `0`; the mission only uses finite graphs. -/
noncomputable def pathwidth {V : Type*} (G : SimpleGraph V) : ℤ :=
  sInf {w : ℤ | ∃ (s : ℕ) (W : Fin s → Finset V), IsPathDecomposition G s W ∧
    w = ((Finset.univ.sup fun i => (W i).card : ℕ) : ℤ) - 1}

end GaussianSweep


