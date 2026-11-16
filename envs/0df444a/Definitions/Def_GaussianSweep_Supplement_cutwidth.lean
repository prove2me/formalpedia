-- Prove2me | Definitions.Def_GaussianSweep_Supplement_cutwidth
-- name    : GaussianSweep_Supplement_cutwidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:33:31.469627+00:00
-- url     : https://prove2.me/theorems/98048176-1047-4e39-81de-712c3449839c
-- title:
--   Cutwidth $\mathrm{cw}(G)$
-- statement:
--   The **cutwidth** of a finite graph $G$ with $n$ vertices is
--   $$
--   \mathrm{cw}(G) = \min_{v_1,\dots,v_n} \ \max_{1 \le i \le n} e(\{v_1,\dots,v_i\}),
--   $$
--   the minimum over all orderings $v_1,\dots,v_n$ of $V(G)$ of the largest number of edges leaving a prefix of the ordering.
--
--   Cutwidth sits between pathwidth and bisection width: the cut-sweep theorems bound it directly.
--
--   **Formalization Note** An ordering is a bijection $\sigma : \{0,\dots,n-1\} \to V$; the prefixes are $\{v : \sigma^{-1}(v) < i\}$ for $i = 0,\dots,n$, and including $i = 0$ changes nothing because $e(\emptyset) = 0$. The empty graph has cutwidth $0$. Natural-number valued.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14); Section 1.1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_GaussianSweep_Supplement_edgeBoundary

namespace GaussianSweep.Supplement

/-- The cutwidth `cw(G)` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14); Section 1.1,
p.1 (PDF p.3)): the minimum, over all orderings `v₁, …, vₙ` of `V(G)`, of
`maxᵢ e({v₁, …, vᵢ})`.

**Formalization Note** An ordering is a bijection `σ : Fin n ≃ V` (0-based, `n = |V|`); the
prefix of length `i` is `{v | σ⁻¹ v < i}`, for `i = 0, …, n`. Including `i = 0` changes nothing,
since `e(∅) = 0`; for `n = 0` the value is `0`. The maximum over the finitely many prefixes and
the minimum over the (nonempty, finite) set of orderings are `⨆` and `⨅` in `ℕ`. -/
noncomputable def cutwidth {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ⨅ σ : Fin (Fintype.card V) ≃ V,
    ⨆ i : Fin (Fintype.card V + 1), edgeBoundary G {v | ((σ.symm v : ℕ)) < (i : ℕ)}

end GaussianSweep.Supplement


