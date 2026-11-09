-- Prove2me | Definitions.Def_GevreyGibbsSep_Grid
-- name    : GevreyGibbsSep_Grid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:50.573406+00:00
-- url     : https://prove2.me/theorems/1b11e988-3ca5-4d4e-9995-655772112aa5
-- title:
--   Index set of the $N$-grid
-- statement:
--   The $N$-grid is $\frac{2\pi}{2N+1}[-N,\dots,N]^d$; this item is its index set $[-N,\dots,N]^d$.
--
--   **Formalization Note** An index $k\in\{0,\dots,2N\}$ stands for $k-N\in\{-N,\dots,N\}$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Appendix A 1, p.20

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Index set of the `N`-grid `(2π/(2N + 1)) [−N, …, N]^d` (arXiv:2608.24527 (sha256
d4fd40eb…), Appendix A 1, p.20).

**Formalization Note** The index `k ∈ {0, …, 2N}` stands for `k − N ∈ {−N, …, N}`. -/
abbrev Grid (d N : ℕ) : Type := Fin d → Fin (2 * N + 1)

end GevreyGibbsSep


