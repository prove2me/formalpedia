-- Prove2me | Definitions.Def_SparseBatchBandit_gridRaw
-- name    : SparseBatchBandit_gridRaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:55.762192+00:00
-- url     : https://prove2.me/theorems/6ef13cab-b006-41a0-87ba-1f37edfc20ae
-- title:
--   Grid recursion $t_m=\lfloor b\sqrt{t_{m-1}}\rfloor$
-- statement:
--   The grid points before the last one are given by the recursion
--
--   $$
--   t_0=0,\qquad t_1=\min\{T,\lfloor b\sqrt{s_0}\rfloor\},\qquad t_m=\min\{T,\lfloor b\sqrt{t_{m-1}}\rfloor\}\quad(m\ge2).
--   $$
--
--   **Formalization Note** The paper's text floors $t_m$ for $m\ge2$ and leaves $t_1$ unfloored; a grid point is a round, so $t_1$ is floored as well. The cap at $T$ acts only when $s_0>T$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §4.1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_gridBase

namespace SparseBatchBandit

/-- The recursion of the static grid before its last point: `t₀ = 0`, `t₁ = ⌊b√s₀⌋`,
`t_m = ⌊b√t_{m−1}⌋`, each capped at `T`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §4.1, p.16 (PDF 16).

**Formalization Note.** The page has the floor on `t_m` for `m ≥ 2` and none on `t₁`; a grid point
is a round, so `t₁` is floored too. The cap matters only when `s₀ > T`. -/
noncomputable def gridRaw (T s₀ M : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => min T ⌊gridBase T s₀ M * Real.sqrt s₀⌋₊
  | m + 2 => min T ⌊gridBase T s₀ M * Real.sqrt (gridRaw T s₀ M (m + 1))⌋₊

end SparseBatchBandit


