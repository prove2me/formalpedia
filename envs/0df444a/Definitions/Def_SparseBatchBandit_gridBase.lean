-- Prove2me | Definitions.Def_SparseBatchBandit_gridBase
-- name    : SparseBatchBandit_gridBase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:03.8722+00:00
-- url     : https://prove2.me/theorems/ba450b3f-585d-4386-b755-56d392715fe3
-- title:
--   Grid parameter $b$
-- statement:
--   The static grid of LBGL is driven by the number
--
--   $$
--   b=\sqrt T\,\Big(\frac{T}{s_0}\Big)^{\frac{1}{2(2^M-1)}}.
--   $$
--
--   It is chosen so that the recursion $t_1=b\sqrt{s_0}$, $t_m=b\sqrt{t_{m-1}}$ ends at $t_M=T$ when no rounding is applied.
--
--   **Formalization Note** The paper writes $b=\Theta(\cdot)$ with the requirement $t_M=T$. This exact value satisfies that requirement for the unrounded recursion.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §4.1, p.16

import Mathlib

namespace SparseBatchBandit

/-- The grid parameter `b = √T · (T/s₀)^{1/(2(2^M−1))}`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §4.1, p.16 (PDF 16).

**Formalization Note.** The page writes `b = Θ(·)`, chosen so that `t_M = T`. The exact value
taken here makes the unrounded recursion `t₁ = b√s₀`, `t_m = b√t_{m−1}` reach `T` at `m = M`
exactly. `2^M − 1` is computed in `ℝ`. -/
noncomputable def gridBase (T s₀ M : ℕ) : ℝ :=
  Real.sqrt T * ((T : ℝ) / s₀) ^ ((1 : ℝ) / (2 * ((2 : ℝ) ^ M - 1)))

end SparseBatchBandit


