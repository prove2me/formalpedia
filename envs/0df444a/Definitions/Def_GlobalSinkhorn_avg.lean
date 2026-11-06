-- Prove2me | Definitions.Def_GlobalSinkhorn_avg
-- name    : GlobalSinkhorn_avg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:21:22.457227+00:00
-- url     : https://prove2.me/theorems/cdbac499-212e-4d7e-8b90-9ff20b910c12
-- title:
--   The average $\langle v\rangle$ of a vector
-- statement:
--   For a vector $v\in\mathbb R^n$ the **average** of its entries is
--   $$
--   \langle v\rangle=\frac1n\sum_{j=1}^n v_j .
--   $$
--   Together with componentwise powers and reciprocals, this is the notation in which the scale-invariant potential $\Phi$ and the second-moment bound (26) are written.
--
--   **Formalization Note** Indices are `Fin n` (0-based). At $n=0$ Lean's total division gives the value $0$; every statement of the mission assumes $n\ge1$ or $n\ge2$.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Section 2 (Preliminary), p.13

import Mathlib

open Matrix

namespace GlobalSinkhorn

/-- The average `⟨z⟩ = (1/n) ∑ⱼ zⱼ`. He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), p.13.

**Formalization Note.** At `n = 0` the value is `0` by total division; the paper's `n` is a
positive integer, and every statement of the mission assumes `0 < n` or `2 ≤ n`. -/
noncomputable def avg {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (∑ j, z j) / n

end GlobalSinkhorn


