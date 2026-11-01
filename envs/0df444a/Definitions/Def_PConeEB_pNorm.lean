-- Prove2me | Definitions.Def_PConeEB_pNorm
-- name    : PConeEB_pNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:53.647539+00:00
-- url     : https://prove2.me/theorems/76ac3595-d184-4a53-a0a7-fe3ca220c69e
-- title:
--   The $p$-norm $\|\cdot\|_p$
-- statement:
--   For $p\in(1,\infty)$ and $\bar x\in\mathbb R^n$,
--   $$
--   \|\bar x\|_p:=\bigl(|\bar x_1|^p+\dots+|\bar x_n|^p\bigr)^{1/p}.
--   $$
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, (4.1), p.17

import Mathlib

namespace PConeEB

/-- The `p`-norm `‖x‖_p := (|x₁|^p + ⋯ + |x_n|^p)^{1/p}`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, (4.1), p.17.

**Formalization Note.** Plain real powers of absolute values, for a real parameter `p`, not the norm
of a `PiLp` space. -/
noncomputable def pNorm {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

end PConeEB


