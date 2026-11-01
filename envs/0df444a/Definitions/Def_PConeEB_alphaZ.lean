-- Prove2me | Definitions.Def_PConeEB_alphaZ
-- name    : PConeEB_alphaZ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:34.218151+00:00
-- url     : https://prove2.me/theorems/475d2ef0-74b2-413e-8227-3d5fbcc2dd6e
-- title:
--   The exponent $\alpha_z$ of (4.6)
-- statement:
--   For $p\in(1,\infty)$ and $z\in\mathbb R^{n+1}$,
--   $$
--   \alpha_z:=\begin{cases}\tfrac12&\text{if }|J_z|=n,\\ \tfrac1p&\text{if }|J_z|=1\text{ and }p<2,\\ \min\{\tfrac12,\tfrac1p\}&\text{otherwise.}\end{cases}
--   $$
--   This is the exponent of the optimal Hölderian error bound for the $p$-cone.
--
--   **Formalization Note** The three cases are tested in this order. For $n\ge2$ the first two exclude each other.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, (4.6), p.19

import Mathlib
import Definitions.Def_PConeEB_Jz

namespace PConeEB

/-- The exponent `α_z` of (4.6): `1/2` if `|J_z| = n`; `1/p` if `|J_z| = 1` and `p < 2`;
`min{1/2, 1/p}` otherwise. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, (4.6), p.19. -/
noncomputable def alphaZ {n : ℕ} (p : ℝ) (z : RR n) : ℝ :=
  if (Jz z).card = n then 1 / 2
  else if (Jz z).card = 1 ∧ p < 2 then 1 / p
  else min (1 / 2) (1 / p)

end PConeEB


