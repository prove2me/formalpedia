-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_ellipNormSq
-- name    : FoundationsRL_LinUCB_ellipNormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:14.446111+00:00
-- url     : https://prove2.me/theorems/fa1b59aa-0cf6-4577-9dca-2a2935824661
-- title:
--   Squared matrix norm $\|v\|_S^2=\langle v,Sv\rangle$
-- statement:
--   For a square matrix $S$ and a vector $v$,
--
--   $$
--   \|v\|_S^2=\langle v,Sv\rangle.
--   $$
--
--   For positive semidefinite $S$ this is the square of the seminorm $\|v\|_S$ of footnote 11. It is used with $S=\widetilde\Sigma^t$ for the confidence ellipsoid and with $S=(\widetilde\Sigma^t)^{-1}$ for the width.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, footnote 11, p. 44

import Mathlib

open Matrix

namespace FoundationsRL.LinUCB

/-- The squared norm `∥v∥²_S = ⟨v, S v⟩` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, footnote 11, p. 44). -/
def ellipNormSq {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  v ⬝ᵥ (S *ᵥ v)

end FoundationsRL.LinUCB


