-- Prove2me | Definitions.Def_PConeEB_pCone
-- name    : PConeEB_pCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:35.127935+00:00
-- url     : https://prove2.me/theorems/95eeaef2-f868-407a-93d6-45ae070452ec
-- title:
--   The $p$-cone $\mathcal K_p^{n+1}$
-- statement:
--   For $p\in(1,\infty)$ and $n\ge2$, the **$p$-cone** is
--   $$
--   \mathcal K_p^{n+1}:=\{x=(x_0,\bar x)\in\mathbb R^{n+1}: x_0\ge\|\bar x\|_p\}.
--   $$
--   For $p=2$ this is the second-order cone. For $p\in(1,\infty)$ every face is $\{0\}$, an extreme ray, or the cone itself.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, (4.1), p.17

import Mathlib
import Definitions.Def_PConeEB_RR
import Definitions.Def_PConeEB_pNorm

namespace PConeEB

/-- The `p`-cone `K_p^{n+1} := {x = (x₀, x̄) ∈ ℝ^{n+1} | x₀ ≥ ‖x̄‖_p}`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, (4.1), p.17. -/
noncomputable def pCone (n : ℕ) (p : ℝ) : Set (RR n) :=
  {x | pNorm p (fun i : Fin n => x i.succ) ≤ x 0}

end PConeEB


