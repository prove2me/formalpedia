-- Prove2me | Definitions.Def_TeschlODE_Horseshoe_shiftZ
-- name    : TeschlODE_Horseshoe_shiftZ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:35:28.951097+00:00
-- url     : https://prove2.me/theorems/c8be4be0-8c5a-4b61-ab82-a0649d9978fe
-- title:
--   The shift map $\sigma$ on the two-sided sequence space $\Sigma_N = \{0,\dots,N-1\}^{\mathbb{Z}}$
-- statement:
--   Let $\Sigma_N = \{0, \dots, N-1\}^{\mathbb{Z}}$ (11.34) be the space of doubly infinite sequences on $N$ symbols. The shift map is "defined as before":
--   $$\sigma(s)_n = s_{n+1}, \qquad n \in \mathbb{Z}.$$
--   Unlike the one-sided shift it is invertible. This is the "double sided shift on two symbols" of Theorem 13.1 when $N = 2$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 306, §11.5 (after Eq. (11.35)), and p. 333, §13.1

import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §11.5, p. 306 (after (11.35)) and §13.1, p. 333: the shift map on the two-sided
sequence space `Σ_N = {0, …, N − 1}^ℤ` (11.34), "defined as before": `σ(s)ₙ = sₙ₊₁` for all
`n ∈ ℤ`. On the two-sided space it is invertible. -/
def shiftZ {N : ℕ} (s : ℤ → Fin N) : ℤ → Fin N :=
  fun n => s (n + 1)

end TeschlODE.Horseshoe


