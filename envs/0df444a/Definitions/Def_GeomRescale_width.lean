-- Prove2me | Definitions.Def_GeomRescale_width
-- name    : GeomRescale_width
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:08.015994+00:00
-- url     : https://prove2.me/theorems/82ad1a68-f565-4166-84c8-7a0027b79e5d
-- title:
--   The width of a set in a direction
-- statement:
--   For a set $X \subset \mathbb{R}^n$ and $a \in \mathbb{R}^n$,
--
--   $$\operatorname{width}_X(a) = \max\{a^{\mathsf T} z : z \in X\}.$$
--
--   **Formalization Note** The maximum is a `sSup`. The mission uses it on $F_\mu$, which is compact and contains $0$.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.3, p.11

import Mathlib

namespace GeomRescale

/-- The width `width_X(a) = max {aᵀz : z ∈ X}` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.3, p.11).

**Formalization Note.** `sSup`; the mission uses it for `X = F_μ`, which is compact and contains `0`,
so the supremum is the maximum. -/
noncomputable def width {n : ℕ} (X : Set (Fin n → ℝ)) (a : Fin n → ℝ) : ℝ :=
  sSup ((fun z => a ⬝ᵥ z) '' X)

end GeomRescale


