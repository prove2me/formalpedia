-- Prove2me | Definitions.Def_SeqExpDiffusion_IsHatC2With
-- name    : SeqExpDiffusion_IsHatC2With
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:56.637726+00:00
-- url     : https://prove2.me/theorems/a984668b-ae12-4799-9dbe-dfae9cb315f9
-- title:
--   $f\in\widehat{\mathcal C}^2$ with exceptional set $N$
-- statement:
--   A function $f$ belongs to $\widehat{\mathcal C}^2$ **with exceptional set** $N$ if
--
--   1. $f\in\mathcal C^1[0,1]$,
--   2. $N\subseteq[0,1]$ is finite, and
--   3. the second derivative $f''(\delta)$ exists for every $\delta\in[0,1]\setminus N$.
--
--   The quasi-variational inequalities (15) are imposed off this set $N$.
--
--   **Formalization Note** Derivatives are taken within $[0,1]$, one-sided at the endpoints.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (13), p.17

import Mathlib

namespace SeqExpDiffusion

/-- `f ∈ Ĉ²` with exceptional set `N`: `f ∈ C¹[0, 1]`, `N ⊆ [0, 1]` is finite, and the second
derivative `f″(δ)` exists for every `δ ∈ [0, 1] \ N`, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (13), p.17.

**Formalization Note** Derivatives on `[0, 1]` are taken within `[0, 1]` (one-sided at the
endpoints). `C¹[0, 1]` is `ContDiffOn ℝ 1 f [0, 1]`; "`f″(δ)` exists" is differentiability of
`derivWithin f [0, 1]` within `[0, 1]` at `δ`. -/
def IsHatC2With (f : ℝ → ℝ) (N : Set ℝ) : Prop :=
  ContDiffOn ℝ 1 f (Set.Icc 0 1) ∧ N.Finite ∧ N ⊆ Set.Icc 0 1 ∧
    ∀ δ ∈ Set.Icc (0 : ℝ) 1 \ N,
      DifferentiableWithinAt ℝ (derivWithin f (Set.Icc 0 1)) (Set.Icc 0 1) δ

end SeqExpDiffusion


