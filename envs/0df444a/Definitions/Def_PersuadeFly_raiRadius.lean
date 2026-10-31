-- Prove2me | Definitions.Def_PersuadeFly_raiRadius
-- name    : PersuadeFly_raiRadius
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:11.481986+00:00
-- url     : https://prove2.me/theorems/3e53ed7a-e9ad-4195-b2c4-abef9ce49b8b
-- title:
--   The radii $\epsilon_t=\min\{\sqrt{|\Omega|/t}\,(1+\sqrt{\Phi\log T}),2\}$
-- statement:
--   For a parameter $\Phi>0$ and a horizon $T$, the radii of Theorems 1 and 2:
--   $$
--   \epsilon_t=\min\Big\{\sqrt{\frac{|\Omega|}{t}}\,\big(1+\sqrt{\Phi\log T}\big),\ 2\Big\},\qquad t\ge1 .
--   $$
--
--   **Formalization Note** $\log$ is the natural logarithm. The formula divides by $t$ and is used for $t\ge1$ only; the first set of Rai is handled separately (see the confidence sets).
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Theorem 1, p.22; Theorem 2, p.27

import Mathlib

namespace PersuadeFly

/-- **The radii `ϵ_t` of Theorems 1 and 2.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Theorem 1, p.22, and Theorem 2, p.27:
`ϵ_t = min{√(|Ω|/t) (1 + √(Φ log T)), 2}`, the radical covering `|Ω|/t` only.

**Formalization Note** `log` is the natural logarithm (`Real.log`). The formula is used for
`t ≥ 1` only: at `t = 0` it divides by zero (Lean returns `0`), and the first set of Rai is the
set `C₀` of `raiSet` instead. -/
noncomputable def raiRadius (Ω : Type) [Fintype Ω] (Φ : ℝ) (T t : ℕ) : ℝ :=
  min (Real.sqrt ((Fintype.card Ω : ℝ) / t) * (1 + Real.sqrt (Φ * Real.log T))) 2

end PersuadeFly


