-- Prove2me | Definitions.Def_ExactModKL_Ieta
-- name    : ExactModKL_Ieta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:55:05.236679+00:00
-- url     : https://prove2.me/theorems/e3e7a3f9-230d-4246-bfcc-f49693806866
-- title:
--   The interval $[0,\eta)$ for $\eta\in(0,\infty]$
-- statement:
--   For $\eta\in(0,\infty]$, the half-open interval
--   $$
--   [0,\eta)=\{t\in\mathbb R:\ 0\le t<\eta\},
--   $$
--   which is $[0,\infty)$ when $\eta=\infty$. It is the domain of every desingularizing function in the class $\Phi_\eta$ and of the exact modulus.
--
--   **Formalization Note** $\eta$ is an extended nonnegative real ($\eta=\infty$ allowed), and $t<\eta$ is compared after embedding $t$ into $[0,\infty]$.
-- source:
--   Wang–Wang, arXiv:2008.13257v5, §3.1, definition of $\Phi_\eta$, p.8

import Mathlib

open scoped ENNReal

namespace ExactModKL

/-- The interval `[0, η)` for `η ∈ (0, ∞]`, as a set of reals: `t ≥ 0` and `t < η`, where `η`
may be `∞` (Wang–Wang, arXiv:2008.13257v5 (preprint), §3.1, p.8: "For η ∈ (0, ∞], denote by Φη
the class of functions ϕ : [0, η) → R+").

**Formalization Note.** `η : ℝ≥0∞`, so `η = ∞` is allowed and gives `[0, ∞)`; the comparison
`t < η` is `ENNReal.ofReal t < η`, which for `t ≥ 0` is the comparison of real numbers. -/
def Ieta (η : ℝ≥0∞) : Set ℝ := {t | 0 ≤ t ∧ ENNReal.ofReal t < η}

end ExactModKL


