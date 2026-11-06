-- Prove2me | Definitions.Def_TiltedCvx_tau
-- name    : TiltedCvx_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:12.743199+00:00
-- url     : https://prove2.me/theorems/7746d457-fcde-4e38-8e45-4850a3b6b068
-- title:
--   The root $\tau_\gamma$ of $\tau^\gamma+\tau=1$
-- statement:
--   For $\gamma\in(0,1]$, $\tau_\gamma\in(0,1/2]$ is the unique solution of
--
--   $$
--   \tau_\gamma^{\gamma}+\tau_\gamma=1 .
--   $$
--
--   For example $\tau_1=1/2$. It determines the sharp secant parameter $\eta(\gamma)$ of Theorem 22.
--
--   **Formalization Note** Defined without presupposing existence or uniqueness, as $\sup\{t\in[0,1/2] : t^\gamma+t\le1\}$ (real powers). For $\gamma\in(0,1]$ the map $t\mapsto t^\gamma+t$ is continuous and strictly increasing on $[0,\infty)$, equals $0$ at $0$ and is at least $1$ at $1/2$, so the supremum is the root; that it solves the equation uniquely is part of Theorem 22.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 22, (23), p.27

import Mathlib

namespace TiltedCvx

/-- **The root `τγ`.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 22, (23), p.27:
for `γ ∈ (0, 1]`, `τγ ∈ (0, 1/2]` is the unique solution of `τγ^γ + τγ = 1`.

**Formalization Note** Defined without presupposing existence or uniqueness, as
`sup{t ∈ [0, 1/2] : t^γ + t ≤ 1}` (real power `Real.rpow`). For `γ ∈ (0, 1]` the map
`t ↦ t^γ + t` is continuous and strictly increasing on `[0, ∞)`, is `0` at `0` and at least `1` at
`1/2`, so this supremum is the paper's `τγ`; that it solves (23) uniquely is part of Theorem 22. -/
noncomputable def tau (γ : ℝ) : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ t ^ γ + t ≤ 1}

end TiltedCvx


