-- Prove2me | Definitions.Def_TiltedCvx_Supplement_binMean
-- name    : TiltedCvx_Supplement_binMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:23:29.927701+00:00
-- url     : https://prove2.me/theorems/e0d7aa92-38fd-4be8-b320-2e3c74e45248
-- title:
--   Binary tilted mean $M_{\gamma,\lambda}(a,b)$
-- statement:
--   For $\gamma\in(0,1]$, $\lambda\in[0,1]$ and $a,b\in\mathbb R$,
--
--   $$
--   M_{\gamma,\lambda}(a,b):=\begin{cases}\dfrac{\gamma\lambda a+(1-\lambda)b}{\gamma\lambda+(1-\lambda)},&a\le b,\\[2ex]\dfrac{\lambda a+\gamma(1-\lambda)b}{\lambda+\gamma(1-\lambda)},&a>b,\end{cases}\qquad\text{(14)}
--   $$
--
--   and for $\gamma=0$, $M_{0,\lambda}(a,b):=\max\{a,b\}$ (15). The mean multiplies by $\gamma$ the weight of the smaller value; $M_{1,\lambda}$ is the arithmetic mean $\lambda a+(1-\lambda)b$. For $\gamma>0$ it is the upper expectile at level $1/(1+\gamma)$ of the two-point distribution. It gives the Jensen form of tilted secant convexity (Theorem 18).
--
--   **Formalization Note** The $\gamma=0$ convention is a separate branch; for $\gamma\in(0,1]$, $\lambda\in[0,1]$ the denominators are positive.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, (14)–(15), p.25

import Mathlib

namespace TiltedCvx.Supplement

/-- **The binary mean `M_{γ,λ}(a, b)` ((14)–(15)).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, (14) and (15), p.25: for `γ ∈ (0, 1]`, `λ ∈ [0, 1]` and `a, b ∈ ℝ`,
`M_{γ,λ}(a, b) := (γλa + (1 − λ)b)/(γλ + (1 − λ))` if `a ≤ b`, and
`(λa + γ(1 − λ)b)/(λ + γ(1 − λ))` if `a > b`; for `γ = 0`, `M_{0,λ}(a, b) := max{a, b}`.

**Formalization Note** The `γ = 0` convention (15) is a separate branch. For `γ ∈ (0, 1]` and
`λ ∈ [0, 1]` both denominators are positive; only these parameters are used. -/
noncomputable def binMean (γ l a b : ℝ) : ℝ :=
  if γ = 0 then max a b
  else if a ≤ b then (γ * l * a + (1 - l) * b) / (γ * l + (1 - l))
  else (l * a + γ * (1 - l) * b) / (l + γ * (1 - l))

end TiltedCvx.Supplement


