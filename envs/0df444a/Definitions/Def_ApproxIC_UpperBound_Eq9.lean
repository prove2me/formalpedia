-- Prove2me | Definitions.Def_ApproxIC_UpperBound_Eq9
-- name    : ApproxIC_UpperBound_Eq9
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:32.935917+00:00
-- url     : https://prove2.me/theorems/efc05bd7-d430-44e7-9854-b2a3e5f37e8c
-- title:
--   Eq. (9), p. 22 — the piecewise-linear inverse best response w with kink at p⋆, slopes m and 2 − m, ν₀ = v̄ − ε^β
-- statement:
--   This file defines the explicit path of eq. (9). For $\beta\in(0,1/2)$, $\varepsilon>0$, an upper end $\bar v$ and a price $p^\star$, set
--   $$\nu_0=\bar v-\varepsilon^\beta,\qquad m=\frac{\bar v-(p^\star+\varepsilon^{1-\beta})}{\nu_0-p^\star},$$
--   $$w(v)=\begin{cases} m\,(v-p^\star)+p^\star+\varepsilon^{1-\beta} & \text{if } v\ge p^\star,\\ (2-m)\,(v-p^\star)+p^\star+\varepsilon^{1-\beta} & \text{if } v\le p^\star,\end{cases}$$
--   and $\mu=w(0)=p^\star(m-1)+\varepsilon^{1-\beta}$. The inverse $v^\star$ of $w$ is
--   $$v^\star(v)=\begin{cases}\dfrac{v-p^\star-\varepsilon^{1-\beta}}{m}+p^\star & \text{if } v\ge p^\star+\varepsilon^{1-\beta},\\[2mm] \dfrac{v-p^\star-\varepsilon^{1-\beta}}{2-m}+p^\star & \text{otherwise.}\end{cases}$$
--   The number of steps $K$, Lemma 2's dual solution $\lambda^\star$ and the dual virtual value $\Delta$ under this path are the general objects of the path file applied to $(\bar v,\mu,\nu_0,v^\star,w)$.
--
--   The closest point of $w$ to the diagonal is $p^\star$, at distance $\varepsilon^{1-\beta}$; this choice balances the number of steps against the distance $w(x)-x$ in Lemmas 3 and 4.
--
--   **Formalization Note** The data are plain functions of $(\bar v,p^\star,\beta,\varepsilon)$, without a `Path` proof object; that eq. (9) is a path for small $\varepsilon$ ($m>1$, $2-m>0$, $0<\mu<\nu_0$) is a proof obligation of the milestones, not part of the definitions. All powers are real powers of the positive number $\varepsilon$.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 22, eq. (9); p. 44 (µ = w(0))

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Path

/-!
# The path of eq. (9) (arXiv:2103.03403v2, p. 22)

For `β ∈ (0, 1/2)` and `ε > 0`:
`w(v) = m (v − p⋆) + p⋆ + ε^{1−β}` if `v ≥ p⋆`, `(2 − m)(v − p⋆) + p⋆ + ε^{1−β}` if `v ≤ p⋆`,
`m = (v̄ − (p⋆ + ε^{1−β})) / (ν₀ − p⋆)`, `ν₀ = v̄ − ε^β`; `µ = w(0)` (p. 44). Its inverse `v⋆`
is written out piecewise. The thresholds, `K`, `λ` and `∆` are those of the `…Of` definitions
applied to these data.
-/

namespace ApproxIC.UpperBound

/-- `ν₀ = v̄ − ε^β`. -/
noncomputable def nu0Eq9 (vbar β ε : ℝ) : ℝ := vbar - ε ^ β

/-- `m = (v̄ − (p⋆ + ε^{1−β})) / (ν₀ − p⋆)`. -/
noncomputable def mEq9 (vbar pstar β ε : ℝ) : ℝ :=
  (vbar - (pstar + ε ^ (1 - β))) / (nu0Eq9 vbar β ε - pstar)

/-- `w` of eq. (9). -/
noncomputable def wEq9 (vbar pstar β ε : ℝ) (v : ℝ) : ℝ :=
  if pstar ≤ v then mEq9 vbar pstar β ε * (v - pstar) + pstar + ε ^ (1 - β)
  else (2 - mEq9 vbar pstar β ε) * (v - pstar) + pstar + ε ^ (1 - β)

/-- `µ = w(0)`. -/
noncomputable def muEq9 (vbar pstar β ε : ℝ) : ℝ := wEq9 vbar pstar β ε 0

/-- The inverse `v⋆` of eq. (9)'s `w`, piecewise around `w(p⋆) = p⋆ + ε^{1−β}`. -/
noncomputable def vstarEq9 (vbar pstar β ε : ℝ) (v : ℝ) : ℝ :=
  if pstar + ε ^ (1 - β) ≤ v then (v - pstar - ε ^ (1 - β)) / mEq9 vbar pstar β ε + pstar
  else (v - pstar - ε ^ (1 - β)) / (2 - mEq9 vbar pstar β ε) + pstar

/-- The number of steps `K` under eq. (9). -/
noncomputable def stepsEq9 (vbar pstar β ε : ℝ) : ℕ :=
  stepsOf vbar (muEq9 vbar pstar β ε) (vstarEq9 vbar pstar β ε)

/-- Lemma 2's `λ` under eq. (9). -/
noncomputable def lamStarEq9 (M : Model) (pstar β ε : ℝ) : ℝ → ℝ :=
  lamStarOf M (muEq9 M.vbar pstar β ε) (vstarEq9 M.vbar pstar β ε) (wEq9 M.vbar pstar β ε)

/-- `∆` under eq. (9), with `λ = lamStarEq9`. -/
noncomputable def DeltaEq9 (M : Model) (pstar β ε : ℝ) : ℝ → ℝ :=
  DeltaOf M (nu0Eq9 M.vbar β ε) (wEq9 M.vbar pstar β ε) (lamStarEq9 M pstar β ε)

end ApproxIC.UpperBound


