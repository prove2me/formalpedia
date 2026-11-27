-- Prove2me | Definitions.Def_RiskBalancingMNL_Supplement_zeta
-- name    : RiskBalancingMNL_Supplement_zeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:55:49.897101+00:00
-- url     : https://prove2.me/theorems/d8d7a4b7-bb22-416f-b16a-1640a796b3de
-- title:
--   The fixed-point objects of §5.2: $m_j(\pi,\theta)$, $\zeta(\theta)$, $\theta(\pi)$, $f(\pi)$ and $\pi^o$
-- statement:
--   For the MNL model with asymmetric price sensitivities, a risk weight $\lambda>0$, a profit level $\pi$ and $\theta\ge0$, the markups (24) are
--   $$
--   m_j(\pi,\theta)=\frac1{\hat b_j}+\frac\pi\lambda-\sqrt{\Big(\frac1{\hat b_j}\Big)^2+\theta},
--   $$
--   and $q_i(\pi,\theta)$ (25) are the MNL shares at these markups. The function $\zeta$ of p.18 is
--   $$
--   \zeta(\theta)=\Big(\frac\pi\lambda\Big)^2+2\sum_{i=1}^n\frac{e^{\hat a_i-\hat b_ic_i-1}}{\hat b_i}\Big(\frac1{\hat b_i}-\sqrt{\big(\tfrac1{\hat b_i}\big)^2+\theta}\Big)\exp\Big(-\hat b_i\Big(\frac\pi\lambda-\sqrt{\big(\tfrac1{\hat b_i}\big)^2+\theta}\Big)\Big)-\theta ,
--   $$
--   $\theta(\pi)$ is its unique root in $[0,\infty)$, and the fixed-point map (27) is
--   $$
--   f(\pi)=\sum_im_i(\pi,\theta(\pi))\,q_i(\pi,\theta(\pi)).
--   $$
--   Finally $\pi^o$ is the profit-maximizing profit, the supremum of $\pi(m)$ over all markup vectors.
--
--   These are the objects of the paper's reduction of the asymmetric problem to a one-dimensional fixed-point search over $\pi\in[0,\pi^o]$, and of Theorem 4.
--
--   **Formalization Note** $\theta(\pi)$ is the witness of "there is exactly one $\theta\ge0$ with $\zeta(\theta)=0$" when that holds, and the value $0$ otherwise; the claim of p.18 (a milestone of this mission) says the root always exists and is unique. $\pi^o$ is `sSup` of the range of the profit; for $n\ge1$ the profit is bounded above and the supremum is attained. Division by $\lambda$ makes these objects meaningful only for $\lambda>0$.
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §5.2, (24)–(27) and the definition of $\zeta$ and $\theta(\pi)$, p.18; $\pi^o$, p.19

import Mathlib
import Definitions.Def_RiskBalancingMNL_Supplement_AsymParams

namespace RiskBalancingMNL.Supplement

variable {n : ℕ}

/-- The markups (24) as functions of `(π, θ)`, Li & Webster, SSRN 3959428 (PDF of 2021-11-14),
§5.2, p.18: `mⱼ(π, θ) = 1/b̂ⱼ + π/λ − √((1/b̂ⱼ)² + θ)`. The shares `qᵢ(π, θ)` of (25) are
`P.share (markupPT P lam π θ) i`. -/
noncomputable def markupPT (P : AsymParams n) (lam π θ : ℝ) : Fin n → ℝ :=
  fun j => 1 / P.bHat j + π / lam - Real.sqrt ((1 / P.bHat j) ^ 2 + θ)

/-- The function `ζ` of SSRN 3959428, p.18, for given `π` and `λ`:
`ζ(θ) = (π/λ)² + 2 Σᵢ (e^{âᵢ−b̂ᵢcᵢ−1}/b̂ᵢ) (1/b̂ᵢ − √((1/b̂ᵢ)² + θ)) exp(−b̂ᵢ(π/λ − √((1/b̂ᵢ)² + θ))) − θ`.

**Formalization Note** Used for `λ > 0` and `θ ≥ 0`; at `λ = 0` Lean's `π / 0 = 0` is a junk
value. -/
noncomputable def zeta (P : AsymParams n) (lam π θ : ℝ) : ℝ :=
  (π / lam) ^ 2 +
    2 * ∑ i, Real.exp (P.aHat i - P.bHat i * P.c i - 1) / P.bHat i *
      (1 / P.bHat i - Real.sqrt ((1 / P.bHat i) ^ 2 + θ)) *
      Real.exp (-(P.bHat i * (π / lam - Real.sqrt ((1 / P.bHat i) ^ 2 + θ)))) - θ

/-- `θ(π)`, the unique root of `ζ` in `[0, ∞)` (SSRN 3959428, p.18: "there exists a unique `θ`
that satisfies `ζ(θ) = 0` for any `π`, which we denote with `θ(π)`").

**Formalization Note** Defined as the witness of `∃! θ, 0 ≤ θ ∧ ζ(θ) = 0` when that holds, and the
junk value `0` otherwise; the companion claim `zeta_unique_root` says the root always exists and is
unique for `λ > 0`, so the junk branch is never taken there. -/
noncomputable def thetaOf (P : AsymParams n) (lam π : ℝ) : ℝ :=
  open Classical in
  if h : ∃! θ : ℝ, 0 ≤ θ ∧ zeta P lam π θ = 0 then Classical.choose h else 0

/-- The fixed-point map (27), SSRN 3959428, p.18:
`f(π) := Σᵢ mᵢ(π, θ(π)) qᵢ(π, θ(π))`, the expected profit of the markups (24) at `θ = θ(π)`. -/
noncomputable def fixedPointMap (P : AsymParams n) (lam π : ℝ) : ℝ :=
  ∑ i, markupPT P lam π (thetaOf P lam π) i * P.share (markupPT P lam π (thetaOf P lam π)) i

/-- `π°`, the profit-maximizing profit (the case `λ = 0`), SSRN 3959428, p.19: the right end of the
search interval `[0, π°]`.

**Formalization Note** Defined as `sSup` of the expected profit over all markup vectors in `ℝⁿ`.
For `n ≥ 1` the profit is bounded above and the supremum is attained (it is the optimal value of
problem (6) at `λ = 0`, whose objective is `π²` on `π ≥ 0`); for an unbounded set Lean's `sSup`
would be the junk value `0`, which does not occur. -/
noncomputable def piO (P : AsymParams n) : ℝ :=
  sSup (Set.range P.profit)

end RiskBalancingMNL.Supplement


