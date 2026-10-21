-- Prove2me | Definitions.Def_JSEQDelay_Diffusion_Skorokhod
-- name    : JSEQDelay_Diffusion_Skorokhod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:16:57.726009+00:00
-- url     : https://prove2.me/theorems/9f5b887b-6e2c-48ff-883b-fc2e17520bcc
-- title:
--   Definition A.1 and (72)–(73), pp. 35–36 — the one-dimensional Skorokhod problem, map and oscillation
-- statement:
--   Let $x\in\mathbb D_+([0,\infty),\mathbb R)$, a right-continuous path with left limits and $x(0)\ge0$. A pair $(z,y)$ with $z$ RCLL and non-negative and $y$ RCLL, non-negative with $y(0)=0$ **solves the one-dimensional Skorokhod problem for $x$** if
--
--   1. $z(t)=x(t)+y(t)$ for all $t\ge0$;
--   2. $y$ is non-decreasing and can increase only when $z$ is zero: $\int_0^t z(s)\,dy(s)=0$ for all $t\ge0$.
--
--   The **Skorokhod map** is $\Gamma=(\Gamma_1,\Gamma_2)$ with
--   $$\Gamma_2(x)(t)=\sup_{0\le s\le t}(x(s))^-,\qquad \Gamma_1(x)(t)=x(t)+\Gamma_2(x)(t),$$
--   and the **oscillation** of a path on $[s,t]$ is $\mathrm{Osc}(f,[s,t])=\sup\{|f(u)-f(r)|: r,u\in[s,t]\}$.
--
--   The map describes a single queue: the scaled queue length is $\Gamma_1$ and the scaled idleness is $\Gamma_2$ of the net input (Remark 2.1, Remark 4.2).
--
--   **Formalization Note** $\Gamma_2$ is the published `skorokhodReg`. The complementarity condition is the published `StieltjesComplementary`, an integral over $[0,\infty)$ of a non-negative integrand, which vanishes exactly when every $\int_0^t$ does. The oscillation is computed in $[0,\infty]$.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), pp. 35–36, Appendix A, Definition A.1, Proposition A.2 (72)–(73) and property 1

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection

namespace JSEQDelay.Diffusion

open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-!
Atar & Lipshutz (authors' manuscript of January 12, 2020), Appendix A, pp. 35–36: the
one-dimensional Skorokhod problem and map. Paths are `ℝ → ℝ`, used only at `t ≥ 0`.
-/

/-- **Definition A.1** (pp. 35–36): for `x ∈ 𝔻₊([0, ∞), ℝ)`, the pair
`(z, y) ∈ 𝔻([0, ∞), ℝ₊) × 𝔻₀([0, ∞), ℝ₊)` solves the one-dimensional Skorokhod problem for `x`
iff `z` is RCLL and non-negative, `y` is RCLL, non-negative and `y(0) = 0`, and
1. `z(t) = x(t) + y(t)` for all `t ≥ 0`;
2. `y` is non-decreasing and can increase only when `z` is zero, i.e. `∫₀ᵗ z(s) dy(s) = 0`
   for all `t ≥ 0` (`StieltjesComplementary z y`: the integral over `[0, ∞)` vanishes). -/
def SkorokhodSolves (x z y : ℝ → ℝ) : Prop :=
  IsCadlag z ∧ (∀ t, 0 ≤ t → 0 ≤ z t) ∧
  IsCadlag y ∧ y 0 = 0 ∧ (∀ t, 0 ≤ t → 0 ≤ y t) ∧
  (∀ t, 0 ≤ t → z t = x t + y t) ∧
  MonotoneOn y (Set.Ici 0) ∧ StieltjesComplementary z y

/-- The Skorokhod map `Γ₁(x)(t) = x(t) + Γ₂(x)(t)` (72), with
`Γ₂(x)(t) = sup_{0 ≤ s ≤ t} (x(s))⁻` (73) the published `skorokhodReg`. -/
noncomputable def Gamma1 (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  x t + skorokhodReg x t

/-- The oscillation `Osc(f, [s, t]) = sup{|f(u) − f(r)| : r, u ∈ [s, t]}` (Proposition A.2,
property 1, p. 36), in `[0, ∞]`. -/
noncomputable def osc (f : ℝ → ℝ) (s t : ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (u : ℝ) (_ : r ∈ Set.Icc s t ∧ u ∈ Set.Icc s t), ENNReal.ofReal |f u - f r|

end JSEQDelay.Diffusion


