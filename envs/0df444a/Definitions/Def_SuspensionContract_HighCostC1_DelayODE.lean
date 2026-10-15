-- Prove2me | Definitions.Def_SuspensionContract_HighCostC1_DelayODE
-- name    : SuspensionContract_HighCostC1_DelayODE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:19.518252+00:00
-- url     : https://prove2.me/theorems/f9e9993f-c7c8-4ac9-93c0-9bb10f9f9a67
-- title:
--   (25)–(26), Lemma 2, Lemma 3, pp. 19–21 — the delay-ODE solution V_w̃, the threshold w̌(w̃), the concavification 𝒱_w̃ and the upper bound ŵ
-- statement:
--   This file defines the solutions of the working-state delay differential equation of Cao, Sun and Tian and the objects built from them.
--
--   For $\tilde w\ge0$, a function $V$ **solves (25)–(26)** if it is continuously differentiable on $[0,\tilde w]$ (with one-sided derivatives at the endpoints) and
--
--   $$(\mu+r)V(w)-\mu V\big((w+\beta)\wedge\tilde w\big)+\rho(\bar w-w)V'(w)-(\mu R-c)+(\rho-r)w=0,\qquad w\in[0,\tilde w],$$
--
--   together with the boundary condition $V(w)=\bar V(\tilde w)$ for all $w\ge\tilde w$. The equation looks ahead by $\beta$, so it is solved backwards from $\tilde w$. $V_{\tilde w}$ denotes such a solution (Lemma EC.2 of the paper shows it exists and is unique on $\mathbb R_+$ for $\tilde w\in[0,\bar w)$).
--
--   With $V',V''$ the first and second derivatives within $\mathbb R_+$ (right derivatives at $0$):
--
--   1. the **threshold** $\check w(\tilde w)$ is the supremum of the $x\in[0,\tilde w]$ such that $V_{\tilde w}''>0$ on $[0,x)$;
--   2. the **concavified function** of Lemma 2(ii) is
--   $$\mathcal V_{\tilde w}(w)=\begin{cases}V_{\tilde w}(\check w(\tilde w))+V_{\tilde w}'(\check w(\tilde w))\,(w-\check w(\tilde w)), & w<\check w(\tilde w),\\ V_{\tilde w}(w\wedge\tilde w), & w\ge\check w(\tilde w);\end{cases}$$
--   3. the **upper bound** $\hat{\mathrm w}$ of Lemma 3 (upright w; not the payment threshold $\hat w$ of Definition 1) is the infimum of the $w\in[0,\bar w)$ with $\mathcal V_w(0)=\underline v$; under Condition 1 there is exactly one such $w$ (Lemma 3).
--
--   These are the building blocks of the working-state value function $V_I=\mathcal V_{\hat{\mathrm w}}$ in the high-switching-cost regime.
--
--   **Formalization Note** $V_{\tilde w}$ is `Classical.choose` of a solution when one exists and the zero function otherwise; its values at $w<0$ are unconstrained and never used. $\check w(\tilde w)$ is defined through the sign of $V''$, not as the output of the paper's proof construction; Lemma 2(i) is what shows it has the stated sign pattern. $\hat{\mathrm w}$ is a junk value ($\inf\emptyset=0$) when no such $w$ exists, so every statement using it assumes Condition 1. The search range $[0,\bar w)$ follows Lemmas EC.2 and 3; Lemma 2 itself is stated for $\tilde w\in(0,\bar w)$.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 19 (25)–(26), p. 21 Lemma 2(i)–(ii), Lemma 3; p. ec23 Lemma EC.2

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_Setting

namespace SuspensionContract.HighCostC1

namespace Params

variable (P : Params)

/-- `V` solves the delay ODE (25) on `[0, w̃]` with boundary condition (26) (p. 19), in the class
`C¹([0, w̃])` of Lemma EC.2: `V` is continuously differentiable on `[0, w̃]` (one-sided derivatives
at the endpoints), (25) holds at every `w ∈ [0, w̃]` with `V′` the derivative within `[0, w̃]`,
and `V(w) = V̄(w̃)` for every `w ≥ w̃`. Values at `w < 0` are unconstrained. -/
def SolvesDDE (wt : ℝ) (V : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 V (Set.Icc 0 wt) ∧
    (∀ w ∈ Set.Icc 0 wt,
      (P.μ + P.r) * V w - P.μ * V (min (w + P.β) wt)
        + P.ρ * (P.wbar - w) * derivWithin V (Set.Icc 0 wt) w
        - (P.μ * P.R - P.c) + (P.ρ - P.r) * w = 0) ∧
    (∀ w, wt ≤ w → V w = P.VbarFn wt)

/-- `V_w̃`: a solution of (25)–(26), chosen when one exists (Lemma EC.2 asserts existence and
uniqueness on `ℝ₊` for `w̃ ∈ [0, w̄)`); the zero function otherwise (junk). -/
noncomputable def Vt (wt : ℝ) : ℝ → ℝ :=
  haveI := Classical.propDecidable (∃ V, P.SolvesDDE wt V)
  if h : ∃ V, P.SolvesDDE wt V then Classical.choose h else fun _ => 0

end Params

/-- First derivative within `ℝ₊` (two-sided at `w > 0`, right derivative at `0`). -/
noncomputable def d1 (f : ℝ → ℝ) (w : ℝ) : ℝ := derivWithin f (Set.Ici 0) w

/-- Second derivative within `ℝ₊`. -/
noncomputable def d2 (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  derivWithin (derivWithin f (Set.Ici 0)) (Set.Ici 0) w

namespace Params

variable (P : Params)

/-- The threshold `w̌(w̃)` of Lemma 2(i): the supremum of the `x ∈ [0, w̃]` such that
`V″_w̃ > 0` on `[0, x)`. -/
noncomputable def wcheck (wt : ℝ) : ℝ :=
  sSup {x : ℝ | 0 ≤ x ∧ x ≤ wt ∧ ∀ y, 0 ≤ y → y < x → 0 < d2 (P.Vt wt) y}

/-- The concavified function `𝒱_w̃` of Lemma 2(ii): the tangent line of `V_w̃` at `w̌(w̃)` for
`w < w̌(w̃)`, and `V_w̃(w ∧ w̃)` for `w ≥ w̌(w̃)`. -/
noncomputable def calV (wt : ℝ) (w : ℝ) : ℝ :=
  if w < P.wcheck wt then
    P.Vt wt (P.wcheck wt) + d1 (P.Vt wt) (P.wcheck wt) * (w - P.wcheck wt)
  else P.Vt wt (min w wt)

/-- The upper bound `ŵ` of Lemma 3 (upright w-hat): the infimum of the `w ∈ [0, w̄)` with
`𝒱_w(0) = v̲` (unique under Condition 1 by Lemma 3; junk `sInf ∅ = 0` otherwise). -/
noncomputable def what : ℝ :=
  sInf {w : ℝ | 0 ≤ w ∧ w < P.wbar ∧ P.calV w 0 = P.vlow}

end Params

end SuspensionContract.HighCostC1


