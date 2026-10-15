-- Prove2me | Definitions.Def_SuspensionContract_ControlBand_DelayODE
-- name    : SuspensionContract_ControlBand_DelayODE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:44.059985+00:00
-- url     : https://prove2.me/theorems/374ffebe-edf5-4bc0-9a9c-876282d9e462
-- title:
--   (25)–(26), p. 19; Lemma 2, p. 21; Lemma 3, p. 21 — the delay-ODE solution V_w̃, its concavification 𝒱_w̃, the threshold w̌(w̃) and the upper bound ŵ
-- statement:
--   For $\tilde w\in[0,\bar w)$, the working-state value function $V_{\tilde w}$ is a $C^1$ function on $[0,\tilde w]$ solving the delay differential equation
--   $$(\mu+r)V_{\tilde w}(w)-\mu V_{\tilde w}((w+\beta)\wedge\tilde w)+\rho(\bar w-w)V_{\tilde w}'(w)-(\mu R-c)+(\rho-r)w=0,\qquad w\in[0,\tilde w],\quad(25)$$
--   with the boundary condition $V_{\tilde w}(w)=\bar V(\tilde w)$ for all $w\ge\tilde w$ (26). The file defines the predicate "$V$ solves (25)–(26)" and lets $V_{\tilde w}$ be a solution when one exists (a junk function otherwise; existence and uniqueness is the paper's Lemma EC.2).
--
--   With $V'$ and $V''$ the derivatives within $\mathbb R_+$, it defines
--   1. the threshold $\check w(\tilde w)=\sup\{x\in[0,\tilde w]: V_{\tilde w}''>0\text{ on }[0,x)\}$ of Lemma 2(i);
--   2. the concavified function of Lemma 2(ii),
--   $$\mathcal V_{\tilde w}(w)=\begin{cases}V_{\tilde w}(\check w(\tilde w))+V_{\tilde w}'(\check w(\tilde w))\,(w-\check w(\tilde w)),& w<\check w(\tilde w),\\ V_{\tilde w}(w\wedge\tilde w),& w\ge\check w(\tilde w);\end{cases}$$
--   3. the upper bound $\hat{\mathrm w}=\inf\{w\in[0,\bar w):\mathcal V_w(0)=\underline v\}$ of Lemma 3, which is unique under Condition 1.
--
--   These are the building blocks of the working-state value function in every parameter region of the paper.
--
--   **Formalization Note.** Three different hats appear in the paper: Definition 1's payment threshold $\hat w$, Lemma 3's $\hat{\mathrm w}$ (this file, `what`), and Proposition 6's bold $\hat{\mathbf w}$ (a free parameter in this mission). The derivative in (25) is taken within $[0,\tilde w]$; elsewhere derivatives are within $\mathbb R_+$ (`d1`, `d2`). $\check w$ is defined by the sign pattern's supremum, not by the property Lemma 2(i) asserts. Values at $w<0$ are irrelevant and unconstrained.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 19, (25)–(27); p. 21, Lemma 2(i)–(ii), Lemma 3; p. ec23, Lemma EC.2

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Setting

namespace SuspensionContract.ControlBand

namespace Params

variable (P : Params)

/-- `V` solves the delay ODE (25) on `[0, w̃]` with boundary condition (26), p. 19: `V` is `C¹` on
`[0, w̃]` (derivative within `[0, w̃]`, one-sided at the ends),
`(µ + r)V(w) − µV((w + β) ∧ w̃) + ρ(w̄ − w)V′(w) − (µR − c) + (ρ − r)w = 0` on `[0, w̃]`, and
`V(w) = V̄(w̃)` for all `w ≥ w̃`. Values at `w < 0` are left free. -/
def SolvesDDE (wt : ℝ) (V : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 V (Set.Icc 0 wt) ∧
    (∀ w ∈ Set.Icc 0 wt,
      (P.μ + P.r) * V w - P.μ * V (min (w + P.β) wt)
        + P.ρ * (P.wbar - w) * derivWithin V (Set.Icc 0 wt) w
        - (P.μ * P.R - P.c) + (P.ρ - P.r) * w = 0) ∧
    ∀ w, wt ≤ w → V w = P.VbarFn wt

open Classical in
/-- `V_w̃`: a solution of (25)–(26) when one exists (Lemma EC.2 asserts existence and uniqueness on
`ℝ₊` for `w̃ ∈ [0, w̄)`), and the junk function `0` otherwise. -/
noncomputable def Vt (wt : ℝ) : ℝ → ℝ :=
  if h : ∃ V, P.SolvesDDE wt V then Classical.choose h else fun _ => 0

end Params

/-- First derivative within `ℝ₊` (two-sided at `w > 0`, right-sided at `0`). -/
noncomputable def d1 (f : ℝ → ℝ) (w : ℝ) : ℝ := derivWithin f (Set.Ici 0) w

/-- Second derivative within `ℝ₊`. -/
noncomputable def d2 (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  derivWithin (derivWithin f (Set.Ici 0)) (Set.Ici 0) w

namespace Params

variable (P : Params)

/-- `w̌(w̃)` of Lemma 2(i), p. 21: the supremum of the `x ∈ [0, w̃]` such that `V″_w̃ > 0` on
`[0, x)`. -/
noncomputable def wcheck (wt : ℝ) : ℝ :=
  sSup {x | 0 ≤ x ∧ x ≤ wt ∧ ∀ y, 0 ≤ y → y < x → 0 < d2 (P.Vt wt) y}

/-- The concavified function `𝒱_w̃` of Lemma 2(ii), p. 21: the tangent line of `V_w̃` at `w̌(w̃)`
on `[0, w̌(w̃))`, and `V_w̃(w ∧ w̃)` on `[w̌(w̃), ∞)`. -/
noncomputable def calV (wt w : ℝ) : ℝ :=
  if w < P.wcheck wt then
    P.Vt wt (P.wcheck wt) + d1 (P.Vt wt) (P.wcheck wt) * (w - P.wcheck wt)
  else P.Vt wt (min w wt)

/-- `ŵ` of Lemma 3, p. 21 (upright hat; not Definition 1's `ŵ` nor Proposition 6's bold `𝐰̂`):
the infimum of the `w ∈ [0, w̄)` with `𝒱_w(0) = v̲`. Meaningful under Condition 1. -/
noncomputable def what : ℝ :=
  sInf {w | 0 ≤ w ∧ w < P.wbar ∧ P.calV w 0 = P.vlow}

end Params

end SuspensionContract.ControlBand


