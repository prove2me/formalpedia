-- Prove2me | Definitions.Def_SuspensionContract_ControlBand_Thresholds
-- name    : SuspensionContract_ControlBand_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:24.090286+00:00
-- url     : https://prove2.me/theorems/44bc7f7a-0c35-4bf0-83bc-78d7b4eeb497
-- title:
--   Lemma 4, (K1), p. 22; Condition 3, Proposition 6, p. 26; (46), p. 27 — K̄₁, Condition 3, Proposition 6's conclusions and the control-band value functions (46)
-- statement:
--   For a switching cost $K$, a pair $(\theta,m)$ is a **tangent pair** (Lemma 4, (29)) if $\theta\in[\check w(\hat{\mathrm w}),\hat{\mathrm w}]$, $m\in[0,\mathcal V_{\hat{\mathrm w}}'(0)]$, $\mathcal V_{\hat{\mathrm w}}(\theta)=m\theta+K+\underline v$ and $\mathcal V_{\hat{\mathrm w}}'(\theta)=m$. The bound (K1) is
--   $$\bar K_1=\inf\{K\in(0,\bar V(\hat{\mathrm w})-\underline v]: m^K<1\}.$$
--   **Condition 3** holds if either Condition 1 and $K<\bar K_1$, or Condition 2 and $K<\underline K$.
--
--   For parameters $(\mathsf c,\hat{\mathbf w},\bar\vartheta,\underline\vartheta)$ the control-band value functions (46) are
--   $$V_I(w)=\begin{cases}V_{\mathsf c}(w),&w\in[0,\underline\vartheta),\\ \mathcal V_{\hat{\mathbf w}}(w),&w\ge\underline\vartheta,\end{cases}\qquad V_\emptyset(w)=\begin{cases}V_{\mathsf c}(w),&w\in[0,\bar\vartheta),\\ \mathcal V_{\hat{\mathbf w}}(w)-K,&w\ge\bar\vartheta.\end{cases}$$
--   The predicate "Proposition 6's conclusions hold for $(\mathsf c,\hat{\mathbf w},\bar\vartheta,\underline\vartheta)$" means: $\mathsf c>0$, $0<\underline\vartheta<\bar\vartheta<\hat{\mathbf w}$, $\hat{\mathbf w}<\hat{\mathrm w}$ under Condition 1 and $\hat{\mathbf w}<\bar w$ under Condition 2,
--   $$\mathcal V_{\hat{\mathbf w}}(\underline\vartheta)=V_{\mathsf c}(\underline\vartheta),\quad \mathcal V_{\hat{\mathbf w}}'(\underline\vartheta)=V_{\mathsf c}'(\underline\vartheta),\quad \mathcal V_{\hat{\mathbf w}}(\bar\vartheta)=V_{\mathsf c}(\bar\vartheta)+K,\quad \mathcal V_{\hat{\mathbf w}}'(\bar\vartheta)=V_{\mathsf c}'(\bar\vartheta)>1\quad(42)\text{–}(45),$$
--   and $\bar\vartheta>\check w(\hat{\mathbf w})$.
--
--   These objects describe the optimal value functions in the low-switching-cost region (Area III of the paper's Figure 2).
--
--   **Formalization Note.** `TangentPair` takes $K$ explicitly, so $\bar K_1$ does not depend on the model's own $K$; if its defining set were empty, Lean's `sInf ∅ = 0` would apply (the set contains $\bar V(\hat{\mathrm w})-\underline v$ with $(\theta,m)=(\hat{\mathrm w},0)$). Proposition 6 prints $\hat{\mathbf w}<\hat{\mathrm w}$ for both branches of Condition 3, but $\hat{\mathrm w}$ does not exist under Condition 2 and the proof there concludes $\hat{\mathbf w}<\bar w$; the predicate uses the branch-wise reading. $0<\underline\vartheta$ is added (the proof gives $\underline\vartheta\in(0,\underline\theta^0)$, and $V_{\mathsf c}'(0)$ is infinite). $V_{\mathsf c}'$ is the ordinary derivative at the positive points $\underline\vartheta,\bar\vartheta$; $\mathcal V'$ is the derivative within $\mathbb R_+$.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 22, Lemma 4, (29), (K1); p. 26, Condition 3, Proposition 6, (42)–(45); p. 27, (46)

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_DelayODE

namespace SuspensionContract.ControlBand

namespace Params

variable (P : Params)

/-- Lemma 4's pair as a predicate, (29), p. 22, for an explicit switching cost `K` (not `P.K`):
`θ ∈ [w̌(ŵ), ŵ]`, `m ∈ [0, 𝒱′_ŵ(0)]`, `𝒱_ŵ(θ) = mθ + K + v̲` and `𝒱′_ŵ(θ) = m`. -/
def TangentPair (K θ m : ℝ) : Prop :=
  θ ∈ Set.Icc (P.wcheck P.what) P.what ∧ m ∈ Set.Icc 0 (d1 (P.calV P.what) 0) ∧
    P.calV P.what θ = m * θ + K + P.vlow ∧ d1 (P.calV P.what) θ = m

/-- `K̄₁ := inf {K ∈ (0, V̄(ŵ) − v̲] | m^K < 1}` (K1), p. 22. It does not depend on `P.K`. -/
noncomputable def Kbar1 : ℝ :=
  sInf {K | 0 < K ∧ K ≤ P.VbarFn P.what - P.vlow ∧ ∃ θ m, P.TangentPair K θ m ∧ m < 1}

/-- Condition 3, p. 26: Condition 1 and `K < K̄₁`, or Condition 2 and `K < K̲`. -/
def Condition3 : Prop :=
  (P.Condition1 ∧ P.K < P.Kbar1) ∨ (P.Condition2 ∧ P.K < P.Klow)

/-- `V_I` of (46), p. 27, for parameters `(𝖼, 𝐰̂, ϑ̲)`: `V_𝖼(w)` on `[0, ϑ̲)`, `𝒱_𝐰̂(w)` for `w ≥ ϑ̲`. -/
noncomputable def VI46 (c wB thLo w : ℝ) : ℝ :=
  if w < thLo then P.Vc c w else P.calV wB w

/-- `V_∅` of (46), p. 27, for parameters `(𝖼, 𝐰̂, ϑ̄)`: `V_𝖼(w)` on `[0, ϑ̄)`, `𝒱_𝐰̂(w) − K` for
`w ≥ ϑ̄`. -/
noncomputable def V046 (c wB thHi w : ℝ) : ℝ :=
  if w < thHi then P.Vc c w else P.calV wB w - P.K

/-- The conclusions of Proposition 6, p. 26, for a tuple `(𝖼, 𝐰̂, ϑ̄, ϑ̲)`: `𝖼 > 0`,
`0 < ϑ̲ < ϑ̄ < 𝐰̂`, `𝐰̂ < ŵ` under Condition 1 and `𝐰̂ < w̄` under Condition 2 (printed slip:
Lemma 3's `ŵ` does not exist under Condition 2), (42)–(45), and `ϑ̄ > w̌(𝐰̂)`. `0 < ϑ̲` is a
disclosed addition (the proof gives `ϑ̲ ∈ (0, θ̲⁰)`; `V′_𝖼(0)` is infinite). -/
def Prop6Params (c wB thHi thLo : ℝ) : Prop :=
  0 < c ∧ 0 < thLo ∧ thLo < thHi ∧ thHi < wB ∧
    (P.Condition1 → wB < P.what) ∧ (P.Condition2 → wB < P.wbar) ∧
    P.calV wB thLo = P.Vc c thLo ∧
    d1 (P.calV wB) thLo = deriv (P.Vc c) thLo ∧
    P.calV wB thHi = P.Vc c thHi + P.K ∧
    d1 (P.calV wB) thHi = deriv (P.Vc c) thHi ∧ 1 < deriv (P.Vc c) thHi ∧
    P.wcheck wB < thHi

end Params

end SuspensionContract.ControlBand


