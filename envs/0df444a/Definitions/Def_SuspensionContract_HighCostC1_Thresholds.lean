-- Prove2me | Definitions.Def_SuspensionContract_HighCostC1_Thresholds
-- name    : SuspensionContract_HighCostC1_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:59.247997+00:00
-- url     : https://prove2.me/theorems/bf3418d5-2e65-4f40-9d68-8f46b48bc0a8
-- title:
--   Lemma 4, (29), (K1), (30), p. 22 — the tangent pair (θ̄^K, m^K), the bound K̄₁ and the suspension-state value function V_∅
-- statement:
--   This file defines the objects of the high-switching-cost regime under Condition 1 in Cao, Sun and Tian.
--
--   Let $\hat{\mathrm w}$ and $\mathcal V_{\hat{\mathrm w}}$ be as in Lemma 3, $\check w(\hat{\mathrm w})$ the threshold of Lemma 2, and $\mathcal V'$ the derivative within $\mathbb R_+$. For a switching cost $K$, a pair $(\theta,m)$ is a **tangent pair** (Lemma 4, (29)) if $\theta\in[\check w(\hat{\mathrm w}),\hat{\mathrm w}]$, $m\in[0,\mathcal V_{\hat{\mathrm w}}'(0)]$, and
--
--   $$\mathcal V_{\hat{\mathrm w}}(\theta)=m\theta+K+\underline v,\qquad \mathcal V_{\hat{\mathrm w}}'(\theta)=m,$$
--
--   i.e. the line $mw+\underline v$ is tangent to $\mathcal V_{\hat{\mathrm w}}(w)-K$ at $w=\theta$. The paper writes the pair as $(\bar\theta^K,m^K)$.
--
--   The bound (K1) is $\bar K_1=\inf\{K\in(0,\bar V(\hat{\mathrm w})-\underline v]\mid m^K<1\}$, and for a tangent pair $(\theta,m)$ of the model's switching cost $K$ the suspension-state value function (30) is
--
--   $$V_\emptyset(w)=\begin{cases}mw+\underline v, & w\in[0,\theta],\\ \mathcal V_{\hat{\mathrm w}}(w)-K, & w>\theta.\end{cases}$$
--
--   $\bar K_1$ is the switching-cost threshold of the paper's Theorem 2 under Condition 1.
--
--   **Formalization Note** The tangent-pair predicate takes $K$ as an explicit argument, so that (K1) can range over switching costs while the model's own $K$ is fixed; $m^K<1$ is read as "some tangent pair for $K$ has $m<1$" (the pair is unique, as the paper's Lemma 4 proof shows). If that set is empty, Lean's $\inf\emptyset=0$ is a junk value. The paper defines (30) on $[0,\bar\theta^K]\cup[\bar\theta^K,\hat{\mathrm w}]$; the second branch is extended to $[\bar\theta^K,\infty)$ as $\mathcal V_{\hat{\mathrm w}}(w)-K$, which equals $\mathcal V_{\hat{\mathrm w}}(\hat{\mathrm w})-K$ beyond $\hat{\mathrm w}$, exactly as Case 3 of the proof in EC.3.5 (p. ec30) uses it.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 22, Lemma 4 (29), (K1), (30); p. ec30, EC.3.5 Case 3

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_DelayODE

namespace SuspensionContract.HighCostC1

namespace Params

variable (P : Params)

/-- Lemma 4's conclusion (29) for a switching cost `K` passed explicitly (not `P.K`):
`θ ∈ [w̌(ŵ), ŵ]`, `m ∈ [0, 𝒱′_ŵ(0)]`, `𝒱_ŵ(θ) = mθ + K + v̲` and `𝒱′_ŵ(θ) = m`. -/
def TangentPair (K θ m : ℝ) : Prop :=
  θ ∈ Set.Icc (P.wcheck P.what) P.what ∧ m ∈ Set.Icc 0 (d1 (P.calV P.what) 0) ∧
    P.calV P.what θ = m * θ + K + P.vlow ∧ d1 (P.calV P.what) θ = m

/-- The bound `K̄₁ := inf {K ∈ (0, V̄(ŵ) − v̲] | m^K < 1}` of (K1), with `m^K < 1` read as
"some pair `(θ, m)` satisfying (29) for `K` has `m < 1`" (the pair is unique). Junk `sInf ∅ = 0`
if the set is empty. -/
noncomputable def Kbar1 : ℝ :=
  sInf {K : ℝ | 0 < K ∧ K ≤ P.VbarFn P.what - P.vlow ∧ ∃ θ m, P.TangentPair K θ m ∧ m < 1}

/-- `V_∅` of (30) for the pair `(θ̄^K, m^K) = (θ, m)` and the switching cost `P.K`: the line
`mw + v̲` on `[0, θ]` and `𝒱_ŵ(w) − K` for `w > θ` (the second branch extended from `[θ, ŵ]`
to `[θ, ∞)`, as the proof in EC.3.5 uses). -/
noncomputable def V030 (θ m : ℝ) (w : ℝ) : ℝ :=
  if w ≤ θ then m * w + P.vlow else P.calV P.what w - P.K

end Params

end SuspensionContract.HighCostC1


