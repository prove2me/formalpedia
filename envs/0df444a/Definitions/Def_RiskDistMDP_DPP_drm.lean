-- Prove2me | Definitions.Def_RiskDistMDP_DPP_drm
-- name    : RiskDistMDP_DPP_drm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:41.508926+00:00
-- url     : https://prove2.me/theorems/432dbb9f-ab44-4680-a0f4-41ffc3353cec
-- title:
--   Finite-horizon dynamic risk measure $\varsigma^{\mathfrak X,\gamma}_{t,x,T}$ (2.9)
-- statement:
--   Let $\gamma\in[0,1]$, $\mathfrak X=(X_t)$ an $\mathbb F$-adapted state process and $\mathfrak Z=(Z_t)_{t\in\mathbb N_0}$ bounded random variables. For $T\in\mathbb N$ the **finite-horizon DRM** is defined backwards by
--   $$\varsigma^{\mathfrak X,\gamma}_{t,x,T}(\mathfrak Z):=\begin{cases}\sigma_{t,x}\big(P^{W^T_t|\mathcal U_t}\big),&0<t<T,\\ \sigma_{T,x}\big(P^{Z_T|\mathcal U_T}\big),&t=T,\end{cases}\qquad W^T_t=Z_t+\gamma\,\varsigma^{\mathfrak X,\gamma}_{t+1,X_{t+1},T}(\mathfrak Z),$$
--   and at time $0$
--   $$\varsigma^{\mathfrak X,\gamma}_{0,T}(\mathfrak Z):=\sigma_0\Big(\mathcal L\big(Z_0+\gamma\,\varsigma^{\mathfrak X}_{1,X_1,T}(\mathfrak Z)\big)\Big).$$
--   Each step applies a state-dependent risk measure to the conditional law of the cost-to-go given the decision information; for a Markov pair it reduces to a composition of one-step operators (Lemma 3.3).
--
--   The module defines `drm` ($t\ge1$), the variable $W^T_t$ (`drmW`) and `drm0`.
--
--   **Formalization Note** $\sigma_{t,x}$ is applied to the conditional distribution when that lies in $\mathcal P_b(\mathbb R)$ and the value is $0$ otherwise; this changes the DRM only on a null set and makes its joint measurability (Lemma 2.7) hold for every version. $W^T_t$ uses the real value of $\varsigma_{t+1,X_{t+1},T}$, which is finite a.s. (Lemma 2.7). For $t>T$ the value is $0$ and unused; $\sigma_0$ is applied as is and its value may be $+\infty$.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (2.9), p. 9

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_IsDistRiskMeasure
import Definitions.Def_RiskDistMDP_DPP_rcd

set_option autoImplicit false

open MeasureTheory Set

namespace RiskDistMDP.DPP

open Classical in
/-- `σ` applied only inside its domain `𝒫_b(ℝ)`: `guardσ σ μ = σ μ` if `μ ∈ 𝒫_b(ℝ)` and `0`
otherwise. Used in the DRM (2.9), where the regular conditional distributions of bounded random
variables lie in `𝒫_b(ℝ)` for `ℙ`-a.e. `ω`. -/
noncomputable def guardσ (σ : Measure ℝ → EReal) (μ : Measure ℝ) : EReal :=
  if InPb μ then σ μ else 0

/-- The **finite-horizon DRM** `ς^{𝔛,γ}_{t,x,T}(ℨ)` of arXiv:2203.09612v4, (2.9), p.9:
for `0 < t < T`, `ς_{t,x,T}(ℨ) := σ_{t,x}(P^{W^T_t | 𝒰_t})` with
`W^T_t = Z_t + γ ς_{t+1, X_{t+1}, T}(ℨ)`, and `ς_{T,x,T}(ℨ) := σ_{T,x}(P^{Z_T | 𝒰_T})`.

`drm σ γ Pr 𝒰 𝔛 Z T t x ω` is the value at `(x, ω)`; `𝒰 t` is the decision information and
`𝔛 = (X_t)` the state process.

**Formalization Note**
* The recursion runs downward from `t = T`; for `t > T` the value is `0` and is never used.
* `σ_{t,x}` is applied through `guardσ`: to the regular conditional distribution when it lies in
  `𝒫_b(ℝ)`, and `0` otherwise. For `ℨ ⊂ L^∞` the conditional distributions are in `𝒫_b(ℝ)` for
  `ℙ`-a.e. `ω` (Lemma 2.7), so this changes the DRM only on a `ℙ`-null set, and it makes the joint
  measurability of Lemma 2.7 hold for every version.
* `W^T_t` uses the real number `(ς_{t+1,X_{t+1},T}(ℨ)).toReal`; Lemma 2.7 (`lemma_2_7`) states
  that these values are finite a.s. -/
noncomputable def drm {Ω 𝕏 : Type*} [mΩ : MeasurableSpace Ω] (σ : ℕ → 𝕏 → Measure ℝ → EReal)
    (γ : ℝ) (Pr : Measure Ω) [IsFiniteMeasure Pr] (𝒰 : ℕ → MeasurableSpace Ω) (𝔛 : ℕ → Ω → 𝕏)
    (Z : ℕ → Ω → ℝ) (T t : ℕ) : 𝕏 → Ω → EReal :=
  if _h : t < T then
    fun x ω => guardσ (σ t x)
      (rcd Pr (𝒰 t) (fun ω' => Z t ω' + γ * (drm σ γ Pr 𝒰 𝔛 Z T (t + 1) (𝔛 (t + 1) ω') ω').toReal) ω)
  else if t = T then
    fun x ω => guardσ (σ T x) (rcd Pr (𝒰 T) (Z T) ω)
  else
    fun _ _ => 0
termination_by T - t
decreasing_by omega

/-- The random variable `W^T_t = Z_t + γ ς^{𝔛,γ}_{t+1,X_{t+1},T}(ℨ)` of arXiv:2203.09612v4, p.9
(for `0 < t < T`), whose regular conditional distribution given `𝒰_t` defines `ς_{t,x,T}`. -/
noncomputable def drmW {Ω 𝕏 : Type*} [mΩ : MeasurableSpace Ω] (σ : ℕ → 𝕏 → Measure ℝ → EReal)
    (γ : ℝ) (Pr : Measure Ω) [IsFiniteMeasure Pr] (𝒰 : ℕ → MeasurableSpace Ω) (𝔛 : ℕ → Ω → 𝕏)
    (Z : ℕ → Ω → ℝ) (T t : ℕ) (ω : Ω) : ℝ :=
  Z t ω + γ * (drm σ γ Pr 𝒰 𝔛 Z T (t + 1) (𝔛 (t + 1) ω) ω).toReal

/-- The DRM at time `0`, `ς^{𝔛,γ}_{0,T}(ℨ) := σ₀(ℒ(Z₀ + γ ς^𝔛_{1,X₁,T}(ℨ)))`
(arXiv:2203.09612v4, p.9), for `T ∈ ℕ`.

**Formalization Note** `ℒ(·)` is the push-forward of `Pr`. `σ₀` is applied directly (it may take
the value `+∞`, so the result is kept in `EReal`). -/
noncomputable def drm0 {Ω 𝕏 : Type*} [mΩ : MeasurableSpace Ω] (σ0 : Measure ℝ → EReal)
    (σ : ℕ → 𝕏 → Measure ℝ → EReal) (γ : ℝ) (Pr : Measure Ω) [IsFiniteMeasure Pr]
    (𝒰 : ℕ → MeasurableSpace Ω) (𝔛 : ℕ → Ω → 𝕏) (Z : ℕ → Ω → ℝ) (T : ℕ) : EReal :=
  σ0 (Pr.map fun ω => Z 0 ω + γ * (drm σ γ Pr 𝒰 𝔛 Z T 1 (𝔛 1 ω) ω).toReal)

end RiskDistMDP.DPP


