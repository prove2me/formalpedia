-- Prove2me | Definitions.Def_OnlineWass_igd
-- name    : OnlineWass_igd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:52.814255+00:00
-- url     : https://prove2.me/theorems/d83f92ba-f2d1-4435-b432-94dbe46ee56b
-- title:
--   The run of IGD($\gamma$), Algorithm 1
-- statement:
--   Given an input $\gamma=(\gamma_1,\dots,\gamma_T)$, a budget $c$ and a problem profile $\mathcal H=(\theta_1,\dots,\theta_T)$, Algorithm 1 starts from $p_1=0$, $c_1=c$, and in each period $t=1,\dots,T$:
--
--   1. observes $\theta_t$ and solves $\tilde x_t\in\operatorname{argmax}_{x\in\mathcal X}\{f(x;\theta_t)-p_t^\top g(x;\theta_t)\}$;
--   2. sets $x_t=\tilde x_t$ if $c_t$ permits a consumption of $g(\tilde x_t;\theta_t)$, and $x_t=0$ otherwise;
--   3. updates the price, $p_{t+1}=\bigl(p_t+\tfrac1{\sqrt T}(g(\tilde x_t;\theta_t)-\gamma_t)\bigr)\vee0$;
--   4. updates the capacity, $c_{t+1}=c_t-g(x_t;\theta_t)$.
--
--   The price update uses the virtual action $\tilde x_t$ even in a period where the true action is $0$. A **tie-break rule** `sel` is a jointly measurable map with `sel p θ` a maximizer in step 1 for all $p\ge0$ and $\theta$. The online reward is $R_T(\pi)=\sum_t f(x_t;\theta_t)$. Also defined are the virtual reward $\sum_t f(\tilde x_t;\theta_t)$ and the overshoot $\sum_{i}[\sum_t g_i(\tilde x_t;\theta_t)-(c_i-1)]^+$.
--
--   With input $\hat\gamma$ of a fluid plan this is IGD($\hat\gamma$), and the step is display (11).
--
--   **Formalization Note** The prices and capacities are defined by recursion on a natural number, reading the profile at index $t$ only. Thus $(p_t,c_t)$ is a function of $\theta_1,\dots,\theta_{t-1}$ by construction. Index $0$ is $p_1$, index $T$ is $p_{T+1}$, and values past $T$ are frozen. "Permits" is coordinatewise: $g_i(\tilde x_t;\theta_t)\le c_{t,i}$ for every $i$. $\sqrt T$ is that of the fixed horizon.
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Algorithm 1, (7), p.17; (11), p.21; R_T(π), p.11; virtual reward and overshoot, p.48

import Mathlib
import Definitions.Def_OnlineWass_Model

namespace OnlineWass

variable {k m : ℕ} {Θ : Type*}

/-- **The tie-break rule of Algorithm 1 line 4, p.17.** A jointly measurable `sel` such that for every
`p ≥ 0` and `θ`, `sel p θ` is a maximizer of `f(x; θ) − pᵀg(x; θ)` over `𝒳`; the virtual action is
`x̃ₜ = sel pₜ θₜ`.

**Formalization Note.** Line 4 writes "solve x̃ₜ = argmax", which is a set under ties; `sel` is the
solver. It is arbitrary, and `OnlineWass.exists_tieBreak` shows one exists. Values at `p ≱ 0` are never
used, as the prices of a run are nonnegative. -/
structure IsTieBreak [MeasurableSpace Θ] (M : Model k m Θ)
    (sel : (Fin m → ℝ) → Θ → Fin k → ℝ) : Prop where
  measurable : Measurable (Function.uncurry sel)
  mem : ∀ p, 0 ≤ p → ∀ θ, sel p θ ∈ M.X
  isMaxOn : ∀ p, 0 ≤ p → ∀ θ, IsMaxOn (fun x => M.lagrangian p x θ) M.X (sel p θ)

variable {T : ℕ}

/-- **The dual prices of IGD(γ), Algorithm 1, p.17: line 2 and (7) (with `γ = γ̂`, (11), p.21).**
`price … t` is `p_{t+1}` of the paper: `p₁ = 0` is index `0` and `p_{T+1}` is index `T`. The update is
`p_{t+1} = (pₜ + (1/√T)(g(x̃ₜ; θₜ) − γₜ)) ∨ 0`, with the virtual action `x̃ₜ = sel pₜ θₜ`, not the true
action.

**Formalization Note.** The recursion reads `H` at index `t` only, so `pₜ` depends on `θ₁, …, θₜ₋₁`
alone, and the policy never sees the true law, the prior, or `W_T` beyond the input `γ`. `√T` is that
of the fixed horizon. The value is frozen past index `T`. -/
noncomputable def price (M : Model k m Θ) (sel : (Fin m → ℝ) → Θ → Fin k → ℝ)
    (γ : Fin T → Fin m → ℝ) (H : Fin T → Θ) : ℕ → Fin m → ℝ
  | 0 => 0
  | t + 1 =>
    if ht : t < T then
      fun i => max (price M sel γ H t i +
        (1 / √(T : ℝ)) * (M.g (sel (price M sel γ H t) (H ⟨t, ht⟩)) (H ⟨t, ht⟩) i - γ ⟨t, ht⟩ i)) 0
    else price M sel γ H t

/-- **The virtual action `x̃ₜ`**, Algorithm 1 line 4, p.17. Index `t : Fin T` is period `t + 1`. -/
noncomputable def virtualAction (M : Model k m Θ) (sel : (Fin m → ℝ) → Θ → Fin k → ℝ)
    (γ : Fin T → Fin m → ℝ) (H : Fin T → Θ) (t : Fin T) : Fin k → ℝ :=
  sel (price M sel γ H t) (H t)

open scoped Classical in
/-- **Algorithm 1 line 5, p.17:** `x̃` if the remaining capacity `b` permits a consumption of
`g(x̃; θ)`, that is `gᵢ(x̃; θ) ≤ bᵢ` for every `i`, and `0` otherwise. -/
noncomputable def admit (M : Model k m Θ) (b : Fin m → ℝ) (xt : Fin k → ℝ) (θ : Θ) : Fin k → ℝ :=
  if ∀ i, M.g xt θ i ≤ b i then xt else 0

/-- **The remaining capacity, Algorithm 1 lines 2 and 7, p.17:** `c₁ = c`, `c_{t+1} = cₜ − g(xₜ; θₜ)`.
`budget … t` is `c_{t+1}` of the paper, and the value is frozen past index `T`. -/
noncomputable def budget (M : Model k m Θ) (sel : (Fin m → ℝ) → Θ → Fin k → ℝ)
    (γ : Fin T → Fin m → ℝ) (c : Fin m → ℝ) (H : Fin T → Θ) : ℕ → Fin m → ℝ
  | 0 => c
  | t + 1 =>
    if ht : t < T then
      fun i => budget M sel γ c H t i -
        M.g (admit M (budget M sel γ c H t) (virtualAction M sel γ H ⟨t, ht⟩) (H ⟨t, ht⟩))
          (H ⟨t, ht⟩) i
    else budget M sel γ c H t

/-- **The true action `xₜ`**, Algorithm 1 line 5, p.17. -/
noncomputable def action (M : Model k m Θ) (sel : (Fin m → ℝ) → Θ → Fin k → ℝ)
    (γ : Fin T → Fin m → ℝ) (c : Fin m → ℝ) (H : Fin T → Θ) (t : Fin T) : Fin k → ℝ :=
  admit M (budget M sel γ c H t) (virtualAction M sel γ H t) (H t)

/-- **`R_T(π)`, p.11:** `Σ_{t=1}^T f(xₜ; θₜ)` for the run of IGD(γ). -/
noncomputable def onlineReward (M : Model k m Θ) (sel : (Fin m → ℝ) → Θ → Fin k → ℝ)
    (γ : Fin T → Fin m → ℝ) (c : Fin m → ℝ) (H : Fin T → Θ) : ℝ :=
  ∑ t, M.f (action M sel γ c H t) (H t)

/-- The reward of the virtual actions, `Σ_{t=1}^T f(x̃ₜ; θₜ)` (p.48). -/
noncomputable def virtualReward (M : Model k m Θ) (sel : (Fin m → ℝ) → Θ → Fin k → ℝ)
    (γ : Fin T → Fin m → ℝ) (H : Fin T → Θ) : ℝ :=
  ∑ t, M.f (virtualAction M sel γ H t) (H t)

/-- The budget overshoot of p.48, `Σ_{i=1}^m [Σ_{t=1}^T gᵢ(x̃ₜ; θₜ) − (cᵢ − 1)]⁺`. -/
noncomputable def overshoot (M : Model k m Θ) (sel : (Fin m → ℝ) → Θ → Fin k → ℝ)
    (γ : Fin T → Fin m → ℝ) (c : Fin m → ℝ) (H : Fin T → Θ) : ℝ :=
  ∑ i, max (∑ t, M.g (virtualAction M sel γ H t) (H t) i - (c i - 1)) 0

end OnlineWass


