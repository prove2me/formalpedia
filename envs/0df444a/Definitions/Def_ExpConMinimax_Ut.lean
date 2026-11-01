-- Prove2me | Definitions.Def_ExpConMinimax_Ut
-- name    : ExpConMinimax_Ut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:52:10.89172+00:00
-- url     : https://prove2.me/theorems/c63e4436-9d78-4bec-9dcb-094144ee2998
-- title:
--   The noise terms $U_t(x,\gamma)$ of (3.8) and $V_t(y,\lambda)$ of (3.10) (corrected: sign of the first term of $V_t$)
-- statement:
--   For a run of Algorithm 1 and a reference point,
--   $$U_t(x,\gamma)=\big(\widetilde\nabla_xL(x_t,y_t,\gamma_{t+1},\omega^1_t,\xi^2_t)-\widetilde\nabla_x\mathcal L(x_t,y_t,\gamma_{t+1})\big)^\top(x-x_t)+\frac{3\|\widetilde\nabla_xL(x_t,y_t,\gamma_{t+1},\omega^1_t,\xi^2_t)\|^2}{2\eta_t}+\big(H(x_t)-h(x_t,\xi^1_t)\big)^\top(\gamma-\gamma_t)+\frac{\|H(x_t)-h(x_t,\xi^1_t)\|^2}{2\beta_t},$$
--   $$V_t(y,\lambda)=\big(\widetilde\nabla_y\mathcal L(x_t,y_t,\lambda_{t+1})-\widetilde\nabla_yL(x_t,y_t,\lambda_{t+1},\omega^2_t,\zeta^2_t)\big)^\top(y-y_t)+\frac{3\|\widetilde\nabla_yL(x_t,y_t,\lambda_{t+1},\omega^2_t,\zeta^2_t)\|^2}{2\kappa_t}+\big(G(y_t)-g(y_t,\zeta^1_t)\big)^\top(\lambda-\lambda_t)+\frac{\|G(y_t)-g(y_t,\zeta^1_t)\|^2}{2\alpha_t}.$$
--
--   They collect the stochastic error of one iteration and appear in Lemmas 3–5.
--
--   **Correction** The paper prints the first term of $V_t$ with the opposite sign, $(\widetilde\nabla_yL-\widetilde\nabla_y\mathcal L)^\top(y-y_t)$. The $y$-block mirrors (B.2) with $(x_t-x)$ replaced by $(y-y_t)$, so the noise term is $(\widetilde\nabla_y\mathcal L-\widetilde\nabla_yL)^\top(y-y_t)$; with the printed sign (3.9) is false (see Lemma 4).
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, (3.8), p.12; (3.10), p.13

import Mathlib
import Definitions.Def_ExpConMinimax_IsRun

namespace ExpConMinimax

variable {dx dy m₁ m₂ : ℕ} {Sω Sξ Sζ : Type*} [MeasurableSpace Sω] [MeasurableSpace Sξ]
  [MeasurableSpace Sζ] {Ω : Type*}

/-- **The noise term `Uₜ(x,γ)`, (3.8)**, p.12.
Yang, Li, Lan, arXiv:2202.07868v2, (3.8):
`Uₜ(x,γ) := (∇̃ₓL(xₜ,yₜ,γₜ₊₁,ω¹ₜ,ξ²ₜ) − ∇̃ₓ𝓛(xₜ,yₜ,γₜ₊₁))ᵀ(x − xₜ)
  + 3‖∇̃ₓL(xₜ,yₜ,γₜ₊₁,ω¹ₜ,ξ²ₜ)‖²/(2ηₜ) + (H(xₜ) − h(xₜ,ξ¹ₜ))ᵀ(γ − γₜ)
  + ‖H(xₜ) − h(xₜ,ξ¹ₜ)‖²/(2βₜ)`.

**Formalization Note.** `Ut P O S η β x y γ t ω u g` is `Uₜ(u, g)` at the outcome `ω`, with the
sample tuple `S t ω` and the step sizes `ηₜ = η t`, `βₜ = β t`. -/
noncomputable def Ut (P : Problem dx dy m₁ m₂) (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ)
    (S : ℕ → Ω → SampleTuple Sω Sξ Sζ) (η β : ℕ → ℝ) (x : ℕ → Ω → Vec dx)
    (y : ℕ → Ω → Vec dy) (γ : ℕ → Ω → Vec m₁) (t : ℕ) (ω : Ω) (u : Vec dx) (g : Vec m₁) : ℝ :=
  inner ℝ (sampledGradLx O (x t ω) (y t ω) (γ (t + 1) ω) (S t ω)
      - meanGradLx O (x t ω) (y t ω) (γ (t + 1) ω)) (u - x t ω)
    + 3 * ‖sampledGradLx O (x t ω) (y t ω) (γ (t + 1) ω) (S t ω)‖ ^ 2 / (2 * η t)
    + inner ℝ (P.H (x t ω) - O.hs (x t ω) (SampleTuple.ξ1 (S t ω))) (g - γ t ω)
    + ‖P.H (x t ω) - O.hs (x t ω) (SampleTuple.ξ1 (S t ω))‖ ^ 2 / (2 * β t)

/-- **The noise term `Vₜ(y,λ)`, (3.10)** (corrected: sign of the first term), p.13.
Yang, Li, Lan, arXiv:2202.07868v2, (3.10):
`Vₜ(y,λ) := (∇̃_yL(xₜ,yₜ,λₜ₊₁,ω²ₜ,ζ²ₜ) − ∇̃_y𝓛(xₜ,yₜ,λₜ₊₁))ᵀ(y − yₜ)
  + 3‖∇̃_yL(xₜ,yₜ,λₜ₊₁,ω²ₜ,ζ²ₜ)‖²/(2κₜ) + (G(yₜ) − g(yₜ,ζ¹ₜ))ᵀ(λ − λₜ)
  + ‖G(yₜ) − g(yₜ,ζ¹ₜ)‖²/(2αₜ)`.

Defined here with the first term `(∇̃_y𝓛(xₜ,yₜ,λₜ₊₁) − ∇̃_yL(xₜ,yₜ,λₜ₊₁,ω²ₜ,ζ²ₜ))ᵀ(y − yₜ)`. The
`y`-block is the mirror of the `x`-block of (B.2) with `(xₜ − x)` replaced by `(y − yₜ)`, so
`Δ_y^{t+1} = ∇̃_yL(…)ᵀ(y − yₜ) + (∇̃_y𝓛(…) − ∇̃_yL(…))ᵀ(y − yₜ)`. **With the printed sign (3.9) is
false**; see `lemma_4`. -/
noncomputable def Vt (P : Problem dx dy m₁ m₂) (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ)
    (S : ℕ → Ω → SampleTuple Sω Sξ Sζ) (κ α : ℕ → ℝ) (x : ℕ → Ω → Vec dx)
    (y : ℕ → Ω → Vec dy) (lam : ℕ → Ω → Vec m₂) (t : ℕ) (ω : Ω) (v : Vec dy) (l : Vec m₂) :
    ℝ :=
  inner ℝ (meanGradLy O (x t ω) (y t ω) (lam (t + 1) ω)
      - sampledGradLy O (x t ω) (y t ω) (lam (t + 1) ω) (S t ω)) (v - y t ω)
    + 3 * ‖sampledGradLy O (x t ω) (y t ω) (lam (t + 1) ω) (S t ω)‖ ^ 2 / (2 * κ t)
    + inner ℝ (P.G (y t ω) - O.gs (y t ω) (SampleTuple.ζ1 (S t ω))) (l - lam t ω)
    + ‖P.G (y t ω) - O.gs (y t ω) (SampleTuple.ζ1 (S t ω))‖ ^ 2 / (2 * α t)

end ExpConMinimax


