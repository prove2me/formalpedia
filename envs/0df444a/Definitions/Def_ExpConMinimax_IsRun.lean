-- Prove2me | Definitions.Def_ExpConMinimax_IsRun
-- name    : ExpConMinimax_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:27.955818+00:00
-- url     : https://prove2.me/theorems/e3ccd9a1-2867-47c0-adeb-e70a3ab59dbd
-- title:
--   Algorithm 1 (Basic-CSPD): a run, the sampled and mean Lagrangian gradients (3.3)–(3.4), and the output averages
-- statement:
--   Given positive step sizes $\{\alpha_t\},\{\beta_t\},\{\kappa_t\},\{\eta_t\}$, an initial point $(x_0,y_0,\gamma_0,\lambda_0)\in\mathcal X\times\mathcal Y\times\mathbb R^{m_1}_+\times\mathbb R^{m_2}_+$ and the samples of iteration $t$, **Algorithm 1** sets
--   $$\gamma_{t+1}=\operatorname*{argmax}_{\gamma\in\mathbb R^{m_1}_+}\Big\{h(x_t,\xi^1_t)^\top\gamma-\tfrac{\beta_t}{2}\|\gamma_t-\gamma\|^2\Big\},\qquad \lambda_{t+1}=\operatorname*{argmin}_{\lambda\in\mathbb R^{m_2}_+}\Big\{-g(y_t,\zeta^1_t)^\top\lambda+\tfrac{\alpha_t}{2}\|\lambda_t-\lambda\|^2\Big\},$$
--   $$x_{t+1}=\operatorname*{argmin}_{x\in\mathcal X}\Big\{\widetilde\nabla_xL(x_t,y_t,\gamma_{t+1},\omega^1_t,\xi^2_t)^\top x+\tfrac{\eta_t}{2}\|x-x_t\|^2\Big\},\qquad y_{t+1}=\operatorname*{argmax}_{y\in\mathcal Y}\Big\{\widetilde\nabla_yL(x_t,y_t,\lambda_{t+1},\omega^2_t,\zeta^2_t)^\top y-\tfrac{\kappa_t}{2}\|y-y_t\|^2\Big\},$$
--   with the sampled gradients (3.4) $\widetilde\nabla_xL(x,y,\gamma,\omega,\xi)=\widetilde\nabla_xf(x,y,\omega)+\sum_i\gamma_i\widetilde\nabla h_i(x,\xi)$ and $\widetilde\nabla_yL(x,y,\lambda,\omega,\zeta)=\widetilde\nabla_yf(x,y,\omega)-\sum_j\lambda_j\widetilde\nabla g_j(y,\zeta)$. The mean gradients (3.3) are $\widetilde\nabla_x\mathcal L(x,y,\gamma)=\widetilde\nabla_xF(x,y)+\sum_i\gamma_i\widetilde\nabla H_i(x)$ and $\widetilde\nabla_y\mathcal L(x,y,\lambda)=\widetilde\nabla_yF(x,y)-\sum_j\lambda_j\widetilde\nabla G_j(y)$. The output is $\bar x_N=\frac1N\sum_{t=1}^Nx_t$, $\bar y_N=\frac1N\sum_{t=1}^Ny_t$.
--
--   A **run** is a family of random sequences $(x_t,y_t,\gamma_t,\lambda_t)_{t\ge0}$ satisfying these updates at every outcome.
--
--   **Formalization Note** Each argmin/argmax is encoded by its characterization (the iterate is feasible and at least as good as every feasible competitor); the objectives are strongly convex/concave, so the iterate is unique. The sequences are defined for every $t\ge0$.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Algorithm 1, p.11; (3.1)–(3.2), p.10; (3.3)–(3.4), p.11; output averages, p.15

import Mathlib
import Definitions.Def_ExpConMinimax_Problem
import Definitions.Def_ExpConMinimax_Oracle

namespace ExpConMinimax

variable {dx dy m₁ m₂ : ℕ} {Sω Sξ Sζ : Type*} [MeasurableSpace Sω] [MeasurableSpace Sξ]
  [MeasurableSpace Sζ]

/-- **Sampled partial gradient of the Lagrangian in `x`**, (3.4), p.11:
`∇̃ₓL(x,y,γ,ω,ξ) := ∇̃ₓf(x,y,ω) + ∑ᵢ γᵢ ∇̃hᵢ(x,ξ)`, evaluated at the samples `ω¹ₜ`, `ξ²ₜ` of a
sample tuple (the samples Algorithm 1 uses in its `x`-update). -/
def sampledGradLx (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (x : Vec dx) (y : Vec dy) (γ : Vec m₁)
    (s : SampleTuple Sω Sξ Sζ) : Vec dx :=
  O.gfx x y (SampleTuple.ω1 s) + O.ghs x (SampleTuple.ξ2 s) γ

/-- **Sampled partial gradient of the Lagrangian in `y`**, (3.4), p.11:
`∇̃_yL(x,y,λ,ω,ζ) := ∇̃_yf(x,y,ω) − ∑ⱼ λⱼ ∇̃gⱼ(y,ζ)`, evaluated at the samples `ω²ₜ`, `ζ²ₜ`. -/
def sampledGradLy (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (x : Vec dx) (y : Vec dy) (lam : Vec m₂)
    (s : SampleTuple Sω Sξ Sζ) : Vec dy :=
  O.gfy x y (SampleTuple.ω2 s) - O.ggs y (SampleTuple.ζ2 s) lam

/-- **Partial (sub)gradient of the Lagrangian in `x`**, (3.3), p.11:
`∇̃ₓ𝓛(x,y,γ) = ∇̃ₓF(x,y) + ∑ᵢ γᵢ ∇̃Hᵢ(x)`, with the oracle means of Assumptions 2.1–2.2. -/
noncomputable def meanGradLx (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (x : Vec dx) (y : Vec dy)
    (γ : Vec m₁) : Vec dx :=
  O.meanGfx x y + O.meanGhs x γ

/-- **Partial (super)gradient of the Lagrangian in `y`**, (3.3), p.11:
`∇̃_y𝓛(x,y,λ) = ∇̃_yF(x,y) − ∑ⱼ λⱼ ∇̃Gⱼ(y)`. -/
noncomputable def meanGradLy (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (x : Vec dx) (y : Vec dy)
    (lam : Vec m₂) : Vec dy :=
  O.meanGfy x y - O.meanGgs y lam

/-- **A run of Algorithm 1 (Basic-CSPD).**
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Algorithm 1, p.11 (equivalently (3.1)–(3.2), p.10):

"Input: Positive step-sizes `{αₜ}, {βₜ}, {κₜ}, {ηₜ}`, and initial points
`(x₀,y₀,γ₀,λ₀) ∈ X × Y × ℝ^{m₁}_+ × ℝ^{m₂}_+`. for `t = 0,1,2,…,N−1` do
  `γₜ₊₁ = argmax_{γ∈ℝ^{m₁}_+} { h(xₜ,ξ¹ₜ)ᵀγ − βₜ/2 ‖γₜ − γ‖² }`,
  `λₜ₊₁ = argmin_{λ∈ℝ^{m₂}_+} { −g(yₜ,ζ¹ₜ)ᵀλ + αₜ/2 ‖λₜ − λ‖² }`,
  `xₜ₊₁ = argmin_{x∈X} { (∇̃ₓf(xₜ,yₜ,ω¹ₜ) + ∑ᵢ γₜ₊₁,ᵢ ∇̃hᵢ(xₜ,ξ²ₜ))ᵀx + ηₜ/2 ‖x − xₜ‖² }`,
  `yₜ₊₁ = argmax_{y∈Y} { (∇̃_yf(xₜ,yₜ,ω²ₜ) − ∑ⱼ λₜ₊₁,ⱼ ∇̃gⱼ(yₜ,ζ²ₜ))ᵀy − κₜ/2 ‖y − yₜ‖² }`.
end for."

`IsRun P O S η κ α β x₀ y₀ γ₀ λ₀ x y γ λ` says that the random sequences `x, y, γ, λ`
(indexed by the iteration `t` and the outcome `ω ∈ Ω`) are produced by Algorithm 1 from the
sample tuples `S t ω = (ω¹ₜ, ω²ₜ, ξ¹ₜ, ξ²ₜ, ζ¹ₜ, ζ²ₜ)`, the step sizes `η, κ, α, β` and the initial
point.

**Formalization Note.** Each `argmin`/`argmax` is encoded by its characterization: the new
iterate lies in the feasible set and its objective value is at least as good as that of every
competitor in the set. Each objective is strongly convex (resp. concave), so the iterate is
unique and the run is determined by the samples. The sequences are defined for every
`t ∈ ℕ`; statements about a horizon `N` only read `t ≤ N`. The dual updates use `ξ¹ₜ`, `ζ¹ₜ`;
the primal updates are both taken at `(xₜ, yₜ)` and use `γₜ₊₁`, `λₜ₊₁` (Jacobi in `x, y`). -/
def IsRun (P : Problem dx dy m₁ m₂) (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) {Ω : Type*}
    (S : ℕ → Ω → SampleTuple Sω Sξ Sζ) (η κ α β : ℕ → ℝ)
    (x₀ : Vec dx) (y₀ : Vec dy) (γ₀ : Vec m₁) (lam₀ : Vec m₂)
    (x : ℕ → Ω → Vec dx) (y : ℕ → Ω → Vec dy) (γ : ℕ → Ω → Vec m₁)
    (lam : ℕ → Ω → Vec m₂) : Prop :=
  (∀ t, 0 < η t ∧ 0 < κ t ∧ 0 < α t ∧ 0 < β t) ∧
  x₀ ∈ P.X ∧ y₀ ∈ P.Y ∧ IsNonneg γ₀ ∧ IsNonneg lam₀ ∧
  (∀ ω, x 0 ω = x₀ ∧ y 0 ω = y₀ ∧ γ 0 ω = γ₀ ∧ lam 0 ω = lam₀) ∧
  ∀ t ω,
    -- `γₜ₊₁ = argmax_{γ ≥ 0} { h(xₜ,ξ¹ₜ)ᵀγ − βₜ/2 ‖γₜ − γ‖² }`
    (IsNonneg (γ (t + 1) ω) ∧ ∀ g : Vec m₁, IsNonneg g →
      inner ℝ (O.hs (x t ω) (SampleTuple.ξ1 (S t ω))) g - β t / 2 * ‖γ t ω - g‖ ^ 2 ≤
        inner ℝ (O.hs (x t ω) (SampleTuple.ξ1 (S t ω))) (γ (t + 1) ω)
          - β t / 2 * ‖γ t ω - γ (t + 1) ω‖ ^ 2) ∧
    -- `λₜ₊₁ = argmin_{λ ≥ 0} { −g(yₜ,ζ¹ₜ)ᵀλ + αₜ/2 ‖λₜ − λ‖² }`
    (IsNonneg (lam (t + 1) ω) ∧ ∀ l : Vec m₂, IsNonneg l →
      -inner ℝ (O.gs (y t ω) (SampleTuple.ζ1 (S t ω))) (lam (t + 1) ω)
          + α t / 2 * ‖lam t ω - lam (t + 1) ω‖ ^ 2 ≤
        -inner ℝ (O.gs (y t ω) (SampleTuple.ζ1 (S t ω))) l + α t / 2 * ‖lam t ω - l‖ ^ 2) ∧
    -- `xₜ₊₁ = argmin_{x ∈ X} { ∇̃ₓL(xₜ,yₜ,γₜ₊₁,ω¹ₜ,ξ²ₜ)ᵀx + ηₜ/2 ‖x − xₜ‖² }`
    (x (t + 1) ω ∈ P.X ∧ ∀ u ∈ P.X,
      inner ℝ (sampledGradLx O (x t ω) (y t ω) (γ (t + 1) ω) (S t ω)) (x (t + 1) ω)
          + η t / 2 * ‖x (t + 1) ω - x t ω‖ ^ 2 ≤
        inner ℝ (sampledGradLx O (x t ω) (y t ω) (γ (t + 1) ω) (S t ω)) u
          + η t / 2 * ‖u - x t ω‖ ^ 2) ∧
    -- `yₜ₊₁ = argmax_{y ∈ Y} { ∇̃_yL(xₜ,yₜ,λₜ₊₁,ω²ₜ,ζ²ₜ)ᵀy − κₜ/2 ‖y − yₜ‖² }`
    (y (t + 1) ω ∈ P.Y ∧ ∀ v ∈ P.Y,
      inner ℝ (sampledGradLy O (x t ω) (y t ω) (lam (t + 1) ω) (S t ω)) v
          - κ t / 2 * ‖v - y t ω‖ ^ 2 ≤
        inner ℝ (sampledGradLy O (x t ω) (y t ω) (lam (t + 1) ω) (S t ω)) (y (t + 1) ω)
          - κ t / 2 * ‖y (t + 1) ω - y t ω‖ ^ 2)

/-- **The output average** `x̄_N = (1/N) ∑_{t=1}^N xₜ` (Algorithm 1, Output, p.11; §3.1.2, p.15).
Note the index range `t = 1, …, N`. -/
noncomputable def avg {E : Type*} [AddCommGroup E] [Module ℝ E] {Ω : Type*} (N : ℕ)
    (x : ℕ → Ω → E) (ω : Ω) : E :=
  (N : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 N, x t ω

end ExpConMinimax


