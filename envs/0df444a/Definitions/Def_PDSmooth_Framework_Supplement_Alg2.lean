-- Prove2me | Definitions.Def_PDSmooth_Framework_Supplement_Alg2
-- name    : PDSmooth_Framework_Supplement_Alg2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:51:23.692572+00:00
-- url     : https://prove2.me/theorems/10203910-0640-4ef1-8192-45ab224eed43
-- title:
--   Algorithm 2, pp. 22–23, 39 — runs of the inexact non-Hilbertian APG method, A_t, τ_t, E_t, v̄_t (5.22), ψ_t (G.1)
-- statement:
--   **Algorithm 2** (inexact non-Hilbertian APG method) takes a DGF $\omega_{\mathcal U}$, errors $\delta_t\ge0$, a parameter $\bar L>0$ with $\bar L\ge L_h$, and positive weights $\alpha_t$, and sets $A_t:=\sum_{i=0}^t\alpha_i$ (`accW`) and $\tau_t:=\alpha_t/A_t$ (`avgW`). A **run** (`IsAlg2Run`) consists of points $u_t,\bar u_t,z_t,w_t\in\mathbb U$, dual vectors $s_t,\hat\nabla h(u_t)\in\mathbb U^*$ and values $\hat h(u_t)$ with:
--
--   1. $u_0\in\mathcal U^o$, $s_0=\hat\nabla h(u_0)$, and $z_0\in\mathcal U^o$ minimizes $\langle s_0,u\rangle+\zeta(u)+\mu\omega_{\mathcal U}(u)+\bar LD_{\omega_{\mathcal U}}(u,u_0)$ over $\mathcal U$;
--   2. for every $t\ge0$:
--
--   $$
--   \begin{aligned}
--   \bar u_{t+1}&\in\operatorname*{arg\,min}_{u\in\mathcal U}\ \langle s_t,u\rangle+A_t(\zeta(u)+\mu\omega_{\mathcal U}(u))+\bar LD_{\omega_{\mathcal U}}(u,u_0), &&(5.10)\\
--   u_{t+1}&=(1-\tau_{t+1})z_t+\tau_{t+1}\bar u_{t+1}, &&(5.11)\\
--   s_{t+1}&=s_t+\alpha_{t+1}\hat\nabla h(u_{t+1}), &&(5.13)\\
--   w_{t+1}&\in\operatorname*{arg\,min}_{u\in\mathcal U}\ \alpha_{t+1}\big(\langle\hat\nabla h(u_{t+1}),u\rangle+\zeta(u)+\mu\omega_{\mathcal U}(u)\big)+(A_t\mu+\bar L)D_{\omega_{\mathcal U}}(u,\bar u_{t+1}), &&(5.14)\\
--   z_{t+1}&=(1-\tau_{t+1})z_t+\tau_{t+1}w_{t+1}, &&(5.15)
--   \end{aligned}
--   $$
--
--   with the minimizers $\bar u_{t+1}$, $w_{t+1}$ in $\mathcal U^o$.
--
--   The oracle step (5.12), that $(\hat h(u_t),\hat\nabla h(u_t))$ is a $(\delta_t,\bar L)$-FOA of $h$ at $u_t$, is stated by each theorem that uses it. The file also defines $E_t:=\sum_{i=0}^tA_i\delta_i$ (`errE`, (G.4)), the average $\bar v_t:=A_t^{-1}\sum_{i=0}^t\alpha_iv_i$ (`vbar`, (5.22)), and the estimate functions
--
--   $$
--   \psi_t(x):=\sum_{i=0}^t\alpha_i\big(\hat h(u_i)+\langle\hat\nabla h(u_i),x-u_i\rangle+\zeta(x)+\mu\omega_{\mathcal U}(x)\big)+\bar LD_{\omega_{\mathcal U}}(x,u_0) \tag{G.1}
--   $$
--
--   (`psiEst`), whose minimum over $\mathcal U$ is $\psi_t^*$ (G.2).
--
--   **Formalization Note** The page prints the initial subproblem with "$LD_{\omega_{\mathcal U}}(u,u_0)$"; it is $\bar LD_{\omega_{\mathcal U}}(u,u_0)$, as (G.1) at $t=0$ and the proof of Lemma G.1 show, and the Lean uses $\bar L$. Minimizers are predicates: the run asserts that the named points minimize. The page's BPP assumption makes them unique and places them in $\mathcal U^o$; the run states membership in $\mathcal U^o$ directly. `ubar 0` and `w 0` are unused. Indices start at $0$.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, pp. 22–23, 39, Algorithm 2, (5.10)–(5.16), (5.22), (G.1), (G.2), (G.4)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Bregman

namespace PDSmooth.Framework.Supplement

open PDSmooth.Framework

/-- Algorithm 2, p. 22: the accumulated weights `A_t = Σ_{i=0}^t α_i`. -/
noncomputable def accW (α : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), α i

/-- Algorithm 2, p. 22: the averaging sequence `τ_t = α_t / A_t`. -/
noncomputable def avgW (α : ℕ → ℝ) (t : ℕ) : ℝ :=
  α t / accW α t

/-- (G.4), p. 40: the accumulated errors `E_t = Σ_{i=0}^t A_i δ_i`. -/
noncomputable def errE (α δ : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), accW α i * δ i

/-- (5.22), p. 23: the weighted average `v̄_t = A_t⁻¹ Σ_{i=0}^t α_i v_i`. -/
noncomputable def vbar {VV : Type*} [AddCommGroup VV] [Module ℝ VV] (α : ℕ → ℝ) (v : ℕ → VV)
    (t : ℕ) : VV :=
  (accW α t)⁻¹ • ∑ i ∈ Finset.range (t + 1), α i • v i

/-- (G.1), p. 39: the estimate functions
`ψ_t(x) = Σ_{i=0}^t α_i (ĥ(u_i) + ⟨∇̂h(u_i), x − u_i⟩ + ζ(x) + μ ω_U(x)) + L̄ D_{ω_U}(x, u₀)`. -/
noncomputable def psiEst {UU : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU]
    (ζ ω : UU → ℝ) (μ Lbar : ℝ) (α hhat : ℕ → ℝ) (ghat : ℕ → UU →L[ℝ] ℝ) (u : ℕ → UU)
    (t : ℕ) (x : UU) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), α i * (hhat i + ghat i (x - u i) + ζ x + μ * ω x)
    + Lbar * bregman ω x (u 0)

/-- A run of Algorithm 2 (p. 22), apart from the first-order oracle (5.12), which the theorems
state separately: inputs `L̄ > 0` with `L̄ ≥ L_h`, positive weights `α_t`, errors `δ_t ≥ 0`;
`u₀ ∈ U° = U ∩ Wo`; `s₀ = ĝ₀`; `z₀ ∈ U°` minimizes `⟨s₀,u⟩ + ζ(u) + μ ω_U(u) + L̄ D(u,u₀)` over `U`;
and for every `t ≥ 0`: `ū_{t+1} ∈ U°` minimizes (5.10), `u_{t+1}` is given by (5.11), `s_{t+1}` by
(5.13), `w_{t+1} ∈ U°` minimizes (5.14), and `z_{t+1}` is given by (5.15). The values
`ĥ_t = hhat t`, `ĝ_t = ghat t` are the oracle outputs at `u_t`; `ubar 0` and `w 0` are unused. -/
structure IsAlg2Run {UU : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU]
    (U Wo : Set UU) (ζ ω : UU → ℝ) (μ Lh Lbar : ℝ) (α δ hhat : ℕ → ℝ)
    (ghat s : ℕ → UU →L[ℝ] ℝ) (u ubar z w : ℕ → UU) : Prop where
  Lbar_pos : 0 < Lbar
  Lh_le : Lh ≤ Lbar
  α_pos : ∀ t, 0 < α t
  δ_nonneg : ∀ t, 0 ≤ δ t
  u0_mem : u 0 ∈ U ∩ Wo
  s_zero : s 0 = ghat 0
  z_zero : z 0 ∈ U ∩ Wo ∧ ∀ x ∈ U,
    s 0 (z 0) + ζ (z 0) + μ * ω (z 0) + Lbar * bregman ω (z 0) (u 0)
      ≤ s 0 x + ζ x + μ * ω x + Lbar * bregman ω x (u 0)
  ubar_succ : ∀ t, ubar (t + 1) ∈ U ∩ Wo ∧ ∀ x ∈ U,
    s t (ubar (t + 1)) + accW α t * (ζ (ubar (t + 1)) + μ * ω (ubar (t + 1)))
        + Lbar * bregman ω (ubar (t + 1)) (u 0)
      ≤ s t x + accW α t * (ζ x + μ * ω x) + Lbar * bregman ω x (u 0)
  u_succ : ∀ t, u (t + 1) = (1 - avgW α (t + 1)) • z t + avgW α (t + 1) • ubar (t + 1)
  s_succ : ∀ t, s (t + 1) = s t + α (t + 1) • ghat (t + 1)
  w_succ : ∀ t, w (t + 1) ∈ U ∩ Wo ∧ ∀ x ∈ U,
    α (t + 1) * (ghat (t + 1) (w (t + 1)) + ζ (w (t + 1)) + μ * ω (w (t + 1)))
        + (accW α t * μ + Lbar) * bregman ω (w (t + 1)) (ubar (t + 1))
      ≤ α (t + 1) * (ghat (t + 1) x + ζ x + μ * ω x)
        + (accW α t * μ + Lbar) * bregman ω x (ubar (t + 1))
  z_succ : ∀ t, z (t + 1) = (1 - avgW α (t + 1)) • z t + avgW α (t + 1) • w (t + 1)

end PDSmooth.Framework.Supplement


