-- Prove2me | Definitions.Def_GPhNGIDiffusion_OccupationCLT_Ito
-- name    : GPhNGIDiffusion_OccupationCLT_Ito
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:19.621993+00:00
-- url     : https://prove2.me/theorems/f1c295fd-2ff0-4d4f-bcdc-f05d0090b259
-- title:
--   (3.14), p. 15 — the Itô integral ∫₀ᵗ⟨H_r, dB_r⟩ as the L² limit of dyadic left-point Riemann sums
-- statement:
--   Let $B$ be a $d$-dimensional Brownian motion on $(\Omega,\mathcal F,\mathbb P)$ and $(H_r)_{r\ge0}$ an $\mathbb R^d$-valued process. For $t\ge0$ and $n\in\mathbb N$ put $t_k=kt/2^n$ and
--   $$
--   S_n=\sum_{k=0}^{2^n-1}\big\langle H_{t_k},\,B_{t_{k+1}}-B_{t_k}\big\rangle .
--   $$
--   A random variable $I$ is the **Itô integral** $\int_0^t\langle H_r,dB_r\rangle$ if $\mathbb E|S_n-I|^2\to0$ as $n\to\infty$.
--
--   For integrands with continuous paths that are bounded on $[0,t]$ and adapted to the filtration of $B$, which is the case of the integrands $\sigma^{-1}J^{\varepsilon,x}_ru$ and $\sigma^{-1}J^x_ru$ of (3.14), this limit exists and coincides almost surely with the Itô integral. The paper's random variables are
--   $$
--   \mathcal I^{\varepsilon,x}_u(t)=\frac1t\int_0^t\langle\sigma^{-1}J^{\varepsilon,x}_ru,dB_r\rangle,\qquad \mathcal I^{x}_u(t)=\frac1t\int_0^t\langle\sigma^{-1}J^{x}_ru,dB_r\rangle .
--   $$
--
--   **Formalization Note** Mathlib has no Itô integral, so the integral is characterized by this predicate; statements quantify over every $I$ satisfying it, which is faithful because such an $I$ exists and is unique up to a null set.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 15, (3.14)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The left-point Riemann sum `∑_{k < 2ⁿ} ⟨H_{t_k}, B_{t_{k+1}} − B_{t_k}⟩` of `∫₀ᵗ ⟨H_r, dB_r⟩`
on the dyadic partition `t_k = k t / 2ⁿ` of `[0, t]`. -/
noncomputable def riemannSum (H : ℝ≥0 → Ω → E d) (B : ℝ≥0 → Ω → E d) (t : ℝ≥0) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n),
    inner ℝ (H (k * t / 2 ^ n) ω) (B ((k + 1) * t / 2 ^ n) ω - B (k * t / 2 ^ n) ω)

/-- `I` is the Itô integral `∫₀ᵗ ⟨H_r, dB_r⟩`: the dyadic left-point Riemann sums converge to
`I` in `L²(P)`. For integrands with continuous paths that are bounded and adapted to the
filtration of `B` (the integrands of (3.14)) this limit exists and is the Itô integral. -/
def IsItoIntegral (P : Measure Ω) (B : ℝ≥0 → Ω → E d) (H : ℝ≥0 → Ω → E d) (t : ℝ≥0)
    (I : Ω → ℝ) : Prop :=
  Tendsto (fun n => ∫⁻ ω, ‖riemannSum H B t n ω - I ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)

end GPhNGIDiffusion.OccupationCLT


