-- Prove2me | Definitions.Def_GPhNGIDiffusion_EMError_EulerMaruyama
-- name    : GPhNGIDiffusion_EMError_EulerMaruyama
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:51.191435+00:00
-- url     : https://prove2.me/theorems/3e4c1c0b-da0d-400b-ad64-645d3e4bd5c8
-- title:
--   Euler–Maruyama chain $\tilde X_{k+1}=\tilde X_k+g(\tilde X_k)\eta+\sqrt\eta\,\sigma\xi_{k+1}$: kernel $\tilde P_\eta$, laws $(\tilde P_\eta^k)^*\nu$, invariance
-- statement:
--   Let $b:\mathbb R^d\to\mathbb R^d$, $\sigma\in\mathbb R^{d\times d}$ and a step $\eta>0$. The **Euler–Maruyama chain** is
--   $$
--   \tilde X^\eta_{k+1}=\tilde X^\eta_k+b(\tilde X^\eta_k)\,\eta+\sqrt\eta\,\sigma\xi_{k+1},\qquad k\in\mathbb N_0,
--   $$
--   with $\xi_1,\xi_2,\dots$ independent standard $d$-dimensional Gaussian vectors. Its one-step transition is
--   $$
--   \tilde P_\eta(x,\cdot)=\text{law of } x+\eta b(x)+\sqrt\eta\,\sigma\xi=\mathcal N\big(x+\eta b(x),\ \eta\sigma\sigma'\big),
--   $$
--   with $\tilde P_\eta f(x)=\int f(y)\,\tilde P_\eta(x,dy)$. The law of $\tilde X^\eta_k$ when $\tilde X^\eta_0\sim\nu$ is $(\tilde P^k_\eta)^*\nu$, defined by $(\tilde P^0_\eta)^*\nu=\nu$ and $(\tilde P^{k+1}_\eta)^*\nu=\int\tilde P_\eta(x,\cdot)\,(\tilde P^k_\eta)^*\nu(dx)$. A probability measure $\tilde\mu$ is **invariant** for the chain if $\int\tilde P_\eta(x,\cdot)\,\tilde\mu(dx)=\tilde\mu$.
--
--   With $b=g$ the model's drift this is the scheme (1.2) whose invariant measure $\tilde\mu_\eta$ approximates the invariant measure $\mu$ of the diffusion.
--
--   **Formalization Note** The kernel is the image of Mathlib's standard Gaussian `stdGaussian` on `EuclideanSpace ℝ (Fin d)` under $z\mapsto x+\eta b(x)+\sqrt\eta\,\sigma z$, the most direct reading of (1.2). The index $k$ starts at $0$.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 3, (1.2); p. 7, the one-step transition P̃_η; p. 27, proof of Lemma A.2

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GPhNGIDiffusion_EMError_Model

open MeasureTheory ProbabilityTheory

namespace GPhNGIDiffusion.EMError

variable {d : ℕ}

/-- The one-step transition `P̃_η(x, ·)` of the Euler–Maruyama chain (1.2), p. 3,
`X̃_{k+1} = X̃_k + b(X̃_k) η + √η σ ξ_{k+1}` with `ξ_{k+1}` standard `d`-dimensional Gaussian: the law
of `x + η b(x) + √η σ ξ`, i.e. `N(x + η b(x), η σσ′)`. -/
noncomputable def emStep (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (σ : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (x : EthierKurtz.SDEState d) :
    Measure (EthierKurtz.SDEState d) :=
  (stdGaussian (EthierKurtz.SDEState d)).map (fun z => x + η • b x + Real.sqrt η • mv σ z)

/-- `P̃_η f(x) = ∫ f(y) P̃_η(x, dy) = E f(X̃^{η,x}_1)` (p. 7). -/
noncomputable def emOp (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (σ : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (f : EthierKurtz.SDEState d → ℝ)
    (x : EthierKurtz.SDEState d) : ℝ :=
  ∫ y, f y ∂(emStep b σ η x)

/-- The law `(P̃^k_η)^* ν` of `X̃^η_k` when `X̃^η_0 ∼ ν`, for `k ∈ ℕ₀ = {0, 1, 2, …}`. -/
noncomputable def emLaw (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (σ : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (ν : Measure (EthierKurtz.SDEState d)) :
    ℕ → Measure (EthierKurtz.SDEState d)
  | 0 => ν
  | k + 1 => (emLaw b σ η ν k).bind (emStep b σ η)

/-- `µ̃` is an invariant probability measure of the Euler–Maruyama chain with step `η`:
`∫ P̃_η(x, ·) µ̃(dx) = µ̃`. -/
def IsEMInvariant (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (σ : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (μ : Measure (EthierKurtz.SDEState d)) : Prop :=
  IsProbabilityMeasure μ ∧ μ.bind (emStep b σ η) = μ

end GPhNGIDiffusion.EMError


