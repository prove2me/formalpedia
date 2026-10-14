-- Prove2me | Definitions.Def_CondPortOT_FiberDual_Setting
-- name    : CondPortOT_FiberDual_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:29.106845+00:00
-- url     : https://prove2.me/theorems/d33e91c2-12c8-4206-a62c-a920fa9cea6d
-- title:
--   (16), p. 20 — the dual feasible set 𝒱 of Theorem 4.4
-- statement:
--   This file fixes the dual feasible set of Theorem 4.4 in the conditional distributionally robust portfolio problem of Nguyen, Zhang, Wang, Blanchet, Delage and Ye. The other objects of the mission (ground cost, empirical measure, transport ball, fiber, conditional expectation, worst-case value, $\rho_{\min}$, $\kappa_i$, $d_i$, $\mathcal I_1$, Assumption 2.4 and the boundary-regularity predicate) come from the shared definition modules of this paper.
--
--   Let $N\ge1$, let $d\in\mathbb R^N$ (in Theorem 4.4, $d_i$ is the distance (14) from the sample $\hat x_i$ to the boundary of the neighbourhood $\mathcal N_\gamma(x_0)$), let $\mathcal I_1\subseteq[N]$ with complement $\mathcal I_2$, and let $\rho\in\mathbb R$. The set $\mathcal V$ of display (16) consists of the tuples $(\lambda,s,\nu^+,\nu^-,\phi,\varphi,\psi)\in\mathbb R^N_+\times\mathbb R^N\times\mathbb R_+\times\mathbb R_+\times\mathbb R\times\mathbb R_+\times\mathbb R^N_+$ such that
--   $$\begin{aligned}&\phi-d_i\varphi+\psi_i-s_i\ge0\quad\forall i\in\mathcal I_1,\qquad \phi+d_i\varphi+\psi_i-s_i\ge0\quad\forall i\in\mathcal I_2,\\&\nu^+-\nu^-+\Big(\sum_{i\in\mathcal I_1}d_i-N\rho\Big)\varphi-\sum_{i\in[N]}\psi_i\ge0,\qquad \varphi-\lambda_i\ge0\quad\forall i\in[N].\end{aligned}$$
--
--   Theorem 4.4 expresses the worst-case conditional expected loss as the infimum of $\phi+(N\varepsilon)^{-1}\nu^+-N^{-1}\nu^-$ over this set, under one further semi-infinite constraint on $s$.
--
--   **Formalization Note.** $[N]$ is `Fin N`. A point of $\mathbb R^N\times\mathbb R^N\times\mathbb R^5\times\mathbb R^N$ is the structure `DualPt N` with its seven fields in the printed order; `phi` is the free variable $\phi$ and `vphi` is $\varphi\ge0$. All sign constraints are in `InV`, which takes $d$, $\mathcal I_1$ (as a `Finset`) and $\rho$ as parameters; $\mathcal I_2$ is its complement.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 20, display (16)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_CondPortOT_BigRadius_Setting
import Definitions.Def_CondPortOT_SingDual_Setting
import Definitions.Def_CondPortOT_SingUninf_Setting

namespace CondPortOT.FiberDual

open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

open Classical in

/-- A point `(λ, s, ν⁺, ν⁻, ϕ, φ, ψ)` of `ℝᴺ × ℝᴺ × ℝ × ℝ × ℝ × ℝ × ℝᴺ`, in the order of (16), p. 20.
`phi` is the free variable `ϕ`, `vphi` the variable `φ`; the signs are imposed by `InV`. -/
structure DualPt (N : ℕ) where
  /-- `λ ∈ ℝᴺ` -/
  lam : Fin N → ℝ
  /-- `s ∈ ℝᴺ` -/
  s : Fin N → ℝ
  /-- `ν⁺` -/
  nuP : ℝ
  /-- `ν⁻` -/
  nuM : ℝ
  /-- `ϕ` (free) -/
  phi : ℝ
  /-- `φ` -/
  vphi : ℝ
  /-- `ψ ∈ ℝᴺ` -/
  psi : Fin N → ℝ

/-- The dual feasible set `𝒱` of (16), p. 20, for given `dᵢ`, `ℐ₁` and `ρ`:
`λ ∈ ℝᴺ₊`, `s ∈ ℝᴺ`, `ν⁺, ν⁻ ∈ ℝ₊`, `ϕ ∈ ℝ`, `φ ∈ ℝ₊`, `ψ ∈ ℝᴺ₊` with
`ϕ − dᵢφ + ψᵢ − sᵢ ≥ 0` (`i ∈ ℐ₁`), `ϕ + dᵢφ + ψᵢ − sᵢ ≥ 0` (`i ∈ ℐ₂`),
`ν⁺ − ν⁻ + (Σ_{i∈ℐ₁} dᵢ − Nρ)φ − Σ_{i∈[N]} ψᵢ ≥ 0` and `φ − λᵢ ≥ 0` (`i ∈ [N]`). -/
def InV {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (v : DualPt N) : Prop :=
  (∀ i, 0 ≤ v.lam i) ∧ 0 ≤ v.nuP ∧ 0 ≤ v.nuM ∧ 0 ≤ v.vphi ∧ (∀ i, 0 ≤ v.psi i) ∧
  (∀ i ∈ I, 0 ≤ v.phi - d i * v.vphi + v.psi i - v.s i) ∧
  (∀ i ∉ I, 0 ≤ v.phi + d i * v.vphi + v.psi i - v.s i) ∧
  0 ≤ v.nuP - v.nuM + (∑ i ∈ I, d i - N * ρ) * v.vphi - ∑ i, v.psi i ∧
  (∀ i, 0 ≤ v.vphi - v.lam i)

end CondPortOT.FiberDual


