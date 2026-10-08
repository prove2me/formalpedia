-- Prove2me | Definitions.Def_DisplMonoMFG_WellPosed_Monotone
-- name    : DisplMonoMFG_WellPosed_Monotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:21.283873+00:00
-- url     : https://prove2.me/theorems/d5e303b4-1bcb-4531-8390-f5224fad9102
-- title:
--   Displacement monotonicity (2.16), semimonotonicity (2.17) and displacement monotone Hamiltonians (3.2)
-- statement:
--   Let $U:\mathbb R^d\times\mathcal P_2\to\mathbb R$ be in $\mathcal C^2(\mathbb R^d\times\mathcal P_2)$. For $\xi,\eta\in\mathbb L^2$ with $\mathcal L_\xi=\mu$, let $(\tilde\xi,\tilde\eta)$ be an independent copy of $(\xi,\eta)$, and set
--
--   $$
--   (d_xd)_\xi U(\eta,\eta):=\tilde{\mathbb E}\Big[\big\langle\partial_{x\mu}U(\xi,\mathcal L_\xi,\tilde\xi)\tilde\eta,\eta\big\rangle+\big\langle\partial_{xx}U(\xi,\mathcal L_\xi)\eta,\eta\big\rangle\Big].
--   $$
--
--   1. $U$ is **displacement monotone** ((2.16), p. 2186) if $(d_xd)_\xi U(\eta,\eta)\ge0$ for all $\xi,\eta\in\mathbb L^2$.
--   2. $U$ is **displacement semimonotone** with constant $\lambda\ge0$ ((2.17), Definition 2.7, p. 2187) if $(d_xd)_\xi U(\eta,\eta)\ge-\lambda\,\mathbb E[|\eta|^2]$ for all $\xi,\eta$.
--   3. A Hamiltonian $H(x,\mu,p)$ is **displacement monotone** (Definition 3.4, (3.2), p. 2191) if, for every $\mu\in\mathcal P_2$, every $\xi$ of law $\mu$, every $\eta\in\mathbb L^2$ and every bounded Lipschitz $\varphi\in C^1(\mathbb R^d;\mathbb R^d)$,
--   $$
--   \tilde{\mathbb E}\Big[\big\langle\partial_{x\mu}H(\xi,\mu,\tilde\xi,\varphi(\xi))\tilde\eta+\partial_{xx}H(\xi,\mu,\varphi(\xi))\eta,\eta\big\rangle\Big]+\frac14\,\mathbb E\Big[\big|(\partial_{pp}H(\xi,\mu,\varphi(\xi)))^{-1/2}\,\tilde{\mathbb E}_{\mathcal F^1_T}\big[\partial_{p\mu}H(\xi,\mu,\tilde\xi,\varphi(\xi))\tilde\eta\big]\big|^2\Big]\le0.
--   $$
--   The momentum variable is evaluated at $\varphi(\xi)$, $\varphi$ of the first variable, in both terms. The inner conditional expectation integrates out $(\tilde\xi,\tilde\eta)$ only.
--
--   Displacement monotonicity of $G$ and of $H$ (Assumption 3.5) is the structural condition under which the paper proves global well-posedness of the master equation.
--
--   **Formalization Note** Expectations are integrals against the joint law $\pi$ of $(\xi,\eta)$ (an $\mathbb L^2$-coupling at $\mu$) and against $\pi\otimes\pi$ for the independent copy. Quantifying over all such couplings is the page's "for any $\xi,\eta\in\mathbb L^2(\mathcal F^1_T)$". The term $|A^{-1/2}w|^2$ is written $\langle A^{-1}w,w\rangle$, which is the same number for a symmetric positive definite $A$. Assumption 3.2(iv), as formalized, makes $\partial_{pp}H$ positive definite, so the matrix inverse is the true inverse.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), (2.16) p. 2186, Definition 2.7 (2.17) p. 2187, Definition 3.4 (3.2) p. 2191

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Regularity

open MeasureTheory Matrix

/-! Gangbo, Mészáros, Mou, Zhang, Ann. Probab. 50 (2022): displacement monotonicity (2.16)
(Definition 2.2(ii), Remark 2.3(ii), Remark 2.4, p. 2186), displacement semimonotonicity (2.17)
(Definition 2.7, p. 2187) and displacement monotone Hamiltonians (Definition 3.4, (3.2), p. 2191).
Expectations over `(ξ, η)` and an independent copy `(ξ̃, η̃)` are double integrals against
`π ⊗ π`, `π` the joint law of `(ξ, η)`. -/

namespace DisplMonoMFG.WellPosed

variable {d : ℕ}

/-- The bilinear form of (2.16), p. 2186:
`(d_x d)_ξ U(η, η) = Ẽ[⟨∂_xμ U(ξ, ℒ_ξ, ξ̃) η̃, η⟩ + ⟨∂_xx U(ξ, ℒ_ξ) η, η⟩]`, with `π` the joint
law of `(ξ, η)`, `μ = ℒ_ξ` and `(ξ̃, η̃)` an independent copy. -/
noncomputable def dxd (w : C2W d (E d) ℝ) (μ : P2 d) (π : Measure (E d × E d)) : ℝ :=
  (∫ z, ∫ z', w.DxDm z.1 μ z'.1 z.2 z'.2 ∂π ∂π) + ∫ z, w.Dxx z.1 μ z.2 z.2 ∂π

/-- Displacement monotonicity (2.16) of `U : ℝ^d × 𝒫₂ → ℝ` with `𝒞²` witnesses `w`:
`(d_x d)_ξ U(η, η) ≥ 0` for all `ξ, η ∈ 𝕃²` (all `𝕃²`-couplings). Remark 2.4 states that
(2.14) and (2.16) are equivalent; Assumption 3.5(i) says "namely, it satisfies (2.16)". -/
def DisplMono (w : C2W d (E d) ℝ) : Prop :=
  ∀ (μ : P2 d) (π : Measure (E d × E d)), IsL2Coupling μ π → 0 ≤ dxd w μ π

/-- Displacement semimonotonicity (2.17), Definition 2.7, p. 2187, with the constant `lam ≥ 0`:
`(d_x d)_ξ U(η, η) ≥ -λ 𝔼[|η|²]` for all `ξ, η ∈ 𝕃²`. -/
def DisplSemimono (w : C2W d (E d) ℝ) (lam : ℝ) : Prop :=
  ∀ (μ : P2 d) (π : Measure (E d × E d)), IsL2Coupling μ π →
    -lam * ∫ z, ‖z.2‖ ^ 2 ∂π ≤ dxd w μ π

/-- The `x`-direction `(u, 0)` in `ℝ^d × ℝ^d` (variables `(x, p)`). -/
def inX (u : E d) : E d × E d := (u, 0)

/-- The `p`-direction `(0, v)` in `ℝ^d × ℝ^d` (variables `(x, p)`). -/
def inP (v : E d) : E d × E d := (0, v)

/-- The matrix `∂_pp H(x, μ, p)`, from the `𝒞²` witness `wH` of `(x, p), μ ↦ H(x, μ, p)`. -/
noncomputable def ppMat (wH : C2W d (E d × E d) ℝ) (x p : E d) (μ : P2 d) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => wH.Dxx (x, p) μ (inP (e i)) (inP (e j))

/-- The `(d_x d)^φ_ξ H(η, η)` term of (3.2), p. 2191:
`Ẽ[⟨∂_xμ H(ξ, μ, ξ̃, φ(ξ)) η̃ + ∂_xx H(ξ, μ, φ(ξ)) η, η⟩]`. -/
noncomputable def dxdH (wH : C2W d (E d × E d) ℝ) (φ : E d → E d) (μ : P2 d)
    (π : Measure (E d × E d)) : ℝ :=
  (∫ z, ∫ z', wH.DxDm (z.1, φ z.1) μ z'.1 (inX z.2) z'.2 ∂π ∂π) +
    ∫ z, wH.Dxx (z.1, φ z.1) μ (inX z.2) (inX z.2) ∂π

/-- The vector `Ẽ_{ℱ¹_T}[∂_pμ H(ξ, μ, ξ̃, φ(ξ)) η̃]` evaluated at `ξ = x`:
`∫ ∂_pμ H(x, μ, x̃, φ(x)) ṽ π(dx̃ dṽ)`, component `i` being the `pᵢ`-derivative. -/
noncomputable def pmuVec (wH : C2W d (E d × E d) ℝ) (φ : E d → E d) (μ : P2 d)
    (π : Measure (E d × E d)) (x : E d) : Fin d → ℝ :=
  fun i => ∫ z', wH.DxDm (x, φ x) μ z'.1 (inP (e i)) z'.2 ∂π

/-- The `Q^φ_ξ H(η, η)` term of (3.2), p. 2191:
`(1/4) 𝔼[|(∂_pp H(ξ, μ, φ(ξ)))^{-1/2} Ẽ_{ℱ¹_T}[∂_pμ H(ξ, μ, ξ̃, φ(ξ)) η̃]|²]`.
Formalization Note: `|A^{-1/2} w|² = ⟨A^{-1} w, w⟩` for a symmetric positive definite `A`; under
Assumption 3.2(iv) (as encoded in `Assm32iv`) `∂_pp H` is positive definite, so `⁻¹` is the true
inverse. -/
noncomputable def QH (wH : C2W d (E d × E d) ℝ) (φ : E d → E d) (μ : P2 d)
    (π : Measure (E d × E d)) : ℝ :=
  (1 / 4 : ℝ) * ∫ z, pmuVec wH φ μ π z.1 ⬝ᵥ
    ((ppMat wH z.1 (φ z.1) μ)⁻¹ *ᵥ pmuVec wH φ μ π z.1) ∂π

/-- Definition 3.4, (3.2), p. 2191: `H` is displacement monotone if for every `μ ∈ 𝒫₂`, every
`ξ` of law `μ`, every `η ∈ 𝕃²` (i.e. every `𝕃²`-coupling `π` at `μ`) and every bounded Lipschitz
`φ ∈ C¹(ℝ^d; ℝ^d)`, `(d_x d)^φ_ξ H(η, η) + Q^φ_ξ H(η, η) ≤ 0`. Note that `p` is evaluated at
`φ(ξ)`, `φ` of the first variable, in both terms. -/
def DisplMonoH (wH : C2W d (E d × E d) ℝ) : Prop :=
  ∀ (μ : P2 d) (π : Measure (E d × E d)) (φ : E d → E d),
    IsL2Coupling μ π → ContDiff ℝ 1 φ → (∃ K, LipschitzWith K φ) → (∃ M, ∀ x, ‖φ x‖ ≤ M) →
      dxdH wH φ μ π + QH wH φ μ π ≤ 0

end DisplMonoMFG.WellPosed


