-- Prove2me | Definitions.Def_SinkhornDRO_BSMD_Objective
-- name    : SinkhornDRO_BSMD_Objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:24:20.932329+00:00
-- url     : https://prove2.me/theorems/9c45c3ef-6108-46bd-bbd7-57c055fa9e24
-- title:
--   The objective (11) F, its level-ℓ approximation (14) F^ℓ, the sampling law of ζ^ℓ, and Assumption 2
-- statement:
--   Let $\mathcal Z$ be a measurable space, $\widehat{\mathbb P}$ a probability measure on $\mathcal Z$ (the nominal distribution) and $x\mapsto\mathbb Q_x$ a Markov kernel on $\mathcal Z$ (the paper's $\mathbb Q_{x,\epsilon}$). Fix $\lambda,\epsilon>0$ and a loss $f_\theta(z)$.
--
--   1. **Objective (11).** $$F(\theta)=\mathbb E_{x\sim\widehat{\mathbb P}}\Big[\lambda\epsilon\log\mathbb E_{z\sim\mathbb Q_x}\big[e^{f_\theta(z)/(\lambda\epsilon)}\big]\Big].$$
--
--   2. **Sampling law of $\zeta^\ell$.** $\zeta=(x,z_1,\dots,z_n)$ with $x\sim\widehat{\mathbb P}$ and, given $x$, $z_1,\dots,z_n$ i.i.d. from $\mathbb Q_x$. The level-$\ell$ sample $\zeta^\ell$ has $n=2^\ell$.
--
--   3. **Level-$\ell$ approximation (14).** $$F^\ell(\theta)=\mathbb E_{\zeta^\ell}\Big[\lambda\epsilon\log\Big(\frac1{2^\ell}\sum_{j=1}^{2^\ell}e^{f_\theta(z_j)/(\lambda\epsilon)}\Big)\Big].$$
--
--   4. **Assumption 2.** (I) $f_\theta(z)$ is convex in $\theta$ for every $z$; (II) $|f_{\theta_1}(z)-f_{\theta_2}(z)|\le L_f\|\theta_1-\theta_2\|_2$ for all $z,\theta_1,\theta_2$; (III) $0\le f_\theta(z)\le B$ for every $\theta\in\Theta$ and $z$.
--
--   5. **Subgradient selector.** A map $(\theta,z)\mapsto\nabla_\theta f_\theta(z)$ with $f_\theta(z)+\langle\nabla_\theta f_\theta(z),\theta'-\theta\rangle\le f_{\theta'}(z)$ for all $\theta'$; this is the paper's "arbitrary subgradient from its subdifferential".
--
--   $F$ is the inner objective of the dual reformulation (D) at a fixed multiplier $\lambda$, and $F^\ell$ is the nested-sample approximation whose subgradients can be estimated without bias.
--
--   **Formalization Note** $\mathbb Q_x$ is an arbitrary Markov kernel, not only the Gibbs kernel (3) of the paper; nothing in the BSMD analysis uses the Gibbs form, so this contains the paper's case. The law of $\zeta$ is `P.bind (fun x => dirac x ⊗ ∏_j Q x)`; the map $x\mapsto\delta_x\otimes\mathbb Q_x^{\otimes n}$ is measurable, so this is the paper's law. Assumption 2(I) is convexity on all of $\mathbb R^{d_\theta}$, as the page states it without a domain; (III) holds on $\Theta$ only.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. 14, (11); p. 15, (14) and the sampling of ζ^ℓ; p. 17, Assumption 2; p. 14 (∇_θ convention)

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace SinkhornDRO.BSMD

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

/-- The sampling law of `ζ = (x, z_1, …, z_n)` (p. 15): `x ∼ P̂`, and given `x`, the `z_j` are
i.i.d. draws from `Q_x`. With `n = 2^ℓ` this is the law of the level-`ℓ` sample `ζ^ℓ`. -/
noncomputable def levelLaw (P : Measure Z) (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    Measure (Z × (Fin n → Z)) :=
  P.bind (fun x => (Measure.dirac x).prod (Measure.pi fun _ : Fin n => Q x))

/-- The objective (11), p. 14, at a fixed multiplier `λ`:
`F(θ) = E_{x∼P̂}[ λε log E_{z∼Q_x}[ e^{f_θ(z)/(λε)} ] ]`. -/
noncomputable def objF (P : Measure Z) (Q : Kernel Z Z) (lam eps : ℝ) (f : Param d → Z → ℝ)
    (θ : Param d) : ℝ :=
  ∫ x, lam * eps * Real.log (∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x)) ∂P

/-- The level-`ℓ` approximation (14), p. 15:
`F^ℓ(θ) = E_{x∼P̂} E_{z_1,…,z_{2^ℓ} ∼ Q_x i.i.d.}[ λε log( 2^{−ℓ} Σ_j e^{f_θ(z_j)/(λε)} ) ]`. -/
noncomputable def objFℓ (P : Measure Z) (Q : Kernel Z Z) [IsMarkovKernel Q] (lam eps : ℝ)
    (f : Param d → Z → ℝ) (ℓ : ℕ) (θ : Param d) : ℝ :=
  ∫ ζ, lam * eps * Real.log (((2 : ℝ) ^ ℓ)⁻¹ * ∑ j, Real.exp (f θ (ζ.2 j) / (lam * eps)))
    ∂(levelLaw P Q (2 ^ ℓ))

/-- Assumption 2 (I), p. 17: `f_θ(z)` is convex in `θ`. -/
def Asm2Convex (f : Param d → Z → ℝ) : Prop :=
  ∀ z, ConvexOn ℝ Set.univ (fun θ => f θ z)

/-- Assumption 2 (II), p. 17: `|f_{θ₁}(z) − f_{θ₂}(z)| ≤ L_f ‖θ₁ − θ₂‖₂` for all `z, θ₁, θ₂`. -/
def Asm2Lipschitz (f : Param d → Z → ℝ) (Lf : ℝ) : Prop :=
  ∀ z θ₁ θ₂, |f θ₁ z - f θ₂ z| ≤ Lf * ‖θ₁ - θ₂‖

/-- Assumption 2 (III), p. 17: `0 ≤ f_θ(z) ≤ B` for every `θ ∈ Θ` and `z ∈ Z`. -/
def Asm2Bounded (Θ : Set (Param d)) (f : Param d → Z → ℝ) (B : ℝ) : Prop :=
  ∀ θ ∈ Θ, ∀ z, 0 ≤ f θ z ∧ f θ z ≤ B

/-- `sg` selects a subgradient of `θ ↦ f_θ(z)` at every `θ` and `z` (the paper's `∇_θ f_θ(z)`,
p. 14: "an arbitrary subgradient from its subdifferential"):
`f_θ(z) + ⟨sg θ z, θ' − θ⟩ ≤ f_{θ'}(z)` for all `θ'`. -/
def IsSubgradSel (f : Param d → Z → ℝ) (sg : Param d → Z → Param d) : Prop :=
  ∀ θ z θ', f θ z + ⟪sg θ z, θ' - θ⟫ ≤ f θ' z

end SinkhornDRO.BSMD


