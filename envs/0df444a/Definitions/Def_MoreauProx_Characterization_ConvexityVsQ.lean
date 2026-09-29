-- Prove2me | Definitions.Def_MoreauProx_Characterization_ConvexityVsQ
-- name    : MoreauProx_Characterization_ConvexityVsQ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:17:07.890758+00:00
-- url     : https://prove2.me/theorems/ec2a5880-ed0d-466e-b676-91bba8cf2384
-- title:
--   Functions more convex or less convex than 𝒬(z) = ½‖z‖², and primitives of prox maps
-- statement:
--   Let $H$ be a real Hilbert space and $\mathcal{Q}(z) = \tfrac12 \|z\|^2$. Following Moreau, a convex function $\varphi_1$ is *more convex* than a convex function $\varphi_2$ (and $\varphi_2$ is *less convex* than $\varphi_1$) when there is a convex function $\gamma$ with values in $]-\infty, +\infty]$ such that $\varphi_1 = \varphi_2 + \gamma$. Only comparisons with $\mathcal{Q}$ are used:
--
--   1. $\varphi$ is **less convex than $\mathcal{Q}$** when there is a convex $\gamma : H \to \,]-\infty, +\infty]$ with
--   $$
--   \varphi(z) + \gamma(z) = \tfrac12 \|z\|^2 \quad \text{for all } z \in H;
--   $$
--   2. $\theta$ is **more convex than $\mathcal{Q}$** when there is a convex $\gamma : H \to \,]-\infty, +\infty]$ with
--   $$
--   \theta(y) = \tfrac12 \|y\|^2 + \gamma(y) \quad \text{for all } y \in H;
--   $$
--   3. $\varphi$ is **the primitive of a prox map** when there is $g \in \Gamma_0(H)$ such that $\varphi$ is the primitive of $\operatorname{prox}_g$, i.e. $\varphi(z) = \tfrac12 \|\operatorname{prox}_g z\|^2 + f(\operatorname{prox}_f z)$ for all $z$, where $f$ is the dual function of $g$.
--
--   These three notions are the vocabulary of Proposition 9.b and Proposition 10.b, which characterize the primitives of prox maps.
--
--   **Formalization Note** The auxiliary function $\gamma$ is `EReal`-valued, never $-\infty$, with convex epigraph; it may take the value $+\infty$, which the "more convex" comparison needs when the dual function takes $+\infty$ (for instance for indicator functions). The convexity of $\varphi$ or $\theta$ themselves is not part of these predicates: in every use it is separately assumed or proved that they lie in $\Gamma_0(H)$.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 288, §9.a (𝒬) and Définition 9.b; p. 289, Proposition 9.b (III)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_Prox
open scoped InnerProductSpace

namespace MoreauProx.Characterization

/-- Moreau Définition 9.b, second function `𝒬(z) = ½‖z‖²`: `φ` is less convex than `𝒬` when
`φ + γ = 𝒬` for some convex `γ : H → ]−∞, +∞]`. -/
def LessConvexThanQ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : H → EReal) : Prop :=
  ∃ γ : H → EReal, (∀ z, γ z ≠ ⊥) ∧ EConvex γ ∧
    ∀ z, φ z + γ z = ((‖z‖ ^ 2 / 2 : ℝ) : EReal)

/-- Moreau Définition 9.b, first function `𝒬(y) = ½‖y‖²`: `θ` is more convex than `𝒬` when
`θ = 𝒬 + γ` for some convex `γ : H → ]−∞, +∞]` (`γ` may take the value `+∞`). -/
def MoreConvexThanQ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (θ : H → EReal) : Prop :=
  ∃ γ : H → EReal, (∀ y, γ y ≠ ⊥) ∧ EConvex γ ∧
    ∀ y, θ y = ((‖y‖ ^ 2 / 2 : ℝ) : EReal) + γ y

/-- Moreau 9.b (III): `φ` is the primitive (Définition 7.a) of some proximal map `prox_g`,
`g ∈ Γ₀(H)`; the primitive is built from the pair `(f, g)` with `f` the dual of `g`. -/
def IsProxPrimitive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : H → EReal) : Prop :=
  ∃ g : H → EReal, GammaZero g ∧ ∀ z, φ z = ((primitive (conj g) g z : ℝ) : EReal)

end MoreauProx.Characterization


