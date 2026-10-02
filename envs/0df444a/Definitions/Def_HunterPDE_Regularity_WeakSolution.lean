-- Prove2me | Definitions.Def_HunterPDE_Regularity_WeakSolution
-- name    : HunterPDE_Regularity_WeakSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T19:18:57.050161+00:00
-- url     : https://prove2.me/theorems/82befa92-d80f-473a-9081-6e96c1cd3b1b
-- title:
--   Uniform ellipticity (4.18) and weak solutions of −∑∂ᵢ(aᵢⱼ∂ⱼu) = f ((4.34)–(4.37))
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and let $a_{ij} : \Omega \to \mathbb{R}$, $1 \le i,j \le n$, be coefficient functions. The coefficients are **uniformly elliptic** on $\Omega$ with constant $\theta > 0$ if
--   $$\sum_{i,j=1}^n a_{ij}(x)\,\xi_i \xi_j \ge \theta |\xi|^2 \qquad \text{for almost every } x \in \Omega \text{ and every } \xi \in \mathbb{R}^n.$$
--   For the operator $Lu = -\sum_{i,j} \partial_i(a_{ij}\partial_j u)$ the bilinear form is
--   $$a(u, v) = \sum_{i,j=1}^n \int_\Omega a_{ij}\, \partial_i u\, \partial_j v \, dx,$$
--   with weak partial derivatives on $\Omega$. For $f \in L^2(\Omega)$, a function $u \in H^1(\Omega)$ is a **weak solution** of $Lu = f$ in $\Omega$ if $a(u, v) = (f, v) = \int_\Omega f v\,dx$ for all $v \in H^1_0(\Omega)$. No boundary condition is imposed on $u$.
--
--   **Formalization Note.** Indices are 0-based (`Fin n`). The coefficients are functions on all of $\mathbb{R}^n$ of which only the values on $\Omega$ matter. The bilinear form and the right-hand side are Bochner integrals, which are well defined under the standing assumptions $a_{ij} \in L^\infty(\Omega)$ and $f \in L^2(\Omega)$ that every theorem using `IsWeakSolution` states as hypotheses. $H^1(\Omega)$ is `MemW 1 2 Ω` and $H^1_0(\Omega)$ is `MemW0 1 2 Ω`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 101, 110–111, Definition 4.16, Eqs. (4.18), (4.34)–(4.37)

import Mathlib
import Definitions.Def_HunterPDE_Regularity_Sobolev

open MeasureTheory

namespace HunterPDE.Regularity

/-- Uniform ellipticity (Hunter, Definition 4.16, (4.18)) of the principal coefficients
`a = (aᵢⱼ)` on `Ω` with constant `θ`: `θ > 0` and `∑ᵢⱼ aᵢⱼ(x) ξᵢ ξⱼ ≥ θ |ξ|²` for almost every
`x ∈ Ω` and every `ξ ∈ ℝⁿ`. Indices are 0-based (`Fin n`). -/
def UniformlyElliptic {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ) : Prop :=
  0 < θ ∧ ∀ᵐ x ∂(volume.restrict Ω), ∀ ξ : Fin n → ℝ,
    θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j

/-- The bilinear form (4.37) of `L u = −∑ᵢⱼ ∂ᵢ(aᵢⱼ ∂ⱼ u)`:
`a(u, v) = ∑ᵢⱼ ∫_Ω aᵢⱼ ∂ᵢu ∂ⱼv dx`, with `∂ᵢ` the weak partial derivatives on `Ω`
(`weakDeriv Ω (Pi.single i 1)`). Meaningful for `u, v ∈ H¹(Ω)` and `aᵢⱼ ∈ L^∞(Ω)`, which every
statement using it assumes. -/
noncomputable def bilinForm {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∑ i, ∑ j, ∫ x in Ω,
    a i j x * Shared.weakDeriv Ω (Pi.single i 1) u x * Shared.weakDeriv Ω (Pi.single j 1) v x

/-- Weak solution (Hunter (4.36)–(4.37)) of `L u = f` in `Ω`, `L u = −∑ᵢⱼ ∂ᵢ(aᵢⱼ ∂ⱼu)`
((4.34)–(4.35)): `u ∈ H¹(Ω) = W^{1,2}(Ω)` and `a(u, v) = (f, v) = ∫_Ω f v dx` for all
`v ∈ H¹₀(Ω) = W^{1,2}_0(Ω)`. No boundary condition is imposed on `u`. -/
def IsWeakSolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  MemW 1 2 Ω u ∧ ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, MemW0 1 2 Ω v →
    bilinForm Ω a u v = ∫ x in Ω, f x * v x

end HunterPDE.Regularity


