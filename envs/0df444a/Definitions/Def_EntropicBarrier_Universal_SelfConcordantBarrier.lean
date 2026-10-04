-- Prove2me | Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
-- name    : EntropicBarrier_Universal_SelfConcordantBarrier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:42:49.90167+00:00
-- url     : https://prove2.me/theorems/69886206-f48b-400f-a8d1-def496126985
-- title:
--   Barrier, condition (3) and $\nu$-self-concordant barrier (Definition 1)
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ and $g:\operatorname{int}(\mathcal K)\to\mathbb R$. Write $\nabla g(x)[h]$, $\nabla^2 g(x)[h,h]$ and $\nabla^3 g(x)[h,h,h]$ for the first, second and third derivatives of $g$ at $x$ in the direction $h$.
--
--   1. $g$ is a **barrier** for $\mathcal K$ if $g(x)\to+\infty$ as $x\to\partial\mathcal K$: for every boundary point $x_0$ of $\mathcal K$, $g(x)\to+\infty$ as $x\to x_0$ with $x\in\operatorname{int}(\mathcal K)$.
--   2. A $C^3$-smooth convex $g$ is **self-concordant** if for all $x\in\operatorname{int}(\mathcal K)$ and $h\in\mathbb R^n$
--   $$\nabla^3 g(x)[h,h,h]\le 2\left(\nabla^2 g(x)[h,h]\right)^{3/2}. \tag{2}$$
--   3. It **satisfies (3) with parameter $\nu$** if for all $x\in\operatorname{int}(\mathcal K)$ and $h\in\mathbb R^n$
--   $$\nabla g(x)[h]\le\sqrt{\nu\cdot\nabla^2 g(x)[h,h]}. \tag{3}$$
--   4. $g$ is a **$\nu$-self-concordant barrier** for $\mathcal K$ if it is a barrier, self-concordant, and satisfies (3) with parameter $\nu$.
--
--   The parameter $\nu$ governs the number of Newton steps an interior-point method needs, $O(\sqrt\nu)$ per constant-factor decrease of the duality gap.
--
--   **Formalization Note** Condition (2) is the published definition `ConvexOptimization.IsSelfConcordantOn (interior K) g`: convex, $C^3$ on the open set, and $|\varphi'''(0)|\le 2\varphi''(0)^{3/2}$ for every line restriction $\varphi(t)=g(x+th)$. This is equivalent to (2): replacing $h$ by $-h$ flips the sign of the third derivative and keeps the second, so (2) for all $h$ is the absolute-value form; and for a $C^3$ function on an open set the derivatives of the line restriction at $0$ are the iterated Fréchet derivatives on the diagonal. In (3), $\nabla g(x)[h]$ is `fderiv ℝ g x h` and $\nabla^2 g(x)[h,h]$ is `iteratedFDeriv ℝ 2 g x (fun _ => h)`. The barrier limit is taken within `interior K` (`𝓝[interior K] x₀`), at every point of `frontier K`; a limit along the full neighbourhood filter would see values outside $\mathcal K$ that the paper never defines. $g$ is a function on all of $\mathbb R^n$ whose values outside $\operatorname{int}(\mathcal K)$ are never used.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 2, Definition 1, eqs. (2)-(3)

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace
open Filter Topology

namespace EntropicBarrier.Universal

/-- **Barrier** (Definition 1, p. 2): `g(x) → +∞` as `x → ∂K`, read as: for every boundary
point `x₀` of `K`, `g(x) → +∞` as `x → x₀` within `int(K)`. -/
def IsBarrier {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x₀ ∈ frontier K, Tendsto g (𝓝[interior K] x₀) atTop

/-- Condition (3) of Definition 1 (p. 2): `∇g(x)[h] ≤ √(ν · ∇²g(x)[h,h])` for all
`x ∈ int(K)` and `h ∈ ℝⁿ`. -/
def SatisfiesNuBound {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) : Prop :=
  ∀ x ∈ interior K, ∀ h : EuclideanSpace ℝ (Fin n),
    fderiv ℝ g x h ≤ Real.sqrt (ν * iteratedFDeriv ℝ 2 g x (fun _ => h))

/-- **`ν`-self-concordant barrier** for `K` (Definition 1, p. 2): a barrier for `K` that is
self-concordant on `int(K)` (condition (2), via the published
`ConvexOptimization.IsSelfConcordantOn`) and satisfies condition (3) with parameter `ν`. -/
def IsNuSelfConcordantBarrier {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) : Prop :=
  IsBarrier K g ∧ ConvexOptimization.IsSelfConcordantOn (interior K) g ∧
    SatisfiesNuBound K g ν

end EntropicBarrier.Universal


