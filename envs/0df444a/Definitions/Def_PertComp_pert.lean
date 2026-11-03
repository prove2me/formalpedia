-- Prove2me | Definitions.Def_PertComp_pert
-- name    : PertComp_pert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:07.124492+00:00
-- url     : https://prove2.me/theorems/3da81fe7-8f23-4e98-a30c-2e436f69c2ff
-- title:
--   The perturbation function $F$ of (1.8)
-- statement:
--   In the setting of Problem 1.1 the perturbation function $F\colon X\times\mathbb R\times Y\to\,]-\infty,+\infty]$ is
--   $$F(x,\xi,y)=\begin{cases}\varphi\big(f(x)+\xi\big)+(g\,\Box\,\ell)(Lx+y)+h(x), & f(x)+\xi\in\operatorname{dom}\varphi;\\ +\infty, & f(x)+\xi\notin\operatorname{dom}\varphi.\end{cases}$$
--   Problem 1.1 is to minimize $F(x,0,0)$. $F$ is a perturbation in the sense of Definition 2.10 with $U=\mathbb R\oplus Y$.
--
--   The helper `dualPair` identifies $(\xi^*,y^*)\in\mathbb R\times Y^*$ with the functional $(\xi,y)\mapsto\xi\xi^*+\langle y,y^*\rangle$ on $\mathbb R\oplus Y$ (pairing (2.1)), the paper's dual variable of $F$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, (1.8), p.3

import Mathlib
import Definitions.Def_PertComp_infConv

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, (1.8), p.3: the perturbation function of
Problem 1.1, `F : X × ℝ × Y → ]−∞, +∞]`,
`F(x, ξ, y) = φ(f(x) + ξ) + (g □ ℓ)(Lx + y) + h(x)` if `f(x) + ξ ∈ dom φ`, and `+∞` if
`f(x) + ξ ∉ dom φ`.

**Formalization Note.** Written as a function on `X × (ℝ × Y)` so that it is a perturbation in
the sense of Definition 2.10 with `U = ℝ ⊕ Y`; `pert φ f g ℓ L h (x, ξ, y)` is `F(x, ξ, y)`. -/
noncomputable def pert {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (φ : ℝ → EReal) (f : X → EReal)
    (g ℓ : Y → EReal) (L : X →L[ℝ] Y) (h : X → EReal) : X × (ℝ × Y) → EReal :=
  fun p => if f p.1 ≠ ⊤ ∧ φ ((f p.1).toReal + p.2.1) ≠ ⊤ then
      φ ((f p.1).toReal + p.2.1) + infConv g ℓ (L p.1 + p.2.2) + h p.1
    else ⊤

/-- The identification `ℝ × Y* ≅ (ℝ ⊕ Y)*`, `(ξ*, y*) ↦ ((ξ, y) ↦ ξ ξ* + ⟨y, y*⟩)` (pairing
(2.1), p.5), by which the paper writes the dual variable of `F` as `(ξ*, y*) ∈ ℝ × Y*`
(Theorem 3.3, p.12). -/
noncomputable def dualPair {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (ξ' : ℝ)
    (y' : StrongDual ℝ Y) : StrongDual ℝ (ℝ × Y) :=
  ξ' • ContinuousLinearMap.fst ℝ ℝ Y + y'.comp (ContinuousLinearMap.snd ℝ ℝ Y)

end PertComp


