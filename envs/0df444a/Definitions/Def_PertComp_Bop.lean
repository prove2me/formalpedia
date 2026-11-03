-- Prove2me | Definitions.Def_PertComp_Bop
-- name    : PertComp_Bop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:05.208266+00:00
-- url     : https://prove2.me/theorems/29c45e2a-1413-4e57-a341-262a9032b19d
-- title:
--   The operator $\boldsymbol B$ of (3.6)
-- statement:
--   In the setting of Problem 1.1, $\boldsymbol B\colon X\oplus\mathbb R\to 2^{X^*\oplus\mathbb R}$ is
--   $$\boldsymbol B(x,\xi^*)=\Big(\big(L^*\circ((\partial g)\,\Box\,(\partial\ell))\circ L\big)(x)+\partial h(x)\Big)\times\{0\},$$
--   where $\Box$ is the parallel sum (2.3) and $(L^*\circ A\circ L)(x)=\{y^*\circ L : y^*\in A(Lx)\}$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Proposition 3.2, (3.6), p.11

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_PertComp_parSum

namespace PertComp

open Pointwise

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, Proposition 3.2, (3.6), p.11: the operator
`𝑩 : X ⊕ ℝ → 2^{X* ⊕ ℝ}`,
`𝑩(x, ξ*) = ((L* ∘ ((∂g) □ (∂ℓ)) ∘ L)(x) + ∂h(x)) × {0}`.

**Formalization Note.** `(L* ∘ A ∘ L)(x) = {y* ∘ L | y* ∈ A(Lx)}`; `□` is the parallel sum
(2.3) (`parSum`); `+` is the pointwise sum of sets. -/
def Bop {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g ℓ : Y → EReal) (L : X →L[ℝ] Y)
    (h : X → EReal) (p : X × ℝ) : Set (StrongDual ℝ X × ℝ) :=
  ((fun y' : StrongDual ℝ Y => y'.comp L) ''
      parSum (RockafellarMaxMono.Shared.subdiff g) (RockafellarMaxMono.Shared.subdiff ℓ) (L p.1) +
    RockafellarMaxMono.Shared.subdiff h p.1) ×ˢ {(0 : ℝ)}

end PertComp


