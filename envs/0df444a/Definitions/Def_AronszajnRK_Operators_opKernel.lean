-- Prove2me | Definitions.Def_AronszajnRK_Operators_opKernel
-- name    : AronszajnRK_Operators_opKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:49:04.324219+00:00
-- url     : https://prove2.me/theorems/241231bf-2fa1-40a8-ae26-1be346b7ea64
-- title:
--   Kernel $\Lambda(x,y) = L^*_x K(x,y)$ of a bounded operator on an RKHS
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$, and let $L$ be a bounded linear operator on $F$ with adjoint $L^*$, the operator for which $(Lf, g) = (f, L^* g)$. The **kernel of $L$** is the function of two points
--   $$
--   \Lambda(x, y) = L^*_x K(x, y),
--   $$
--   obtained by applying $L^*$ to $K(\cdot, y)$, an element of $F$, and evaluating the result at $x$. For each $y$, the function $x \mapsto \Lambda(x, y)$ therefore belongs to $F$, and the reproducing property gives the representation of $L$ by its kernel:
--   $$
--   Lf(y) = (f, \Lambda(\cdot, y)) \qquad \text{for every } f \in F,\ y \in E.
--   $$
--
--   Every bounded operator on $F$ is determined by its kernel, and the results of the mission translate properties of operators (adjoint, symmetry, positivity, bounds, limits) into properties of their kernels.
--
--   **Formalization Note.** For `L : H →L[ℂ] H`, `opKernel L x y` is `(adjoint L) (kerFun H y 1)` evaluated at `x`. Mathlib's inner product `⟪u, v⟫_ℂ` is conjugate-linear in `u`, so the paper's $(f, g)$ is `⟪g, f⟫_ℂ`, and the representation formula reads `L f y = ⟪(adjoint L) (kerFun H y 1), f⟫_ℂ`. On the one-point space with $K = 1$ and $L = c\,I$ the kernel is $\bar c$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 372, §11, Eq. (1) and (2)

import Mathlib

namespace AronszajnRK.Operators

/-- The kernel `Λ(x, y) = L*ₓ K(x, y)` of a bounded operator `L` on a complex reproducing
kernel Hilbert space `H` of functions `X → ℂ` (Aronszajn, *Theory of Reproducing Kernels*,
Trans. Amer. Math. Soc. 68 (1950), §11, Eq. (1), p. 372, PDF p. 36): for each `y`, the adjoint
`L*` is applied to the element `K(·, y) = RKHS.kerFun H y 1` of `H`, and the resulting element
of `H` is evaluated at `x`. For every `y` the function `x ↦ Λ(x, y)` thus belongs to `H`, and
`L f (y) = ⟪(adjoint L) (kerFun H y 1), f⟫_ℂ`, which is Aronszajn's §11, Eq. (2)
`Lf(y) = (f(x), Λ(x, y))` written in Mathlib's convention (Mathlib's inner product is
conjugate-linear in its first argument, Aronszajn's scalar product in its second). -/
noncomputable def opKernel {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) (x y : X) : ℂ :=
  (ContinuousLinearMap.adjoint L) (RKHS.kerFun H y 1) x

end AronszajnRK.Operators


