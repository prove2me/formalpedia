-- Prove2me | Definitions.Def_AronszajnRK_Product_kernelFn
-- name    : AronszajnRK_Product_kernelFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:34:00.346541+00:00
-- url     : https://prove2.me/theorems/b20a0772-a00d-4194-ad0c-03829218b0a8
-- title:
--   Scalar reproducing kernel $K(x,y)$ of a complex RKHS
-- statement:
--   Let $X$ be an arbitrary set and let $H$ be a complex Hilbert space of functions $f : X \to \mathbb{C}$ in which every point evaluation $f \mapsto f(y)$ is continuous (a reproducing kernel Hilbert space). Its **reproducing kernel** is the function $K : X \times X \to \mathbb{C}$ such that, for every $y \in X$, the function $K(\cdot, y)$ belongs to $H$ and
--
--   $$
--   f(y) = (f, K(\cdot, y)) \qquad \text{for every } f \in H,
--   $$
--
--   where $(f, g)$ is linear in $f$ and conjugate-linear in $g$ (Aronszajn's convention).
--
--   This is the kernel $K$ of every statement of the mission: $K_1$, $K_2$ for the two given classes, $K'$ for the direct product, and $K_1 K_2$ for the product kernel.
--
--   **Formalization Note** Mathlib's `RKHS.kernel H x y` is a continuous linear operator $\mathbb{C} \to \mathbb{C}$; the scalar $K(x,y)$ is its value at $1$. With this choice $K(\cdot, y)$ is Mathlib's `kerFun H y 1`, and $f(y) = \langle K(\cdot,y), f\rangle$ in Mathlib's inner product, which is conjugate-linear in the first slot.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 343, §1, conditions 1 and 2

import Mathlib

namespace AronszajnRK.Product

/-- The scalar reproducing kernel `K(x, y)` of a complex RKHS `H` of `ℂ`-valued functions on `X`
(N. Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §1, p. 343,
PDF p. 7, conditions 1 and 2). Mathlib's `RKHS.kernel H x y` is an operator `ℂ →L[ℂ] ℂ`;
Aronszajn's number `K(x, y)` is its value at `1`. By `RKHS.kerFun_apply`,
`kerFun H y 1 x = kernelFn H x y`, so `K(·, y)` is the element `kerFun H y 1` of `H`. -/
noncomputable def kernelFn (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {X : Type*} [RKHS ℂ H X ℂ] (x y : X) : ℂ :=
  RKHS.kernel H x y 1

end AronszajnRK.Product


