-- Prove2me | Definitions.Def_AronszajnRK_Sum_kernelFn
-- name    : AronszajnRK_Sum_kernelFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:30:46.926315+00:00
-- url     : https://prove2.me/theorems/a6a1341f-a88b-40b8-a9cf-4bb586696b75
-- title:
--   Scalar reproducing kernel $K(x,y)$ of a complex RKHS
-- statement:
--   Let $E$ be an arbitrary set and let $F$ be a class of complex-valued functions on $E$ forming a complex Hilbert space in which every point evaluation $f\mapsto f(y)$ is continuous. A function $K(x,y)$ on $E\times E$ is the **reproducing kernel** of $F$ if
--
--   1. for every $y\in E$, the function $K(\cdot,y)$ belongs to $F$;
--   2. (*reproducing property*) for every $y\in E$ and every $f\in F$,
--   $$f(y)=(f,\,K(\cdot,y)).$$
--
--   This definition names the scalar function $K:E\times E\to\mathbb C$ attached to such a space $F$, so that every statement of the mission can speak of "the kernel of $F$" and add or compare kernels pointwise.
--
--   **Formalization Note** Mathlib's class `RKHS ℂ H X ℂ` presents $F$ as a complex Hilbert space `H` with a continuous injective linear map into functions `X → ℂ`. Mathlib's `RKHS.kernel H` is operator-valued (values in `ℂ →L[ℂ] ℂ`); the scalar kernel is its value at $1$, i.e. $K(x,y)=K_y(x)$ where $K_y$ is the element `RKHS.kerFun H y 1`. Mathlib's inner product is conjugate-linear in the first argument, so the paper's $(f,K(\cdot,y))$ is `⟪kerFun H y 1, f⟫_ℂ`.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 343, §1, Definition (conditions 1 and 2)

import Mathlib

namespace AronszajnRK.Sum

/-- The scalar reproducing kernel `K(x, y)` of a complex Hilbert space `H` of functions on `X`
with a reproducing kernel (Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc.
68 (1950), §1, Definition, p. 343 (PDF 7)). Mathlib's `RKHS.kernel H` is operator-valued
(`ℂ →L[ℂ] ℂ`); Aronszajn's scalar `K(x, y)` is its value at `1`. By `RKHS.kerFun_apply`,
`K(·, y)` is the element `RKHS.kerFun H y 1` of `H`, and the reproducing property reads
`⟪RKHS.kerFun H y 1, f⟫_ℂ = f y` (`RKHS.kerFun_inner`). -/
noncomputable def kernelFn {X : Type*} (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] : X → X → ℂ :=
  fun x y => RKHS.kernel H x y 1

end AronszajnRK.Sum


