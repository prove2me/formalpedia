-- Prove2me | Definitions.Def_ScutaruFid_gaussKernel
-- name    : ScutaruFid_gaussKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:07.708518+00:00
-- url     : https://prove2.me/theorems/75fa7309-a21f-4262-874d-abf5b7892821
-- title:
--   Gaussian kernel $\exp[-(ax^2+dy^2+2bxy)+lx+ky+g]$
-- statement:
--   For complex parameters $a,b,d,l,k,g$, the **Gaussian kernel** is the function of $x,y\in\mathbb R$
--
--   $$
--   \langle x|\rho|y\rangle=\exp\big[-(ax^2+dy^2+2bxy)+lx+ky+g\big].
--   $$
--
--   By the paper (p.1), the most general Gaussian density operator of a single mode is the integral operator with such a kernel; the oscillator semigroup is the semigroup of these integral operators.
--
--   **Formalization Note** `gaussKernel a b d l k g x y`, in this argument order. No condition is imposed on the parameters; the conditions under which the kernel is a density operator are the theorem `density_kernel_conditions`.
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eq. (3), p.1

import Mathlib

namespace ScutaruFid

/-- **Gaussian kernel**, eq. (3). Scutaru, arXiv:quant-ph/9708013v1, eq. (3), p.1:
"<x|ρ|y> = exp[−(ax² + dy² + 2bxy) + lx + ky + g]".

`gaussKernel a b d l k g x y = exp(−(a x² + d y² + 2 b x y) + l x + k y + g)` for complex
parameters `a, b, d, l, k, g` and real `x, y`.

**Formalization Note** The argument order is `a b d l k g` (quadratic coefficients `a` of `x²`,
`b` of `2xy`, `d` of `y²`; linear coefficients `l` of `x`, `k` of `y`; constant `g`). All
parameters are complex, as on the page; the conditions that make the kernel a density operator
are theorems of the mission (`density_kernel_conditions`), not part of the definition. -/
noncomputable def gaussKernel (a b d l k g : ℂ) (x y : ℝ) : ℂ :=
  Complex.exp (-(a * (x : ℂ) ^ 2 + d * (y : ℂ) ^ 2 + 2 * b * (x : ℂ) * (y : ℂ)) + l * (x : ℂ) +
    k * (y : ℂ) + g)

end ScutaruFid


