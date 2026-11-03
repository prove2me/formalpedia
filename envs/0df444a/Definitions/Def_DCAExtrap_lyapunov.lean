-- Prove2me | Definitions.Def_DCAExtrap_lyapunov
-- name    : DCAExtrap_lyapunov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:38.882212+00:00
-- url     : https://prove2.me/theorems/bf5bd065-2367-4f6a-80e3-2d2aeb5ca619
-- title:
--   Auxiliary function $\Phi(x,y) = F(x) + \frac{(1+\delta)L}{2} D_\varphi(y,x)$
-- statement:
--   On pairs $(x,y)\in E\times E$ the auxiliary function of the global convergence analysis is
--
--   $$
--   \Phi(x,y) = F(x) + \frac{(1+\delta)L}{2}\,D_\varphi(y,x).
--   $$
--
--   Note the order $D_\varphi(y,x)$: the gradient of $\varphi$ is taken at $x$. Along a DCAe run, $\Phi(x^k,x^{k-1})=F(x^k)+\frac{(1+\delta)L}{2}D_\varphi(x^{k-1},x^k)$.
--
--   **Formalization Note** Pairs live in the Euclidean product `WithLp 2 (E × E)`, with $\|(x,y)\|^2=\|x\|^2+\|y\|^2$ and inner product the sum of the two inner products. $\Phi$ is `EReal`-valued.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, (24), p.8

import Mathlib
import Definitions.Def_DCAExtrap_bregman
import Definitions.Def_DCAExtrap_objF

namespace DCAExtrap

/-- **The auxiliary function Φ** (Phan–Le Thi, arXiv:2106.04743v1, (24), p.8):
`Φ(x, y) = F(x) + (1 + δ)L/2 · D_φ(y, x)` on pairs `(x, y) ∈ E × E`.

**Formalization Note.** Pairs live in `WithLp 2 (E × E)`, the Euclidean product, whose norm is
`‖(x, y)‖ = (‖x‖² + ‖y‖²)^{1/2}` and whose inner product is the sum of the two inner products
(Mathlib's plain `E × E` has the sup norm and no inner product). Note the argument order
`D_φ(y, x)`: the gradient of `φ` is taken at the first component `x`. `Φ` is `EReal`-valued
because `F` is. -/
noncomputable def lyapunov {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (g : E → EReal) (h : E → ℝ) (φ : E → ℝ) (L δ : ℝ)
    (z : WithLp 2 (E × E)) : EReal :=
  objF f g h z.fst + (((1 + δ) * L / 2 * bregman φ z.snd z.fst : ℝ) : EReal)

end DCAExtrap


