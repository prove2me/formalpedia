-- Prove2me | Definitions.Def_FracPSG_Abstract_Supplement_Merit
-- name    : FracPSG_Abstract_Supplement_Merit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:57:05.023855+00:00
-- url     : https://prove2.me/theorems/5df43149-4718-4d30-ad04-5c9af5ab46cd
-- title:
--   The merit function $h(x,y)=f(x)/g(x)+\iota_S(x)+c\|x-y\|^2$ of Theorem 5.5 (p. 18)
-- statement:
--   For the fractional program $\min_{x\in S} f(x)/g(x)$ and a constant $c\in\mathbb R$, the **merit function** of Theorem 5.5 is
--   $$h(x,y):=\frac{f(x)}{g(x)}+\iota_S(x)+c\|x-y\|^2,\qquad (x,y)\in\mathcal H\times\mathcal H,$$
--   with the value $+\infty$ unless $x\in S\cap\operatorname{dom} f$. The product $\mathcal H\times\mathcal H$ carries the Hilbert norm $\|(x,y)\|^2=\|x\|^2+\|y\|^2$. The file also names the point $(x,y)$ of that product.
--
--   Evaluated along the iterates of Algorithm 1 at $(x_{n+1},x_n)$, with $c$ the constant of (14), $h$ is the Lyapunov function that decreases by $\alpha\|x_{n+1}-x_n\|^2$ per step; its KL property is the hypothesis of Theorem 5.5.
--
--   **Formalization Note** The product is `WithLp 2 (H × H)`, an inner-product space, so the published KL definitions apply to $h$. The quotient is the one of `FracPSG.Abstract.Supplement.Stationary` ($+\infty$ where $f=+\infty$). Adding the real number $c\|x-y\|^2$ to $+\infty$ gives $+\infty$ in `EReal`.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 18, Theorem 5.5 (definition of h)

import Mathlib
import Definitions.Def_FracPSG_Subseq_Basic
import Definitions.Def_FracPSG_Abstract_Supplement_Stationary

namespace FracPSG.Abstract.Supplement

open FracPSG.Subseq

/-- The merit function of Theorem 5.5 (p. 18) on `H × H` with the Hilbert (ℓ²) product norm:
`h(x, y) = f(x)/g(x) + ι_S(x) + c‖x − y‖²`, equal to `+∞` unless `x ∈ S ∩ dom f`. -/
noncomputable def merit {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N)))
    (f : EuclideanSpace ℝ (Fin N) → EReal) (g : EuclideanSpace ℝ (Fin N) → ℝ) (c : ℝ) :
    WithLp 2 (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) → EReal :=
  fun p => addInd (quotient f g) S (WithLp.ofLp p).1 +
    ((c * ‖(WithLp.ofLp p).1 - (WithLp.ofLp p).2‖ ^ 2 : ℝ) : EReal)

/-- The pair `(x, y)` as a point of the Hilbert product `H × H`. -/
def pair {N : ℕ} (x y : EuclideanSpace ℝ (Fin N)) :
    WithLp 2 (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) :=
  WithLp.toLp 2 (x, y)

end FracPSG.Abstract.Supplement


