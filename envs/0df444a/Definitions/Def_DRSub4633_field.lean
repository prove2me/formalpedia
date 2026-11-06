-- Prove2me | Definitions.Def_DRSub4633_field
-- name    : DRSub4633_field
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:09:35.921121+00:00
-- url     : https://prove2.me/theorems/e8de0ccd-6e6b-4925-a236-9b82d1238e60
-- title:
--   The comparison field $g(f,x)$
-- statement:
--   For $f$ and a state $x$ in the cube, the comparison field is
--   $$g(f,x)=d+\int_0^1\mathcal J(t)\,dt,$$
--   with blocks
--   $$\mathcal J_S(t)=\lambda(t)(1-a(t))V(t)+\kappa(t)(1-a(t))\nabla_SF(a(t),\mathbf 0_L)-U(t)\nu_t,\qquad \mathcal J_L(t)=[w(t)+\varpi(t)]\,g^L(t),$$
--   products with $1-a(t)$ coordinatewise. If $S$ is empty, its terms are absent.
--
--   This is the single vector that bounds every comparator in Theorem 4.1.
--
--   **Formalization Note** The integral is taken coordinatewise as an interval integral over $[0,1]$. The dummy coordinate's component is zero and is dropped. Gradients are within-cube derivatives `GeomDRSub.pd`.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (24), p.12

import Mathlib
import Definitions.Def_DRSub4633_chainD
import Definitions.Def_DRSub4633_sPar
import Definitions.Def_DRSub4633_lam
import Definitions.Def_DRSub4633_kappa
import Definitions.Def_DRSub4633_UWeight
import Definitions.Def_DRSub4633_wDens
import Definitions.Def_DRSub4633_varpiDens
import Definitions.Def_DRSub4633_aPath
import Definitions.Def_DRSub4633_Vgrad
import Definitions.Def_DRSub4633_nuInc
import Definitions.Def_DRSub4633_gLarge
import Definitions.Def_DRSub4633_resid
import Definitions.Def_DRSub4633_mergePt
import Definitions.Def_GeomDRSub_pd

namespace DRSub4633

/-- **The comparison field `g(f, x)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (24), p.12:
`g(f, x) = d + ∫_0^1 J(t) dt` with
`J_S(t) = λ(t)(1 − a(t))V(t) + κ(t)(1 − a(t))∇_S F(a(t), 0_L) − U(t)ν_t` and
`J_L(t) = [w(t) + ϖ(t)] g^L(t)` (products with `1 − a(t)` coordinatewise). "If `S` is empty, all its
vector terms are absent."

**Formalization Note.** The integral is taken coordinatewise, as an interval integral over `[0, 1]`
(for `f` continuously differentiable on the cube each integrand is bounded and piecewise continuous
in `t`, so this equals the vector integral). The dummy coordinate's component is zero and is
dropped. `∇_S F` is the within-cube partial derivative `GeomDRSub.pd` of `F`. The function is total
in `(f, x)`; only `x` in the cube is used. -/
noncomputable def field {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => chainD f x j + ∫ t in (0 : ℝ)..1,
    (if x j ≤ sPar then
      lam t * (1 - aPath x t j) * Vgrad f x t j
        + kappa t * (1 - aPath x t j) * GeomDRSub.pd (resid f x) j (mergePt x (aPath x t) 0)
        - UWeight t * nuInc f x t j
    else (wDens t + varpiDens t) * gLarge f x t j))

end DRSub4633


