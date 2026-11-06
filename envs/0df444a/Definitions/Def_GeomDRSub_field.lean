-- Prove2me | Definitions.Def_GeomDRSub_field
-- name    : GeomDRSub_field
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:39.040751+00:00
-- url     : https://prove2.me/theorems/e9279324-9929-4adf-9ace-e422e1176f8e
-- title:
--   The field $g_\zeta(f,x)$
-- statement:
--   For an objective $f$ and a state $x$, with $p=h_\zeta(x)$ and the path points $\ell_{i,s}$, $u_{i,s}$, let
--   $$
--   A_i=\int_0^1\partial_i f(\ell_{i,s})\,ds,\qquad C_i=\int_0^1\partial_i f(u_{i,s})\,ds .
--   $$
--   The **field** is the vector with coordinates
--   $$
--   [g_\zeta(f,x)]_i=(1-p_i)A_i+p_iC_i\qquad(i\in[d]).
--   $$
--   It averages partial derivatives along the two coordinate paths; it is not the gradient of $f$. It is the vector passed to the linear online learner.
--
--   **Formalization Note** Partial derivatives are taken within the cube (Definition 3.1's boundary convention).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 4.1, p.10, Eq. (15)

import Mathlib
import Definitions.Def_GeomDRSub_pd
import Definitions.Def_GeomDRSub_lowerPt
import Definitions.Def_GeomDRSub_upperPt

namespace GeomDRSub

/-- **The field `g_ζ(f, x)`** of Eq. (15). Aggarwal–Lu, arXiv:2610.00545, Section 4.1, p.10:
"`Aᵢ = ∫₀¹ ∂ᵢf(ℓ_{i,s}) ds`, `Cᵢ = ∫₀¹ ∂ᵢf(u_{i,s}) ds`, `[g_ζ(f, x)]ᵢ = (1 − pᵢ)Aᵢ + pᵢCᵢ`
`(i ∈ [d])`", with `p = h_ζ(x)` and the lower and upper path points `ℓ_{i,s}`, `u_{i,s}` of (14).

**Formalization Note.** The partial derivatives are the within-cube derivatives `pd` (boundary
convention of Definition 3.1); the integrals are interval integrals over `s ∈ [0,1]`. -/
noncomputable def field {d : ℕ} (ζ : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i =>
    (1 - hAct ζ x i) * (∫ s in (0 : ℝ)..1, pd f i (lowerPt ζ x i s)) +
      hAct ζ x i * (∫ s in (0 : ℝ)..1, pd f i (upperPt ζ x i s)))

end GeomDRSub


