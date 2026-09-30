-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ExponentialPreimage
-- name    : WeierstrassEllipticZeta_ExponentialPreimage
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-25T03:16:47.040969+00:00
-- url     : https://prove2.me/theorems/dccf69f1-191a-4e56-a49a-4a4b1b43e312
-- title:
--   Exponential preimage of the actual subgroup equations
-- statement:
--   The inverse image in C³ of all bihomogeneous polynomial equations vanishing on an actual subgroup H in a compatible Model M, under the explicit entire exponential coordinates. This definition names a set. It does not assume that this set is additive or that its analytic identity component has the equations of H. Those are separate algebraic geometric obligations, and no field is added to Model.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, exponential map and Lemma A.1.

import Definitions.Def_WeierstrassEllipticZeta_SubgroupLinearization
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false
noncomputable section

namespace WeierstrassEllipticZeta.PhilipponApplication.Model
open PhilipponMultiplicity
variable {S : Fin 5 → ℂ → ℂ}

/-- The inverse image under the explicit exponential coordinates of the
projective closure of an actual subgroup. The definition does not assert that
this set is additive, nor that its analytic identity component is dense. -/
def exponentialPreimage (M : Model S) (H : AlgebraicSubgroup M.group) :
    Set (Fin 3 → ℂ) :=
  {v | ∀ (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ), Bihomogeneous Q m n →
    (∀ g ∈ H.carrier,
      M.group.ambient.eval (M.polynomial Q) (M.group.embedding g) = 0) →
    MvPolynomial.eval (exponentialCoordinates S v) Q = 0}

end WeierstrassEllipticZeta.PhilipponApplication.Model


