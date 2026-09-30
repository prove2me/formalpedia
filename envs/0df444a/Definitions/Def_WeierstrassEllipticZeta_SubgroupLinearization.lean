-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_SubgroupLinearization
-- name    : WeierstrassEllipticZeta_SubgroupLinearization
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-25T02:01:57.800813+00:00
-- url     : https://prove2.me/theorems/f24a05f7-0e7d-48be-9452-5a3cd892d016
-- title:
--   Linear exponential equation sets in the Weierstrass model
-- statement:
--   The explicit entire coordinates of the exponential map send v in C³ to [1,v₀; S₀(v₁),S₁(v₁),S₂(v₁),S₃(v₁)+v₂S₀(v₁),S₄(v₁)+v₂S₂(v₁)]. A subgroup has linear exponential equations when its bihomogeneous equations agree with those of the image of some complex vector subspace under this map. The predicate contains no classification, degree or multiplicity conclusion. It does not assert that an actual connected algebraic subgroup satisfies the predicate; that is a separate open theorem.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, exponential coordinates and Lemma A.1.

import Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases

set_option autoImplicit false
noncomputable section
namespace WeierstrassEllipticZeta.PhilipponApplication

/-- Entire homogeneous coordinates of the exponential map in Appendix A. -/
def exponentialCoordinates (S : Fin 5 → ℂ → ℂ) (v : Fin 3 → ℂ) : Fin 7 → ℂ :=
  ![1, v 0, S 0 (v 1), S 1 (v 1), S 2 (v 1),
    S 3 (v 1) + v 2 * S 0 (v 1), S 4 (v 1) + v 2 * S 2 (v 1)]

/-- Equality of homogeneous equations with the exponential image of some
complex vector subspace. No subgroup classification or degree bound is included. -/
def Model.HasLinearSubgroupEquations {S : Fin 5 → ℂ → ℂ} (M : Model S)
    (H : PhilipponMultiplicity.AlgebraicSubgroup M.group) : Prop :=
  ∃ V : Submodule ℂ (Fin 3 → ℂ),
    M.HasParametricEquations H (fun v : V => exponentialCoordinates S v.val)

end WeierstrassEllipticZeta.PhilipponApplication


