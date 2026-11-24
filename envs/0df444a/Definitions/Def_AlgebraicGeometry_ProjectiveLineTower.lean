-- Prove2me | Definitions.Def_AlgebraicGeometry_ProjectiveLineTower
-- name    : AlgebraicGeometry_ProjectiveLineTower
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-24T02:14:27.665095+00:00
-- url     : https://prove2.me/theorems/51bafa4d-07a6-4f92-a27e-3d446b91216c
-- title:
--   Relative powers of the projective line
-- statement:
--   The iterated fiber product of $n+1$ relative projective lines over a specified base.
-- source:
--   Stacks Project, Lemma 59.91.10, https://stacks.math.columbia.edu/tag/0A4F.

import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section

namespace PhilipponEtaleProjectiveLineTower

universe u

/-- The `(n+1)`-fold fiber product of relative projective lines,
formed as a tower of pullbacks of the projective-line projection. -/
def linePower {R : Type u} [CommRing R] {S : Scheme.{u}} (v : S ⟶ Spec (.of R)) :
    ℕ → Over S
  | 0 => Over.mk (pullback.fst v (ProjSpace.π R 1))
  | n + 1 =>
      let P := linePower v n
      Over.mk (pullback.fst (P.hom ≫ v) (ProjSpace.π R 1) ≫ P.hom)

end PhilipponEtaleProjectiveLineTower


