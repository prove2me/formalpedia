-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:09.793407+00:00
-- url     : https://prove2.me/theorems/b7fc195f-0644-4125-ab0d-a03f765d4b65
-- title:
--   POrbit Degree
-- statement:
--   Definitions and structural lemmas for POrbit Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
def homogForm (g : Polynomial ℤ) (p q : Coord n) : MvPolynomial (Coord n) ℤ :=
  ∑ j ∈ Finset.range (g.natDegree + 1), C (g.coeff j) * X p ^ j * X q ^ (g.natDegree - j)
end
end GroundTheory.Heights₂.Heights


