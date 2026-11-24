-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitArchSum
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitArchSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:23.761901+00:00
-- url     : https://prove2.me/theorems/4e176a38-5c4b-4b30-b495-87375b41b454
-- title:
--   POrbit Arch Sum
-- statement:
--   Definitions and structural lemmas for POrbit Arch Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitArchSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitArchSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
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
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
end GroundTheory.Heights₂.Heights


