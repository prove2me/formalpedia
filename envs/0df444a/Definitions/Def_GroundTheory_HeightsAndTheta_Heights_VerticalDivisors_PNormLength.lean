-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormLength
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:04.795158+00:00
-- url     : https://prove2.me/theorems/3174439c-817f-45f7-99ed-3cff842774ad
-- title:
--   PNorm Length
-- statement:
--   Definitions and structural lemmas for PNorm Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormLength.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open Module
noncomputable section
section NormLength
variable {R B : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B]
end NormLength
end
end GroundTheory.Heights₂.Heights.Vertical


