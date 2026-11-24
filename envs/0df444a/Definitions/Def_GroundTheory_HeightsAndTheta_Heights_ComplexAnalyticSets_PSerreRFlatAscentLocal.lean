-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscentLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscentLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:48.800845+00:00
-- url     : https://prove2.me/theorems/67f2488a-9088-411a-8af3-469c1fc64d87
-- title:
--   PSerre RFlat Ascent Local
-- statement:
--   Definitions and structural lemmas for PSerre RFlat Ascent Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSerreRFlatAscentLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing
section FlatLocal
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]
end FlatLocal
section Localized
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime]
end Localized
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


