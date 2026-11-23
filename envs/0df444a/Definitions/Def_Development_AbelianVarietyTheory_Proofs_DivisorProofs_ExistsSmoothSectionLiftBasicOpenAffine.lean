-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSectionLiftBasicOpenAffine
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSectionLiftBasicOpenAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:18.688811+00:00
-- url     : https://prove2.me/theorems/0fd419d9-0294-4742-886d-90e69f2e7e5e
-- title:
--   Exists Smooth Section Lift Basic Open Affine
-- statement:
--   Definitions and structural lemmas for Exists Smooth Section Lift Basic Open Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSectionLiftBasicOpenAffine.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_FiniteLocalLifts_SmLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SecLift
variable {R R₀ : Type} [CommRing R] [CommRing R₀]
end GlobalTheory.SecLift


