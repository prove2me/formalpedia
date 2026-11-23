-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:47.53093+00:00
-- url     : https://prove2.me/theorems/0605020a-13d5-4741-9cec-4cf6ebf70e54
-- title:
--   Cub NSucc
-- statement:
--   Definitions and structural lemmas for Cub NSucc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CubNSucc.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace GlobalTheory.CubeBalance
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
end GlobalTheory.CubeBalance


