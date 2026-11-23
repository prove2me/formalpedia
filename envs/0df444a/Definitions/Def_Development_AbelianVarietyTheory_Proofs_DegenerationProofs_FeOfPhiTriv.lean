-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:27.232349+00:00
-- url     : https://prove2.me/theorems/5f9dcff2-e122-4dd7-9504-fa2e2be89b68
-- title:
--   Fe Of Phi Triv
-- statement:
--   Definitions and structural lemmas for Fe Of Phi Triv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FeOfPhiTriv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
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
namespace GlobalTheory.Ex.PhiOp
section Cube
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h
end Cube
variable {O : Type} [CommRing O] (N : NumD O)
end GlobalTheory.Ex.PhiOp


