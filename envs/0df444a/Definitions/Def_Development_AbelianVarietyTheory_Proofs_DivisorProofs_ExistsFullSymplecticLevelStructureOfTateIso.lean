-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIso
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIso
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:03.513043+00:00
-- url     : https://prove2.me/theorems/f3366b49-0be3-46b0-901c-9086ed927bd6
-- title:
--   Exists Full Symplectic Level Structure Of Tate Iso
-- statement:
--   Definitions and structural lemmas for Exists Full Symplectic Level Structure Of Tate Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFullSymplecticLevelStructureOfTateIso.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FullLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
end GlobalTheory.FullLevel


