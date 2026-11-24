-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevels
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevels
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:18:44.555214+00:00
-- url     : https://prove2.me/theorems/785a7cdf-a170-44d4-af07-94d4643f0ffc
-- title:
--   Is Full Symplectic Level Structure Unique Of Levels
-- statement:
--   Definitions and structural lemmas for Is Full Symplectic Level Structure Unique Of Levels, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullSymplecticLevelStructureUniqueOfLevels.lean

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
namespace GlobalTheory.FullLevel.Uniq
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
  {N : ℕ} {z : kˣ} {ev : D.La → Q}
end GlobalTheory.FullLevel.Uniq
namespace GlobalTheory.FullLevel
open Uniq
end GlobalTheory.FullLevel


