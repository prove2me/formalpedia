-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPowOfFiniteField
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPowOfFiniteField
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:58.558845+00:00
-- url     : https://prove2.me/theorems/3105419e-69ab-4a73-b964-2affb915bee1
-- title:
--   Exists Pow Of Finite Field
-- statement:
--   Definitions and structural lemmas for Exists Pow Of Finite Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPowOfFiniteField.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace GlobalTheory.EmbFrob
open Polynomial
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
end GlobalTheory.EmbFrob


