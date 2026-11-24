-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:28.983273+00:00
-- url     : https://prove2.me/theorems/73b9aa95-9da3-498b-a78a-4d5bcbc2caea
-- title:
--   Exists Unique Maximal Above Place
-- statement:
--   Definitions and structural lemmas for Exists Unique Maximal Above Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueMaximalAbovePlace.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
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
namespace GlobalTheory.OnePrime
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
end GlobalTheory.OnePrime


