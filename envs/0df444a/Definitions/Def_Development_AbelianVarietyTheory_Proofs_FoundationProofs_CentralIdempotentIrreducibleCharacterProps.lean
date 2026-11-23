-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:22.105483+00:00
-- url     : https://prove2.me/theorems/0c57e168-2af1-4e08-bebd-9e1d14c9b75d
-- title:
--   Central Idempotent Irreducible Character Props
-- statement:
--   Definitions and structural lemmas for Central Idempotent Irreducible Character Props, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralIdempotentIrreducibleCharacterProps.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.ZCalc
variable {G : Type} [Group G] [Fintype G]
end GlobalTheory.BadShare.ZCalc


