-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsSimpleModuleOfFinrankEnd
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsSimpleModuleOfFinrankEnd
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:13.23773+00:00
-- url     : https://prove2.me/theorems/7fe2fec8-d705-4d7b-8f4e-adfd03e80e5c
-- title:
--   Is Simple Module Of Finrank End
-- statement:
--   Definitions and structural lemmas for Is Simple Module Of Finrank End, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsSimpleModuleOfFinrankEnd.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_IrreducibleCharacters_CuspidalCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CuspCharCompare
open CuspElliptic GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
open scoped MonoidAlgebra
section Group
variable {G : Type} [Group G]
variable [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
end Group
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
end GlobalTheory.CuspCharCompare


