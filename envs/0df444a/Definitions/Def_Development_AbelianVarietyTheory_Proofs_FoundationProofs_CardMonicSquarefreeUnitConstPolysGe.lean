-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:37:07.492842+00:00
-- url     : https://prove2.me/theorems/b99448c2-aa72-40bd-9851-3702f71ba048
-- title:
--   Card Monic Squarefree Unit Const Polys Ge
-- statement:
--   Definitions and structural lemmas for Card Monic Squarefree Unit Const Polys Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardMonicSquarefreeUnitConstPolysGe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.SqCount
variable (g : ℕ) [Fact g.Prime]
noncomputable def monicSet (N : ℕ) : Finset (ZMod g)[X] :=
  Finset.univ.image fun c : Fin N → ZMod g => (X ^ N + ∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X])
variable {g}
end GlobalTheory.BadShare.SqCount


