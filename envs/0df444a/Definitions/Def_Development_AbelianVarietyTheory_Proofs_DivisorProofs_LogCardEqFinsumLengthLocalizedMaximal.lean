-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:05.976104+00:00
-- url     : https://prove2.me/theorems/1c3b2f1f-9d56-43e2-8e4b-be587d5df16b
-- title:
--   Log Card Eq Finsum Length Localized Maximal
-- statement:
--   Definitions and structural lemmas for Log Card Eq Finsum Length Localized Maximal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardEqFinsumLengthLocalizedMaximal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CardLength
variable {R : Type} [CommRing R]
noncomputable def lenAt (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q] : ℕ∞ :=
  Module.length (Localization.AtPrime w) (LocalizedModule w.primeCompl Q)
end GlobalTheory.CardLength


