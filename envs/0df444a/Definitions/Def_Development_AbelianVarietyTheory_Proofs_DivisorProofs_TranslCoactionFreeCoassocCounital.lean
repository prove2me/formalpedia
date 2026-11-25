-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslCoactionFreeCoassocCounital
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslCoactionFreeCoassocCounital
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:39:08.058268+00:00
-- url     : https://prove2.me/theorems/9bb61368-c957-4782-b847-9d5779c4be4c
-- title:
--   Transl Coaction Free Coassoc Counital
-- statement:
--   Definitions and structural lemmas for Transl Coaction Free Coassoc Counital, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslCoactionFreeCoassocCounital.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
namespace GlobalTheory.TranslFree
variable {R A B : Type} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B] [Bialgebra R B]
  (f : A →ₐc[R] B)
end GlobalTheory.TranslFree


