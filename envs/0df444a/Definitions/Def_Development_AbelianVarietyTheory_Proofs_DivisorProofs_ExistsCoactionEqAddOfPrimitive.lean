-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoactionEqAddOfPrimitive
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoactionEqAddOfPrimitive
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:38:57.848239+00:00
-- url     : https://prove2.me/theorems/6d264ab7-9d8f-4302-8626-211cba7caed8
-- title:
--   Exists Coaction Eq Add Of Primitive
-- statement:
--   Definitions and structural lemmas for Exists Coaction Eq Add Of Primitive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoactionEqAddOfPrimitive.lean

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
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
namespace GlobalTheory.HopfQuot
section
variable {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
end
end GlobalTheory.HopfQuot


