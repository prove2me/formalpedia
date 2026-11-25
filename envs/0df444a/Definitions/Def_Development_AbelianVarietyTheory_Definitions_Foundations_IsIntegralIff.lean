-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:52:05.53773+00:00
-- url     : https://prove2.me/theorems/d549f906-97c3-4b8d-8c40-0c347185f954
-- title:
--   Is Integral Iff
-- statement:
--   Definitions and structural lemmas for Is Integral Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
namespace GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
def stdLat (L : LocE F E) (n : ℕ) : Submodule L.O (Fin n → E) :=
  Submodule.span L.O (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → E))
end GlobalTheory.HL.Model


