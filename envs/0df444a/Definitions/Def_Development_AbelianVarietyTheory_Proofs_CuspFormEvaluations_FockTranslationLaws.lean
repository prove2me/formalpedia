-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:55:56.894346+00:00
-- url     : https://prove2.me/theorems/9de230c2-6c4c-4f88-a3ae-7998397b1e8a
-- title:
--   Fock Translation Laws
-- statement:
--   Definitions and structural lemmas for Fock Translation Laws, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2
namespace FockTranslation
variable {ι : Type} [Fintype ι]
end FockTranslation
end GlobalTheory


