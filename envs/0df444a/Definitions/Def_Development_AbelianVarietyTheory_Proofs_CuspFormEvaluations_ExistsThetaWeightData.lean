-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaWeightData
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaWeightData
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:16:08.865317+00:00
-- url     : https://prove2.me/theorems/1b9fe6ea-459c-449e-b317-fd1367d17fa2
-- title:
--   Exists Theta Weight Data
-- statement:
--   Definitions and structural lemmas for Exists Theta Weight Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsThetaWeightData.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.ThetaWeight
open Finset
variable {ι : Type*} [Fintype ι]
def size (m : ℤ) (G : (ι → ℤ) × ℤ) : ℤ := ∑ i, |G.1 i| + m * G.2 + 1
end GlobalTheory.ThetaWeight


