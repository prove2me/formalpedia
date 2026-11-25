-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivCocycleMemRangeCobOfPullbackMulP
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivCocycleMemRangeCobOfPullbackMulP
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:00.262332+00:00
-- url     : https://prove2.me/theorems/4fef1ebb-6232-4bc8-90dc-26306edf2d4b
-- title:
--   PDiv Cocycle Mem Range Cob Of Pullback Mul P
-- statement:
--   Definitions and structural lemmas for PDiv Cocycle Mem Range Cob Of Pullback Mul P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivCocycleMemRangeCobOfPullbackMulP.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulPEqOfTranslInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
end PDivGroup
end GlobalTheory


