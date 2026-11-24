-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:18.897566+00:00
-- url     : https://prove2.me/theorems/9d8b7ec3-1f0d-4266-81ee-e4ecf148287f
-- title:
--   Witt Extension Hermitian Frames
-- statement:
--   Definitions and structural lemmas for Witt Extension Hermitian Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.SgAlg.WittField
variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
def qr (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (u : Fin n → E) (l : E) : Matrix (Fin n) (Fin n) E :=
  1 - l • vecMulVec u ((fun i => σ (u i)) ᵥ* J)
end GlobalTheory.SgAlg.WittField


