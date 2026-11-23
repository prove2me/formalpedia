-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:50.995752+00:00
-- url     : https://prove2.me/theorems/6765bcc5-2af3-4caa-9e1c-f013088d2eaa
-- title:
--   Trace Power Sum Mod Eq
-- statement:
--   Definitions and structural lemmas for Trace Power Sum Mod Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.TraceAeval
open Module
noncomputable def powMat {R : Type*} [CommRing R] (n : ℕ) (ψ : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ((X ^ ((j : ℕ) + 1)) %ₘ ψ).coeff i
end GlobalTheory.TraceAeval


