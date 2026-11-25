-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ContDiffOnIffLocalExtension
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ContDiffOnIffLocalExtension
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:38:08.841578+00:00
-- url     : https://prove2.me/theorems/a6b12730-c04e-4f56-8131-4aa02ded6f94
-- title:
--   Cont Diff On Iff Local Extension
-- statement:
--   Definitions and structural lemmas for Cont Diff On Iff Local Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ContDiffOnIffLocalExtension.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
namespace GlobalTheory.UnitaryRetraction
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Calculus
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X}
end Calculus
def cay (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 - X) * (1 + X)⁻¹
def skewPart (H X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℝ) • (X - H * Xᴴ * H)
variable {H : Matrix (Fin n) (Fin n) ℂ}
end GlobalTheory.UnitaryRetraction


