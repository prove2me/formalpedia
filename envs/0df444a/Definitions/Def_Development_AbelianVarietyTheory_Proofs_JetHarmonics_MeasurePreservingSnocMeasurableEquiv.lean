-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeasurePreservingSnocMeasurableEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeasurePreservingSnocMeasurableEquiv
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:09:37.817484+00:00
-- url     : https://prove2.me/theorems/d97e71d8-6b38-561b-b953-d7de87934633
-- title:
--   Measure Preserving Snoc Measurable Equiv
-- statement:
--   Definitions and structural lemmas for Measure Preserving Snoc Measurable Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MeasurePreservingSnocMeasurableEquiv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace GlobalTheory
noncomputable def snocMeasurableEquiv (n : ℕ) : ((Fin n → ℂ) × ℂ) ≃ᵐ (Fin (n + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n)).symm
end GlobalTheory


