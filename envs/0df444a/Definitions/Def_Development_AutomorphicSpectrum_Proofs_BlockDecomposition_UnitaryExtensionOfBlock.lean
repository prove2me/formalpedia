-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryExtensionOfBlock
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryExtensionOfBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:21.652251+00:00
-- url     : https://prove2.me/theorems/53f6e093-ea31-4959-8f7c-3cd0b9aabe29
-- title:
--   Unitary Extension Of Block
-- statement:
--   Definitions and structural lemmas for Unitary Extension Of Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryExtensionOfBlock.lean

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
namespace GlobalTheory.CompanionTheory.WittFrame
abbrev FrameIdx (D m : ℕ) := Fin D ⊕ₗ (Fin m ⊕ₗ (Fin D)ᵒᵈ)
def frameEquiv (D m : ℕ) : FrameIdx D m ≃ Fin D ⊕ (Fin m ⊕ Fin D) :=
  ofLex.trans (Equiv.sumCongr (Equiv.refl _)
    (ofLex.trans (Equiv.sumCongr (Equiv.refl _) OrderDual.ofDual)))
end GlobalTheory.CompanionTheory.WittFrame


