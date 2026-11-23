-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
-- name    : Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:03.810641+00:00
-- url     : https://prove2.me/theorems/febceaf9-635c-4173-8b8a-2e396f866a5e
-- title:
--   Two Mul Pow Four Dvd Card General Linear Group
-- statement:
--   Definitions and structural lemmas for Two Mul Pow Four Dvd Card General Linear Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TwoMulPowFourDvdCardGeneralLinearGroup.lean

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
namespace GlobalTheory
def transvectionUnit {R : Type} [CommRing R] {r : ℕ} {i j : Fin r} (h : i ≠ j) : GL (Fin r) R :=
  ⟨transvection i j (1 : R), transvection i j (-1 : R),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩
end GlobalTheory


