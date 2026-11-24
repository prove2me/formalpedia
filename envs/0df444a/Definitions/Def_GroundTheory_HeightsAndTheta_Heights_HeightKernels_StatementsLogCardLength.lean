-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:55.30586+00:00
-- url     : https://prove2.me/theorems/760f7a42-1828-4d71-ac62-b86623b61b58
-- title:
--   Statements Log Card Length
-- statement:
--   Definitions and structural lemmas for Statements Log Card Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsLogCardLength.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
noncomputable section
open Classical in

def locLen {R : Type*} [CommRing R] (m : Ideal R) (N : Type*) [AddCommGroup N] [Module R N] : ℕ :=
  if h : m.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N)).toNat
  else 0
def LogCardLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [Finite N],
    Real.log (Nat.card N) =
      ∑ᶠ (m : Ideal R) (_ : m.IsMaximal), (locLen m N : ℝ) * Real.log (Nat.card (R ⧸ m))
end
end GroundTheory.Heights₂.Heights


