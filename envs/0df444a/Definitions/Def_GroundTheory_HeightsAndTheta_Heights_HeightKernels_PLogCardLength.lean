-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:20.931726+00:00
-- url     : https://prove2.me/theorems/3a5dc044-0229-4099-a8b2-db5052688f05
-- title:
--   PLog Card Length
-- statement:
--   Definitions and structural lemmas for PLog Card Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
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
namespace logCardLength
open Module
variable (R : Type) [CommRing R]
def term (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) : ℝ :=
  ∑ᶠ (_ : m.IsMaximal), (locLen m N : ℝ) * Real.log (Nat.card (R ⧸ m))
def FinLoc (N : Type) [AddCommGroup N] [Module R N] : Prop :=
  ∀ (m : Ideal R) [m.IsPrime],
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N) ≠ ⊤
variable {R}
end logCardLength
end
end GroundTheory.Heights₂.Heights


