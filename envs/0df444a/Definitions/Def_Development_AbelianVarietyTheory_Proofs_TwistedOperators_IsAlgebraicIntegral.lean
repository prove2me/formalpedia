-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsAlgebraicIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsAlgebraicIntegral
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:46:29.701986+00:00
-- url     : https://prove2.me/theorems/9c684fbc-2c64-446c-9f06-ae2c2aefd2e1
-- title:
--   Is Algebraic Integral
-- statement:
--   Definitions and structural lemmas for Is Algebraic Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsAlgebraicIntegral.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace GlobalTheory.HaarAlg
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def avg (F : K → Matrix ι ι ℂ) : Matrix ι ι ℂ := Matrix.of fun a b => ∫ g, F g a b ∂κ
variable [κ.IsMulLeftInvariant]
end GlobalTheory.HaarAlg


