-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralContinuousMultilinearMapPiMeasure
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralContinuousMultilinearMapPiMeasure
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T06:00:42.16036+00:00
-- url     : https://prove2.me/theorems/d91913aa-900b-448c-a793-41a4138f47c9
-- title:
--   Integral Continuous Multilinear Map Pi Measure
-- statement:
--   Definitions and structural lemmas for Integral Continuous Multilinear Map Pi Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralContinuousMultilinearMapPiMeasure.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace GlobalTheory.MultilinFubini
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
  {E : ι → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
def vecOn (g : ∀ i, X i → E i) (s : Finset ι) (m : ∀ i, E i) (x : ∀ i : s, X i) : ∀ i, E i :=
  fun i => if h : i ∈ s then g i (x ⟨i, h⟩) else m i
end GlobalTheory.MultilinFubini


