-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomB
-- name    : Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:58.914838+00:00
-- url     : https://prove2.me/theorems/a5a96a5e-1185-46f8-8f88-58f87f1071f8
-- title:
--   Mom B
-- statement:
--   Definitions and structural lemmas for Mom B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/FormalDegree/FormalDegreeHilbert/MomB.lean

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
namespace PositivityTheory.RgFd
def MomA : Prop :=
  ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (ν : Measure Ω) (ν' : Measure Ω') (U : Ω → ℝ) (U' : Ω' → ℝ)
    (t0 : ℕ), Measurable U → Measurable U' → (∀ x, 0 ≤ U x ∧ U x ≤ 1) → (∀ y, 0 ≤ U' y ∧ U' y ≤ 1) → 1 ≤ t0 →
    (∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (U x ^ (j * t0)) ∂ν = ∫⁻ y, ENNReal.ofReal (U' y ^ (j * t0)) ∂ν') →
    (∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (U x ^ (j * t0)) ∂ν ≠ ⊤) →
    ν {x | 0 < U x} = ν' {y | 0 < U' y}
def MomB : Prop :=
  ∀ (I : Type) [Fintype I] (α β : I → ℝ) (c : ℝ), (∀ i, 0 < α i) → (∀ i, 0 ≤ β i) → 0 ≤ c →
    ∃ (ν' : Measure (I → ℝ)) (U' : (I → ℝ) → ℝ), Measurable U' ∧ (∀ y, 0 < U' y ∧ U' y ≤ 1) ∧
      ∀ t : ℕ, ∫⁻ y, ENNReal.ofReal (U' y ^ t) ∂ν' = ENNReal.ofReal (c / ∏ i, (α i + t * β i))
def MomW : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → ENNReal) (U : Ω → ℝ) (I : Type) [Fintype I] (α β : I → ℝ)
    (c : ℝ) (t0 : ℕ), Measurable h → Measurable U → (∀ x, 0 ≤ U x ∧ U x ≤ 1) → (∀ i, 0 < α i) → (∀ i, 0 ≤ β i) → 0 ≤ c →
    (∀ t : ℕ, t0 ≤ t → ∫⁻ x, h x * ENNReal.ofReal (U x ^ t) ∂P = ENNReal.ofReal (c / ∏ i, (α i + t * β i))) →
    ∫⁻ x in {x | 0 < U x}, h x ∂P = ENNReal.ofReal (c / ∏ i, α i)
end PositivityTheory.RgFd


