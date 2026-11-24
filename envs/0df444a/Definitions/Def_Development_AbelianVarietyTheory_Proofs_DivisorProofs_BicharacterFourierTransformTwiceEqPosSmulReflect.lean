-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:14.926272+00:00
-- url     : https://prove2.me/theorems/54821093-26cb-4938-9e4d-abe24a960669
-- title:
--   Bicharacter Fourier Transform Twice Eq Pos Smul Reflect
-- statement:
--   Definitions and structural lemmas for Bicharacter Fourier Transform Twice Eq Pos Smul Reflect, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
noncomputable section
namespace GlobalTheory.KSp.FourInv
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}
theorem ne_zero (he : IsPair e) (x y : X) : e x y ≠ 0 := by
  intro h
  have h1 := he.norm x y
  rw [h, norm_zero] at h1
  exact zero_ne_one h1
theorem add_right (he : IsPair e) (x y y' : X) : e x (y + y') = e x y * e x y' := by
  rw [he.symm x (y + y'), he.add y y' x, he.symm y x, he.symm y' x]
theorem zero_right (he : IsPair e) (x : X) : e x 0 = 1 := by
  have h := add_right he x 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (ne_zero he x 0) (by rw [mul_one]; exact h.symm)
def ann (he : IsPair e) (L : Set X) : AddSubgroup X where
  carrier := {z | ∀ y ∈ L, e y z = 1}
  zero_mem' := fun y _ => zero_right he y
  add_mem' := fun {a b} ha hb y hy => by rw [add_right he, ha y hy, hb y hy, one_mul]
  neg_mem' := fun {a} ha y hy => by
    have h := add_right he y a (-a)
    rw [add_neg_cancel, zero_right he, ha y hy, one_mul] at h
    exact h.symm
variable [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
end GlobalTheory.KSp.FourInv
namespace GlobalTheory.KSp
end GlobalTheory.KSp
end


