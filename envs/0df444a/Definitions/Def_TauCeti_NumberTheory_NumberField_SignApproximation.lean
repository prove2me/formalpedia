-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_SignApproximation
-- name    : TauCeti_NumberTheory_NumberField_SignApproximation
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:50:56.904341+00:00
-- url     : https://prove2.me/theorems/73c96f87-2696-4934-bda8-8f0a43faf4b9
-- title:
--   Prescribing the signs of a number field element at the real places
-- statement:
--   For a number field, signs can be prescribed at its real places using local targets of absolute value one. An approximation within distance one preserves each prescribed real sign and ensures nonvanishing. These facts connect weak approximation with positivity conditions.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/SignApproximation.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/SignApproximation.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Prescribing the signs of a number field element at the real places

Weak approximation says that a number field `K` is dense in the product of its completions at the
infinite places; Mathlib records the diagonal form of this,
`NumberField.InfinitePlace.denseRange_algebraMap_pi`, on the product of the copies of `K` carrying
the topology of each infinite place. This file turns that topological statement into the
arithmetic one it is used for: an element of `K` may be prescribed, independently at each real
place, to be positive or negative there.

The passage is the usual one. Approximating the tuple whose entry at a place is `1` or `-1` to
within `1` forces the sign of each real embedding of the approximating element, because a real
number within distance `1` of `±1` has the sign of `±1`; the same estimate at any one place, real
or complex, keeps the element away from `0`.

## Main results

* `NumberField.exists_forall_infinitePlace_sub_lt`: weak approximation at the infinite
  places in `ε`-`δ` form, with targets in `K` measured by the places themselves.
* `NumberField.exists_forall_apply_eq_one_and_embedding_of_isReal_eq`: the family of targets that
  such an approximation is aimed at, of absolute value one at every infinite place and of
  prescribed sign at every real place.
* `NumberField.mul_pos_of_infinitePlace_sub_lt`: an element within `1` of a target of absolute
  value one at a real place has the sign of that target there.
* `NumberField.ne_zero_of_infinitePlace_sub_lt`: an element within `1` of a target of absolute
  value one at any infinite place is nonzero.
* `NumberField.exists_ne_zero_forall_isReal_pos`: a nonzero element of `K` whose real
  embeddings have prescribed signs.
* `NumberField.exists_ne_zero_neg_iff_mem`: the same statement with the prescription given
  as the set of real places at which the element is to be negative.

## References

The weak approximation theorem for pairwise inequivalent absolute values is Artin--Whaples; see
E. Artin and G. Whaples, *Axiomatic characterization of fields by the product formula for
valuations*, Bull. Amer. Math. Soc. **51** (1945), and, for the number field statement,
J. W. S. Cassels and A. Fröhlich, *Algebraic Number Theory*, Chapter II.
-/

 section

open NumberField NumberField.InfinitePlace

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]



omit [NumberField K] in
/-- **A family of targets of absolute value one with prescribed signs.**  For any prescribed sign
at each real place of a number field there is a family `b`, one element of `K` for each infinite
place, whose entry at `v` has absolute value one at `v` and whose entry at a real place `w` has
there exactly the prescribed sign.

This is the family that weak approximation at the infinite places is aimed at: absolute value one
keeps an approximation of it away from `0`, and
`NumberField.mul_pos_of_infinitePlace_sub_lt` turns the approximation into a sign prescription. -/
theorem exists_forall_apply_eq_one_and_embedding_of_isReal_eq
    (s : {w : InfinitePlace K // w.IsReal} → ℤˣ) :
    ∃ b : InfinitePlace K → K, (∀ v : InfinitePlace K, v (b v) = 1) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        embedding_of_isReal w.2 (b w.1) = ((s w : ℤ) : ℝ) := by
  classical
  refine ⟨fun v => if h : v.IsReal then ((s ⟨v, h⟩ : ℤ) : K) else 1, fun v => ?_, fun w => ?_⟩
  · dsimp only
    by_cases h : v.IsReal
    · rw [dif_pos h]
      rcases Int.units_eq_one_or (s ⟨v, h⟩) with hs | hs <;> rw [hs]
      · simp
      · rw [coe_apply]
        simp
    · rw [dif_neg h, map_one]
  · dsimp only
    rw [dif_pos w.2, Subtype.coe_eta, map_intCast]

omit [NumberField K] in
/-- **An approximation of a target of absolute value one has the sign of that target.**  At a real
place `w`, an element `x` within `1` of a target `y` with `w y = 1` has the same sign as `y` under
the real embedding at `w`.

Together with `NumberField.exists_forall_apply_eq_one_and_embedding_of_isReal_eq` this is the whole
archimedean content of a sign prescription: everything else is the approximation itself. -/
theorem mul_pos_of_infinitePlace_sub_lt {w : InfinitePlace K} (hw : w.IsReal) {x y : K}
    (hy : w y = 1) (h : w (x - y) < 1) :
    0 < embedding_of_isReal hw y * embedding_of_isReal hw x := by
  have hy' : |embedding_of_isReal hw y| = 1 := by
    rw [← Real.norm_eq_abs, norm_embedding_of_isReal]
    exact hy
  have hσ : |embedding_of_isReal hw x - embedding_of_isReal hw y| < 1 := by
    rw [← map_sub, ← Real.norm_eq_abs, norm_embedding_of_isReal]
    exact h
  rw [abs_lt] at hσ
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hy' with hy1 | hy1 <;> rw [hy1] at hσ ⊢ <;>
    linarith [hσ.1, hσ.2]

omit [NumberField K] in
/-- An element within `1` of a target of absolute value one at an infinite place is nonzero. -/
theorem ne_zero_of_infinitePlace_sub_lt {w : InfinitePlace K} {x y : K} (hy : w y = 1)
    (h : w (x - y) < 1) : x ≠ 0 := by
  rintro rfl
  rw [coe_apply, zero_sub, AbsoluteValue.map_neg, ← coe_apply, hy] at h
  exact lt_irrefl 1 h





end NumberField

end
end


