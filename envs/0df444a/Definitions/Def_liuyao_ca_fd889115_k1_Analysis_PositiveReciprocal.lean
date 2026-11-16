-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PositiveReciprocal
-- name    : liuyao_ca_fd889115_k1_Analysis_PositiveReciprocal
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:30.451405+00:00
-- url     : https://prove2.me/theorems/776b7ea8-bbfa-486b-a7b8-eb7573838eba
-- title:
--   Computable analysis · PositiveReciprocal · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/PositiveReciprocal.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

/-!
# Positive reciprocals of raw reals

This file supplies the finite interval operation needed to form a reciprocal
when a valid raw real comes with a uniform positive rational lower bound.
The lower clipping step is explicit: it replaces the lower endpoint by the
maximum of the computed endpoint and the certified bound.  No completed real
or nonzero decision is used.
-/

namespace ComputableAnalysis
namespace RealCompute

/-- Clip the lower endpoint of every box at a fixed rational bound. -/
def lowerClip (x : RealCompute) (lower : Rat) : RealCompute where
  compute := fun n =>
    let I := x.compute n
    { lo := maxRat2 I.lo lower, hi := I.hi }

theorem lowerClip_compute (x : RealCompute) (lower : Rat) (n : Nat) :
    (lowerClip x lower).compute n =
      { lo := maxRat2 (x.compute n).lo lower,
        hi := (x.compute n).hi } := by
  rfl

/-- Lower clipping can only reduce the width of a rational interval box. -/
theorem lowerClip_compute_width_le
    (x : RealCompute) (lower : Rat) (n : Nat) :
    ((lowerClip x lower).compute n).width <= (x.compute n).width := by
  rw [lowerClip_compute]
  unfold QInterval.width maxRat2
  by_cases h : (x.compute n).lo <= lower
  · simp [h]
    grind [Rat.sub_eq_add_neg]
  · simp [h]

/-- Lower clipping preserves validity when the clipping point remains below
every upper endpoint. -/
theorem lowerClip_valid
    (x : RealCompute) (lower : Rat) (hx : x.Valid)
    (hlower : forall n, lower <= (x.compute n).hi) :
    (lowerClip x lower).Valid := by
  constructor
  · intro n
    rw [lowerClip_compute]
    unfold QInterval.width maxRat2
    by_cases h : (x.compute n).lo <= lower
    · simp [h]
      grind [Rat.sub_eq_add_neg, hlower n]
    · simp [h]
      exact hx.1 n
  · constructor
    · intro n m hnm
      have hnested := hx.2.1 n m hnm
      rw [lowerClip_compute, lowerClip_compute]
      unfold maxRat2
      by_cases hn : (x.compute n).lo <= lower
      · rw [if_pos hn]
        by_cases hm : (x.compute m).lo <= lower
        · rw [if_pos hm]
          exact ⟨Rat.le_refl, hlower m, hnested.2.2⟩
        · rw [if_neg hm]
          exact ⟨by grind, hnested.2.1, hnested.2.2⟩
      · rw [if_neg hn]
        have hm : ¬(x.compute m).lo <= lower := by
          intro hml
          exact hn (Rat.le_trans hnested.1 hml)
        rw [if_neg hm]
        exact hnested
    · intro eps
      obtain ⟨N, hN⟩ := hx.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hwidth := hN n hn
      rw [lowerClip_compute]
      unfold QInterval.width maxRat2
      by_cases h : (x.compute n).lo <= lower
      · simp [h]
        have hl := hlower n
        have hlo : (x.compute n).lo <= lower := h
        grind [QInterval.width, Rat.sub_eq_add_neg]
      · simp [h]
        exact hwidth

/-- The reciprocal evaluator of a positively clipped raw real. -/
def positiveReciprocal (x : RealCompute) (lower : Rat) : RealCompute where
  compute := fun n => QInterval.inv ((lowerClip x lower).compute n)

theorem positiveReciprocal_compute
    (x : RealCompute) (lower : Rat) (hlower : 0 < lower) (n : Nat) :
    (positiveReciprocal x lower).compute n =
      { lo := 1 / (x.compute n).hi,
        hi := 1 / maxRat2 (x.compute n).lo lower } := by
  rw [show (positiveReciprocal x lower).compute n =
      QInterval.inv ((lowerClip x lower).compute n) by rfl]
  rw [lowerClip_compute]
  have hmax : 0 < maxRat2 (x.compute n).lo lower := by
    unfold maxRat2
    by_cases h : (x.compute n).lo <= lower
    · simp [h, hlower]
    · simp [h]
      grind
  simp [QInterval.inv, hmax]

theorem one_div_antitone_of_pos {a b : Rat}
    (ha : 0 < a) (hab : a <= b) : 1 / b <= 1 / a := by
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · have hane : a ≠ 0 := Rat.ne_of_gt ha
    have hb : 0 < b := by grind
    have hbne : b ≠ 0 := Rat.ne_of_gt hb
    calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hbne]
      _ <= b := hab
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hane]
  · exact Rat.mul_pos ha (by grind)

/-- A valid raw real with a uniform positive rational lower bound has a valid
reciprocal, computed by rational interval inversion after lower clipping. -/
theorem positiveReciprocal_valid
    (x : RealCompute) (lower : Rat) (hx : x.Valid) (hlower0 : 0 < lower)
    (hlower : forall n, lower <= (x.compute n).hi) :
    (positiveReciprocal x lower).Valid := by
  let y := lowerClip x lower
  have hy : y.Valid := lowerClip_valid x lower hx hlower
  have hyLower : forall n, lower <= (y.compute n).lo := by
    intro n
    dsimp [y]
    rw [lowerClip_compute]
    unfold maxRat2
    by_cases h : (x.compute n).lo <= lower
    · simp [h]
    · simp [h]
      grind
  have hyPos : forall n, 0 < (y.compute n).lo := fun n =>
    by grind
  constructor
  · intro n
    change 0 <= (QInterval.inv (y.compute n)).width
    simp [QInterval.inv, hyPos n]
    have horder := interval_order_of_valid y hy n
    have hrecip := one_div_antitone_of_pos (hyPos n) horder
    grind [QInterval.width, Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hnested := hy.2.1 n m hnm
      change (QInterval.inv (y.compute n)).lo <=
          (QInterval.inv (y.compute m)).lo /\
        (QInterval.inv (y.compute m)).lo <=
          (QInterval.inv (y.compute m)).hi /\
        (QInterval.inv (y.compute m)).hi <=
          (QInterval.inv (y.compute n)).hi
      simp [QInterval.inv, hyPos n, hyPos m]
      exact ⟨
        one_div_antitone_of_pos
          (by grind [hyPos m, hnested.2.2]) hnested.2.2,
        one_div_antitone_of_pos (hyPos m) hnested.2.1,
        one_div_antitone_of_pos (hyPos n) hnested.1⟩
    · intro eps
      let scaled : QPos :=
        { val := eps.val * lower * lower
          property := Rat.mul_pos
            (Rat.mul_pos eps.property hlower0) hlower0 }
      obtain ⟨N, hN⟩ := hy.2.2 scaled
      refine ⟨N, ?_⟩
      intro n hn
      have hwidth := hN n hn
      have horder := interval_order_of_valid y hy n
      have hlo := hyPos n
      have hhi : 0 < (y.compute n).hi := by grind
      change (QInterval.inv (y.compute n)).width <= eps.val
      simp [QInterval.inv, hlo]
      change 1 / (y.compute n).lo - 1 / (y.compute n).hi <= eps.val
      rw [show 1 / (y.compute n).lo - 1 / (y.compute n).hi =
          (y.compute n).width /
            ((y.compute n).lo * (y.compute n).hi) by
        unfold QInterval.width
        rw [Rat.div_def, Rat.div_def, Rat.div_def]
        have hloNe := Rat.ne_of_gt hlo
        have hhiNe := Rat.ne_of_gt hhi
        grind [Rat.sub_eq_add_neg, Rat.inv_mul_rev,
          Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel _ hloNe, Rat.mul_inv_cancel _ hhiNe]]
      have hprod : lower * lower <=
          (y.compute n).lo * (y.compute n).hi := by
        exact rat_mul_le_mul_of_nonneg
          (Rat.le_of_lt hlower0) (hyLower n)
          (Rat.le_of_lt hlower0)
          (Rat.le_trans (hyLower n) horder)
      have hinv := one_div_antitone_of_pos
        (Rat.mul_pos hlower0 hlower0) hprod
      have hwidth0 := hy.1 n
      rw [Rat.div_def]
      calc
        (y.compute n).width *
            ((y.compute n).lo * (y.compute n).hi)⁻¹ <=
            (y.compute n).width * (1 / (lower * lower)) :=
          Rat.mul_le_mul_of_nonneg_left
            (by simpa [Rat.div_def] using hinv) hwidth0
        _ <= scaled.val * (1 / (lower * lower)) :=
          Rat.mul_le_mul_of_nonneg_right hwidth
            (Rat.le_of_lt (by
              rw [Rat.div_def]
              exact Rat.mul_pos (by decide +kernel)
                ((Rat.inv_pos).2 (Rat.mul_pos hlower0 hlower0))))
        _ = eps.val := by
          dsimp [scaled]
          rw [Rat.div_def]
          have hne : lower * lower ≠ 0 :=
            Rat.ne_of_gt (Rat.mul_pos hlower0 hlower0)
          grind [Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel _ hne]

/-- Quantitative interval inversion: clipping at `lower > 0` followed by
reciprocal inversion costs at most the input width divided by `lower^2`.
This pointwise estimate exposes the rate hidden inside the validity proof. -/
theorem positiveReciprocal_compute_width_le
    (x : RealCompute) (lower : Rat) (hx : x.Valid) (hlower0 : 0 < lower)
    (hlower : forall n, lower <= (x.compute n).hi) (n : Nat) :
    ((positiveReciprocal x lower).compute n).width <=
      (x.compute n).width / (lower * lower) := by
  let y := lowerClip x lower
  have hy : y.Valid := lowerClip_valid x lower hx hlower
  have hyLower : lower <= (y.compute n).lo := by
    dsimp [y]
    rw [lowerClip_compute]
    unfold maxRat2
    by_cases h : (x.compute n).lo <= lower
    · simp [h]
    · simp [h]
      grind
  have hyLoPos : 0 < (y.compute n).lo := by grind
  have hyOrder := interval_order_of_valid y hy n
  have hyHiPos : 0 < (y.compute n).hi := by grind
  have hprod : lower * lower <=
      (y.compute n).lo * (y.compute n).hi :=
    rat_mul_le_mul_of_nonneg
      (Rat.le_of_lt hlower0) hyLower
      (Rat.le_of_lt hlower0) (Rat.le_trans hyLower hyOrder)
  have hinv := one_div_antitone_of_pos
    (Rat.mul_pos hlower0 hlower0) hprod
  have hyWidth0 := hy.1 n
  have hclipWidth : (y.compute n).width <= (x.compute n).width := by
    exact lowerClip_compute_width_le x lower n
  change (QInterval.inv (y.compute n)).width <= _
  simp [QInterval.inv, hyLoPos]
  change 1 / (y.compute n).lo - 1 / (y.compute n).hi <= _
  rw [show 1 / (y.compute n).lo - 1 / (y.compute n).hi =
      (y.compute n).width /
        ((y.compute n).lo * (y.compute n).hi) by
    unfold QInterval.width
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have hloNe := Rat.ne_of_gt hyLoPos
    have hhiNe := Rat.ne_of_gt hyHiPos
    grind [Rat.sub_eq_add_neg, Rat.inv_mul_rev,
      Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel _ hloNe, Rat.mul_inv_cancel _ hhiNe]]
  have hinvNonneg : 0 <= 1 / (lower * lower) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hlower0 hlower0)))
  calc
    (y.compute n).width /
        ((y.compute n).lo * (y.compute n).hi) <=
      (y.compute n).width / (lower * lower) := by
        rw [Rat.div_def, Rat.div_def]
        exact Rat.mul_le_mul_of_nonneg_left
          (by simpa [Rat.div_def] using hinv) hyWidth0
    _ <= (x.compute n).width / (lower * lower) := by
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right hclipWidth
        (by simpa [Rat.div_def] using hinvNonneg)

theorem positiveReciprocal_compute_hi_le
    (x : RealCompute) (lower : Rat) (hlower0 : 0 < lower) (n : Nat) :
    ((positiveReciprocal x lower).compute n).hi <= 1 / lower := by
  rw [positiveReciprocal_compute x lower hlower0 n]
  apply one_div_antitone_of_pos hlower0
  unfold maxRat2
  by_cases h : (x.compute n).lo <= lower <;> simp [h]
  grind

end RealCompute
end ComputableAnalysis


