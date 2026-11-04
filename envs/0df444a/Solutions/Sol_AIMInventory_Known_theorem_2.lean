-- Prove2me | solution 1 for AIMInventory.Known.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T09:51:45.169068+00:00
-- url     : https://prove2.me/submissions/3e3e72de-c82d-4d9c-b66b-458a46bc73fc

import Mathlib
import Definitions.Def_AIMInventory_Known_AIM
import Definitions.Def_AIMInventory_Known_Queue


section
open MeasureTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

lemma clip_bounds {Y z : ℝ} (hY : 0 ≤ Y) : projInterval Y z ∈ Set.Icc 0 Y := by
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) hY⟩

lemma clip_distance {Y z u : ℝ} (hu : u ∈ Set.Icc 0 Y) :
    (projInterval Y z-u)^2 ≤ (z-u)^2 := by
  unfold projInterval
  rcases le_total z Y with hz | hz
  · rw [min_eq_left hz]
    rcases le_total 0 z with hz0 | hz0
    · rw [max_eq_left hz0]
    · rw [max_eq_right hz0]; nlinarith [hu.1]
  · rw [min_eq_right hz, max_eq_left (hu.1.trans hu.2)]
    nlinarith [hu.2]

lemma state_bounds {Y γ b h q : ℝ} (hq : q ∈ Set.Icc 0 Y)
    (r : Regime) (d : DemandPath) (t : ℕ) :
    (aimState r Y γ b h q d t).1 ∈ Set.Icc 0 Y ∧
    (aimState r Y γ b h q d t).1 ≤ (aimState r Y γ b h q d t).2 ∧
    (aimState r Y γ b h q d t).2 ≤ Y := by
  have hY := hq.1.trans hq.2
  induction t using Nat.twoStepInduction with
  | zero => exact ⟨hq, le_rfl, hq.2⟩
  | one => exact ⟨hq, le_rfl, hq.2⟩
  | more t _ ih =>
    simp only [aimState]
    refine ⟨clip_bounds hY, le_max_left _ _, max_le (clip_bounds hY).2 ?_⟩
    cases r with
    | perishable => exact hY
    | nonPerishable =>
      exact max_le (by have := (d t).coe_nonneg; linarith [ih.2.2]) hY

lemma target_nonneg {Y γ b h q : ℝ} (hq : q ∈ Set.Icc 0 Y)
    (r : Regime) (d : DemandPath) (t : ℕ) : 0 ≤ aimTarget r Y γ b h q d t :=
  (state_bounds hq r d t).1.1

lemma target_le {Y γ b h q : ℝ} (hq : q ∈ Set.Icc 0 Y)
    (r : Regime) (d : DemandPath) (t : ℕ) : aimTarget r Y γ b h q d t ≤ Y :=
  (state_bounds hq r d t).1.2

lemma level_bounds {Y γ b h q : ℝ} (hq : q ∈ Set.Icc 0 Y)
    (r : Regime) (d : DemandPath) (t : ℕ) : aimLevel r Y γ b h q d t ∈ Set.Icc 0 Y :=
  ⟨(state_bounds hq r d t).1.1.trans (state_bounds hq r d t).2.1,
    (state_bounds hq r d t).2.2⟩

lemma target_regime (r : Regime) (Y γ b h q : ℝ) (d : DemandPath) (t : ℕ) :
    aimTarget r Y γ b h q d t = aimTarget .perishable Y γ b h q d t := by
  induction t using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more t _ ih =>
    change projInterval Y (_ - _ * gradEst h b (d t) _) = projInterval Y (_ - _ * gradEst h b (d t) _)
    change aimTarget r Y γ b h q d (t+1) = aimTarget .perishable Y γ b h q d (t+1) at ih
    unfold aimTarget at ih
    rw [ih]

lemma perishable_level {Y γ b h q : ℝ} (hq : q ∈ Set.Icc 0 Y) (d : DemandPath) (t : ℕ) :
    aimLevel .perishable Y γ b h q d t = aimTarget .perishable Y γ b h q d t := by
  cases t with
  | zero => rfl
  | succ t =>
    cases t with
    | zero => rfl
    | succ t =>
      change max (projInterval Y _) 0 = projInterval Y _
      exact max_eq_left (clip_bounds (hq.1.trans hq.2)).1

lemma state_measurable (r : Regime) (Y γ b h q : ℝ) (t : ℕ) :
    Measurable (fun d : DemandPath => aimState r Y γ b h q d t) := by
  induction t using Nat.twoStepInduction with
  | zero => exact measurable_const
  | one => exact measurable_const
  | more t _ ih =>
    simp only [aimState, projInterval, gradEst]
    have hd : Measurable (fun d : DemandPath => (d t : ℝ)) := measurable_coe_nnreal_real.comp (measurable_pi_apply t)
    have hg : Measurable (fun d : DemandPath => if (d t : ℝ) < (aimState r Y γ b h q d (t+1)).1 then h else -b) :=
      Measurable.ite (measurableSet_lt hd ih.fst) measurable_const measurable_const
    have ht := ((ih.fst.sub (hg.const_mul (stepSize γ Y b h (t+1)))).min (measurable_const (a := Y))).max (measurable_const (a := (0:ℝ)))
    apply ht.prodMk
    cases r <;> simp only [nextOnHand]
    · exact ht.max measurable_const
    · exact ht.max ((ih.snd.sub hd).max measurable_const)

lemma state_prefix (r : Regime) (Y γ b h q : ℝ) (t : ℕ) (d e : DemandPath)
    (heq : ∀ j, j+1 < t → d j=e j) :
    aimState r Y γ b h q d t = aimState r Y γ b h q e t := by
  induction t using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more t _ ih =>
    have hs := ih (fun j hj => heq j (by omega))
    simp only [aimState, hs, heq t (by omega)]

end
end AIMProof
end

section
open MeasureTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

def hingeCost (h b y D : ℝ) : ℝ := h * max (y-D) 0 + b * max (D-y) 0

lemma hinge_integrable (P : DemandLaw) (h b y : ℝ) :
    Integrable (fun D : ℝ≥0 => hingeCost h b y D) P.law := by
  exact (((integrable_const y).sub P.finiteMean).sup (integrable_const 0)).const_mul h |>.add
    (((P.finiteMean.sub (integrable_const y)).sup (integrable_const 0)).const_mul b)

lemma Q_integral (P : DemandLaw) (h b : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    Q P h b y = ∫ D : ℝ≥0, hingeCost h b y D ∂P.law := by
  unfold Q LostSalesOrderUpTo.Asymptotic.backorderCost
    LostSalesOrderUpTo.Asymptotic.expectedHolding LostSalesOrderUpTo.Asymptotic.expectedShortfall
  simp only [Real.coe_toNNReal _ hy]
  change _ = ∫ D : ℝ≥0, h * max (y-(D:ℝ)) 0 + b * max ((D:ℝ)-y) 0 ∂P.law
  rw [integral_add]
  · simp only [integral_const_mul]
  · exact (((integrable_const y).sub P.finiteMean).sup (integrable_const 0)).const_mul h
  · exact (((P.finiteMean.sub (integrable_const y)).sup (integrable_const 0)).const_mul b)

lemma hinge_subgradient {h b q u D : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b) :
    hingeCost h b q D - hingeCost h b u D ≤ gradEst h b D q * (q-u) := by
  unfold hingeCost gradEst
  split_ifs with hd
  · rcases le_total D u with hu | hu
    · rw [max_eq_left (by linarith : 0 ≤ q-D), max_eq_right (by linarith : D-q ≤ 0),
        max_eq_left (by linarith : 0 ≤ u-D), max_eq_right (by linarith : D-u ≤ 0)]
      ring_nf
      exact le_rfl
    · rw [max_eq_left (by linarith : 0 ≤ q-D), max_eq_right (by linarith : D-q ≤ 0),
        max_eq_right (by linarith : u-D ≤ 0), max_eq_left (by linarith : 0 ≤ D-u)]
      nlinarith [mul_nonneg hh (sub_nonneg.mpr hu), mul_nonneg hb (sub_nonneg.mpr hu)]
  · have hd' : q ≤ D := le_of_not_gt hd
    rcases le_total D u with hu | hu
    · rw [max_eq_right (by linarith : q-D ≤ 0), max_eq_left (by linarith : 0 ≤ D-q),
        max_eq_left (by linarith : 0 ≤ u-D), max_eq_right (by linarith : D-u ≤ 0)]
      nlinarith [mul_nonneg hh (sub_nonneg.mpr hu), mul_nonneg hb (sub_nonneg.mpr hu)]
    · rw [max_eq_right (by linarith : q-D ≤ 0), max_eq_left (by linarith : 0 ≤ D-q),
        max_eq_right (by linarith : u-D ≤ 0), max_eq_left (by linarith : 0 ≤ D-u)]
      ring_nf
      exact le_rfl

lemma hinge_upper_difference {h b q y D : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b) (hqy : q ≤ y) :
    hingeCost h b y D - hingeCost h b q D ≤ h*(y-q) := by
  have hs := hinge_subgradient (q := y) (u := q) (D := D) hh hb
  unfold gradEst at hs
  split_ifs at hs with hd
  · exact hs
  · nlinarith [mul_nonneg (add_nonneg hh hb) (sub_nonneg.mpr hqy)]

lemma grad_bound {h b D q : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b) :
    |gradEst h b D q| ≤ max b h := by
  unfold gradEst
  split_ifs <;> simp only [abs_neg, abs_of_nonneg hh, abs_of_nonneg hb]
  · exact le_max_right _ _
  · exact le_max_left _ _

lemma grad_measurable (h b : ℝ) : Measurable (fun z : ℝ × ℝ => gradEst h b z.1 z.2) := by
  unfold gradEst
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const measurable_const

lemma grad_integrable (P : DemandLaw) (h b q : ℝ) :
    Integrable (fun D : ℝ≥0 => gradEst h b D q) P.law := by
  classical
  unfold gradEst
  exact Integrable.piecewise (measurableSet_lt measurable_coe_nnreal_real measurable_const)
    (integrable_const h).integrableOn (integrable_const (-b)).integrableOn

lemma Q_subgradient (P : DemandLaw) {h b q u : ℝ}
    (hh : 0 ≤ h) (hb : 0 ≤ b) (hq : 0 ≤ q) (hu : 0 ≤ u) :
    Q P h b q - Q P h b u ≤
      ∫ D : ℝ≥0, gradEst h b D q * (q-u) ∂P.law := by
  rw [Q_integral P h b hq, Q_integral P h b hu, ← integral_sub (hinge_integrable P h b q) (hinge_integrable P h b u)]
  exact integral_mono ((hinge_integrable P h b q).sub (hinge_integrable P h b u))
    ((grad_integrable P h b q).mul_const _) (fun _ => hinge_subgradient hh hb)

lemma Q_upper_difference (P : DemandLaw) {h b q y : ℝ}
    (hh : 0 ≤ h) (hb : 0 ≤ b) (hq : 0 ≤ q) (hqy : q ≤ y) :
    Q P h b y - Q P h b q ≤ h*(y-q) := by
  rw [Q_integral P h b (hq.trans hqy), Q_integral P h b hq,
    ← integral_sub (hinge_integrable P h b y) (hinge_integrable P h b q)]
  calc
    _ ≤ ∫ _ : ℝ≥0, h*(y-q) ∂P.law := integral_mono
      ((hinge_integrable P h b y).sub (hinge_integrable P h b q)) (integrable_const _)
      (fun _ => hinge_upper_difference hh hb hqy)
    _ = _ := by simp

lemma Q_measurable (P : DemandLaw) (h b : ℝ) : Measurable (Q P h b) := by
  have hm : Measurable (fun z : ℝ × ℝ≥0 => hingeCost h b (max z.1 0) z.2) := by
    unfold hingeCost
    fun_prop
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := P.law)
  have he : (fun y : ℝ => ∫ D : ℝ≥0, hingeCost h b (max y 0) D ∂P.law) = Q P h b := by
    funext y
    rw [← Q_integral P h b (le_max_right y 0)]
    unfold Q
    congr 1
    exact NNReal.eq (by simp only [Real.coe_toNNReal' , max_assoc, max_self])
  rw [he] at hi
  exact hi.measurable

lemma Q_nonneg (P : DemandLaw) {h b y : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b) (hy : 0 ≤ y) :
    0 ≤ Q P h b y := by
  rw [Q_integral P h b hy]
  exact integral_nonneg fun _ => add_nonneg (mul_nonneg hh (le_max_right _ _))
    (mul_nonneg hb (le_max_right _ _))

lemma Q_bound (P : DemandLaw) {h b y Y : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hy : y ∈ Set.Icc 0 Y) : Q P h b y ≤ h*Y + b*mean P := by
  rw [Q_integral P h b hy.1]
  calc
    _ ≤ ∫ D : ℝ≥0, h*Y + b*(D:ℝ) ∂P.law := integral_mono (hinge_integrable P h b y)
      ((integrable_const _).add (P.finiteMean.const_mul _)) (fun D => by
        unfold hingeCost
        exact add_le_add (mul_le_mul_of_nonneg_left (max_le (by have := D.coe_nonneg; linarith [hy.2]) (hy.1.trans hy.2)) hh)
          (mul_le_mul_of_nonneg_left (max_le (by linarith [hy.1]) D.coe_nonneg) hb))
    _ = _ := by rw [integral_add (integrable_const _) (P.finiteMean.const_mul _)]; simp [mean, integral_const_mul]

end
end AIMProof
end

section
open Finset
namespace AIMProof

lemma inv_sqrt_succ_le (n : ℕ) :
    1 / Real.sqrt ((n : ℝ) + 1) ≤
      2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hsq0 := Real.sq_sqrt hn
  apply (div_le_iff₀ hp).2
  nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ))]

lemma sum_inv_sqrt_range (n : ℕ) :
    ∑ i ∈ range n, 1 / Real.sqrt ((i : ℝ) + 1) ≤ 2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    linarith [inv_sqrt_succ_le n]

lemma sum_inv_sqrt_Icc (T : ℕ) :
    ∑ i ∈ Icc 1 T, 1 / Real.sqrt (i : ℝ) ≤ 2 * Real.sqrt (T : ℝ) := by
  have he : (∑ i ∈ Icc 1 T, 1 / Real.sqrt (i : ℝ)) =
      ∑ i ∈ range T, 1 / Real.sqrt ((i : ℝ) + 1) := by
    have hset : Icc 1 T = Ico 1 (T+1) := by
      ext i
      simp only [mem_Icc, mem_Ico]
      omega
    rw [hset]
    simpa [add_comm] using (sum_Ico_eq_sum_range (f := fun i : ℕ => 1 / Real.sqrt (i : ℝ)) 1 (T+1))
  rw [he]
  exact sum_inv_sqrt_range T

lemma positive_part_exp_bound {A S : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S) :
    max (A-S) 0 ≤ A * Real.exp (A-S) := by
  by_cases h : S ≤ A
  · rw [max_eq_left (sub_nonneg.2 h)]
    have he : 1 ≤ Real.exp (A-S) := Real.one_le_exp_iff.2 (sub_nonneg.2 h)
    nlinarith
  · rw [max_eq_right (by linarith)]
    positivity

end AIMProof
end

section
open MeasureTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

lemma weighted_telescope (a w : ℕ → ℝ) (A : ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ A)
    (hw : Monotone w) (hw0 : ∀ i, 0 ≤ w i) (n : ℕ) :
    ∑ i ∈ Finset.range (n+1), w i * (a i-a (i+1)) ≤ w n * A := by
  have hs : ∀ n, (∑ i ∈ Finset.range (n+1), w i * (a i-a (i+1))) ≤
      w n * A - w n * a (n+1) := by
    intro n
    induction n with
    | zero => simp only [Nat.reduceAdd, Finset.sum_range_one]
              nlinarith [mul_le_mul_of_nonneg_left (ha 0).2 (hw0 0)]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have he := mul_le_mul_of_nonneg_left (ha (n+1)).2 (sub_nonneg.mpr (hw (Nat.le_succ n)))
      nlinarith
  exact (hs n).trans (sub_le_self _ (mul_nonneg (hw0 n) (ha (n+1)).1))

lemma step_pos {γ Y b h : ℝ} (hγ : 0 < γ) (hY : 0 < Y) (hb : 0 < b)
    {t : ℕ} (ht : 1 ≤ t) : 0 < stepSize γ Y b h t := by
  unfold stepSize
  positivity

lemma target_one_step {γ Y b h q u : ℝ} (hγ : 0 < γ) (hY : 0 < Y)
    (hh : 0 < h) (hb : 0 < b) (hu : u ∈ Set.Icc 0 Y)
    (d : DemandPath) (i : ℕ) :
    2 * (gradEst h b (d i) (aimTarget .perishable Y γ b h q d (i+1)) *
      (aimTarget .perishable Y γ b h q d (i+1)-u)) ≤
    (1 / stepSize γ Y b h (i+1)) *
      ((aimTarget .perishable Y γ b h q d (i+1)-u)^2 -
       (aimTarget .perishable Y γ b h q d (i+2)-u)^2) +
      stepSize γ Y b h (i+1) * (max b h)^2 := by
  have he := step_pos (h := h) hγ hY hb (Nat.succ_le_succ (Nat.zero_le i))
  have hc := clip_distance (z := aimTarget .perishable Y γ b h q d (i+1) -
      stepSize γ Y b h (i+1) * gradEst h b (d i) (aimTarget .perishable Y γ b h q d (i+1))) hu
  have hg := grad_bound (D := (d i : ℝ)) (q := aimTarget .perishable Y γ b h q d (i+1)) hh.le hb.le
  have hg2 : (gradEst h b (d i) (aimTarget .perishable Y γ b h q d (i+1)))^2 ≤ (max b h)^2 :=
    sq_le_sq.mpr (by rw [abs_of_nonneg (le_trans hb.le (le_max_left b h))]; exact hg)
  have hn : aimTarget .perishable Y γ b h q d (i+2) = projInterval Y
      (aimTarget .perishable Y γ b h q d (i+1) - stepSize γ Y b h (i+1) *
        gradEst h b (d i) (aimTarget .perishable Y γ b h q d (i+1))) := rfl
  rw [← hn] at hc
  apply (mul_le_mul_iff_right₀ he).mp
  have hm := mul_le_mul_of_nonneg_left hg2 (sq_nonneg (stepSize γ Y b h (i+1)))
  field_simp
  nlinarith

end
end AIMProof
end

section
open MeasureTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

lemma inv_step_formula {γ Y b h : ℝ} (hγ : 0 < γ) (hY : 0 < Y) (hb : 0 < b)
    {t : ℕ} (ht : 1 ≤ t) :
    1 / stepSize γ Y b h t = max b h / (γ*Y) * Real.sqrt t := by
  have hB : 0 < max b h := hb.trans_le (le_max_left _ _)
  have hs : 0 < Real.sqrt (t:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast ht)
  unfold stepSize
  field_simp

lemma path_regret {γ Y b h q u : ℝ} (hγ : 0 < γ) (hY : 0 < Y)
    (hh : 0 < h) (hb : 0 < b) (hq : q ∈ Set.Icc 0 Y) (hu : u ∈ Set.Icc 0 Y)
    (d : DemandPath) {T : ℕ} (hT : 1 ≤ T) :
    (∑ i ∈ Finset.range T, gradEst h b (d i) (aimTarget .perishable Y γ b h q d (i+1)) *
      (aimTarget .perishable Y γ b h q d (i+1)-u)) ≤
    (γ + 1/γ)*Y*max b h*Real.sqrt T := by
  let B := max b h
  have hB : 0 < B := hb.trans_le (le_max_left _ _)
  let a : ℕ → ℝ := fun i => (aimTarget .perishable Y γ b h q d (i+1)-u)^2
  let w : ℕ → ℝ := fun i => 1/stepSize γ Y b h (i+1)
  have ha : ∀ i, 0 ≤ a i ∧ a i ≤ Y^2 := by
    intro i
    have hqi : aimTarget .perishable Y γ b h q d (i+1) ∈ Set.Icc 0 Y := (state_bounds (γ := γ) (b := b) (h := h) hq .perishable d (i+1)).1
    refine ⟨sq_nonneg _, ?_⟩
    dsimp [a]
    apply sq_le_sq.mpr
    rw [abs_of_pos hY]
    exact abs_le.mpr ⟨by linarith [hqi.1, hu.2], by linarith [hqi.2, hu.1]⟩
  have hwf (i : ℕ) : w i = B/(γ*Y)*Real.sqrt (i+1) := by
    simpa only [w, B, Nat.cast_add, Nat.cast_one] using inv_step_formula (h := h) (t := i+1) hγ hY hb (by omega)
  have hwm : Monotone w := by
    intro i j hij
    rw [hwf, hwf]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hij 1)) (by positivity)
  have hw0 : ∀ i, 0 ≤ w i := fun i => (step_pos hγ hY hb (by omega)).le |> one_div_nonneg.mpr
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  have hw := weighted_telescope a w (Y^2) ha hwm hw0 n
  have hp := Finset.sum_le_sum (s := Finset.range (n+1)) (fun i _ => target_one_step (q := q) hγ hY hh hb hu d i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hp
  have hs : (∑ i ∈ Finset.range (n+1), stepSize γ Y b h (i+1)) ≤
      γ*Y/B*(2*Real.sqrt (n+1)) := by
    calc
      _ = γ*Y/B * ∑ i ∈ Finset.range (n+1), 1/Real.sqrt ((i:ℝ)+1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [stepSize, Nat.cast_add, Nat.cast_one]
        dsimp [B]
        ring
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using mul_le_mul_of_nonneg_left (sum_inv_sqrt_range (n+1)) (show 0 ≤ γ*Y/B by positivity)
  have hs' := mul_le_mul_of_nonneg_right hs (sq_nonneg B)
  have he : B/(γ*Y)*Real.sqrt (n+1)*Y^2 + γ*Y/B*(2*Real.sqrt (n+1))*B^2 =
      (1/γ+2*γ)*Y*B*Real.sqrt (n+1) := by field_simp
  rw [hwf] at hw
  have hfinal : (1/γ+2*γ)*Y*B*Real.sqrt (n+1) ≤
      2*((γ+1/γ)*Y*B*Real.sqrt (n+1))  := by
    have hp : 0 ≤ (1/γ)*Y*B*Real.sqrt (n+1) := by positivity
    nlinarith
  dsimp [a, w] at hw
  dsimp [B] at hs' he hfinal hw
  simp only [Nat.add_assoc, Nat.reduceAdd] at hw
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  nlinarith

end
end AIMProof
end

section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

lemma fresh_independent (P : DemandLaw) (t : ℕ) (f : DemandPath → ℝ)
    (hf : Measurable f) (hp : ∀ d e, (∀ j < t, d j=e j) → f d=f e) :
    IndepFun f (fun d => d t) (demandPathLaw P) := by
  classical
  let S := Finset.range t
  let lift : (S → ℝ≥0) → DemandPath := fun v j => if hj : j < t then v ⟨j, Finset.mem_range.mpr hj⟩ else 0
  have hl : Measurable lift := by
    apply measurable_pi_lambda
    intro j
    dsimp [lift]
    split_ifs <;> fun_prop
  have hi := iIndepFun_infinitePi (P := fun _ : ℕ => P.law) (X := fun _ (D : ℝ≥0) => D)
    (fun _ => measurable_id)
  have hs := hi.indepFun_finset S {t} (by simp [S]) (fun j => measurable_pi_apply j)
  have hc := hs.comp (hf.comp hl) (measurable_pi_apply (⟨t, by simp⟩ : ({t}:Finset ℕ)))
  have he : (fun d : DemandPath => f (lift (fun i : S => d i))) = f := by
    funext d
    apply hp
    intro j hj
    simp [lift, hj]
  simpa only [Function.comp_def, he, demandPathLaw] using hc

lemma fresh_integral (P : DemandLaw) (t : ℕ) (f : DemandPath → ℝ)
    (hf : Measurable f) (hp : ∀ d e, (∀ j < t, d j=e j) → f d=f e)
    (F : ℝ × ℝ≥0 → ℝ) (hF : Measurable F)
    (hi : Integrable (fun d => F (f d, d t)) (demandPathLaw P)) :
    (∫ d, F (f d, d t) ∂demandPathLaw P) =
      ∫ d, ∫ D, F (f d, D) ∂P.law ∂demandPathLaw P := by
  have hj := (fresh_independent P t f hf hp).map_prod_eq_prod_map_map hf.aemeasurable (measurable_pi_apply t).aemeasurable
  have heval : (demandPathLaw P).map (fun d => d t) = P.law :=
    Measure.infinitePi_map_eval (fun _ : ℕ => P.law) t
  rw [heval] at hj
  have hm : Measurable (fun d : DemandPath => (f d, d t)) := hf.prodMk (measurable_pi_apply t)
  have hip : Integrable F (((demandPathLaw P).map f).prod P.law) := by
    rw [← hj]
    exact (integrable_map_measure hF.aestronglyMeasurable hm.aemeasurable).mpr hi
  calc
    _ = ∫ z, F z ∂(((demandPathLaw P).map f).prod P.law) := by
      rw [← hj, integral_map hm.aemeasurable hF.aestronglyMeasurable]
    _ = ∫ x, ∫ D, F (x,D) ∂P.law ∂((demandPathLaw P).map f) := integral_prod F hip
    _ = _ := integral_map hf.aemeasurable hF.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable

end
end AIMProof
end

section
open MeasureTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) : Integrable f μ := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

lemma Q_run_integrable (P : DemandLaw) {h b γ Y q : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hq : q ∈ Set.Icc 0 Y) (r : Regime) (t : ℕ) :
    Integrable (fun d => Q P h b (aimLevel r Y γ b h q d t)) (demandPathLaw P) := by
  apply bounded_integrable _ ((Q_measurable P h b).comp (state_measurable r Y γ b h q t).snd)
  intro d
  change |Q P h b (aimLevel r Y γ b h q d t)| ≤ h*Y+b*mean P
  rw [abs_of_nonneg (Q_nonneg P hh hb (level_bounds hq r d t).1)]
  exact Q_bound P hh hb (level_bounds hq r d t)

lemma grad_product_bound {h b Y u q D : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hq : q ∈ Set.Icc 0 Y) (hu : u ∈ Set.Icc 0 Y) :
    |gradEst h b D q * (q-u)| ≤ max b h * Y := by
  rw [abs_mul]
  exact mul_le_mul (grad_bound hh hb) (abs_le.mpr ⟨by linarith [hq.1, hu.2], by linarith [hq.2, hu.1]⟩)
    (abs_nonneg _) (hb.trans (le_max_left _ _))

lemma target_regret_step (P : DemandLaw) {h b γ Y q u : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hq : q ∈ Set.Icc 0 Y) (hu : u ∈ Set.Icc 0 Y) (i : ℕ) :
    (∫ d, Q P h b (aimTarget .perishable Y γ b h q d (i+1))-Q P h b u ∂demandPathLaw P) ≤
    ∫ d, gradEst h b (d i) (aimTarget .perishable Y γ b h q d (i+1)) *
      (aimTarget .perishable Y γ b h q d (i+1)-u) ∂demandPathLaw P := by
  let f : DemandPath → ℝ := fun d => aimTarget .perishable Y γ b h q d (i+1)
  let F : ℝ × ℝ≥0 → ℝ := fun z => gradEst h b z.2 z.1 * (z.1-u)
  have hf : Measurable f := (state_measurable .perishable Y γ b h q (i+1)).fst
  have hF : Measurable F := by
    apply Measurable.mul
    · exact (grad_measurable h b).comp (measurable_coe_nnreal_real.comp measurable_snd |>.prodMk measurable_fst)
    · exact measurable_fst.sub_const u
  have hi : Integrable (fun d => F (f d,d i)) (demandPathLaw P) :=
    bounded_integrable _ (hF.comp (hf.prodMk (measurable_pi_apply i)))
      (fun d => grad_product_bound hh hb (state_bounds hq .perishable d (i+1)).1 hu)
  have he := fresh_integral P i f hf (fun d e hde => congrArg Prod.fst
    (state_prefix .perishable Y γ b h q (i+1) d e (fun j hj => hde j (by omega)))) F hF hi
  rw [he]
  have hleft : Integrable (fun d => Q P h b (f d)-Q P h b u) (demandPathLaw P) := by
    have hl := (Q_run_integrable P (γ := γ) hh hb hq .perishable (i+1)).sub (integrable_const (Q P h b u))
    exact hl.congr (ae_of_all _ (fun d => by
      change Q P h b (aimLevel .perishable Y γ b h q d (i+1)) - Q P h b u = Q P h b (f d) - Q P h b u
      rw [perishable_level hq]))
  have hright : Integrable (fun d => ∫ D, F (f d,D) ∂P.law) (demandPathLaw P) := by
    apply bounded_integrable _ (C := max b h * Y) (hF.stronglyMeasurable.integral_prod_right'.measurable.comp hf)
    intro d
    have hbd : ∀ D : ℝ≥0, ‖F (f d,D)‖ ≤ max b h * Y := by
      intro D
      exact grad_product_bound hh hb (state_bounds hq .perishable d (i+1)).1 hu
    have hn := norm_integral_le_of_norm_le_const (μ := P.law) (ae_of_all _ hbd)
    simpa [Function.comp_def, measureReal_def]  using hn
  exact integral_mono hleft hright (fun d => Q_subgradient P hh hb (target_nonneg hq .perishable d (i+1)) hu.1)

end
end AIMProof
end

section
open MeasureTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

lemma sum_periods (f : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, f t = ∑ i ∈ Finset.range T, f (i+1) := by
  have hs : Finset.Icc 1 T = Finset.Ico 1 (T+1) := by ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hs]
  simpa [add_comm] using Finset.sum_Ico_eq_sum_range (f := f) 1 (T+1)

lemma target_regret (P : DemandLaw) {h b γ Y q u : ℝ} (hh : 0 < h) (hb : 0 < b)
    (hγ : 0 < γ) (hY : 0 < Y) (hq : q ∈ Set.Icc 0 Y) (hu : u ∈ Set.Icc 0 Y)
    {T : ℕ} (hT : 1 ≤ T) :
    (∫ d, ∑ t ∈ Finset.Icc 1 T,
      (Q P h b (aimTarget .perishable Y γ b h q d t)-Q P h b u) ∂demandPathLaw P) ≤
      (γ+1/γ)*Y*max b h*Real.sqrt T := by
  let g : ℕ → DemandPath → ℝ := fun i d => gradEst h b (d i) (aimTarget .perishable Y γ b h q d (i+1)) *
    (aimTarget .perishable Y γ b h q d (i+1)-u)
  have hg : ∀ i, Integrable (g i) (demandPathLaw P) := by
    intro i
    apply bounded_integrable _ (C := max b h * Y)
    · apply Measurable.mul
      · exact (grad_measurable h b).comp
          ((measurable_coe_nnreal_real.comp (measurable_pi_apply i)).prodMk
            (state_measurable .perishable Y γ b h q (i+1)).fst)
      · exact (state_measurable .perishable Y γ b h q (i+1)).fst.sub_const u
    · intro d
      exact grad_product_bound hh.le hb.le (state_bounds hq .perishable d (i+1)).1 hu
  have hc : ∀ i, Integrable (fun d => Q P h b (aimTarget .perishable Y γ b h q d (i+1))-Q P h b u) (demandPathLaw P) := by
    intro i
    have hs := (Q_run_integrable P (γ := γ) hh.le hb.le hq .perishable (i+1)).sub (integrable_const (Q P h b u))
    exact hs.congr (ae_of_all _ (fun d => by
      change Q P h b (aimLevel .perishable Y γ b h q d (i+1))-Q P h b u = _
      rw [perishable_level hq]))
  simp_rw [sum_periods]
  rw [integral_finsetSum _ (fun i _ => hc i)]
  calc
    _ ≤ ∑ i ∈ Finset.range T, ∫ d, g i d ∂demandPathLaw P :=
      Finset.sum_le_sum (fun i _ => target_regret_step P hh.le hb.le hq hu i)
    _ = ∫ d, ∑ i ∈ Finset.range T, g i d ∂demandPathLaw P :=
      (integral_finsetSum _ (fun i _ => hg i)).symm
    _ ≤ ∫ _ : DemandPath, (γ+1/γ)*Y*max b h*Real.sqrt T ∂demandPathLaw P :=
      integral_mono (integrable_finsetSum _ (fun i _ => hg i)) (integrable_const _)
        (fun d => path_regret hγ hY hh hb hq hu d hT)
    _ = _ := by simp

end
end AIMProof
end

section
open MeasureTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

lemma cumulative_cost_integrable (P : DemandLaw) {h b γ Y q : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hq : q ∈ Set.Icc 0 Y) (r : Regime) (T : ℕ) (v : ℝ) :
    Integrable (fun d => ∑ t ∈ Finset.Icc 1 T, (Q P h b (aimLevel r Y γ b h q d t)-v)) (demandPathLaw P) := by
  exact integrable_finsetSum _ (fun t _ => (Q_run_integrable P hh hb hq r t).sub (integrable_const v))

lemma average_regret (P : DemandLaw) {h b γ Y q : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hq : q ∈ Set.Icc 0 Y) (r : Regime) {T : ℕ} (hT : 1 ≤ T) (v : ℝ) :
    avgExpectedCost P r Y γ b h q T - v =
      (1/(T:ℝ)) * ∫ d, ∑ t ∈ Finset.Icc 1 T,
        (Q P h b (aimLevel r Y γ b h q d t)-v) ∂demandPathLaw P := by
  have hT0 : (T:ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  simp_rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.Icc 1 T).card = T := by simp
  rw [hc, integral_sub (integrable_finsetSum _ (fun t _ => Q_run_integrable P hh hb hq r t)) (integrable_const _)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  unfold avgExpectedCost
  rw [integral_const_mul]
  field_simp

end
end AIMProof
end

section
open MeasureTheory Finset
open CappedBaseStock AIMInventory.Known
namespace AIMProof

noncomputable def input (ρ : ℝ) (s n : ℕ) : ℝ :=
  ∑ j ∈ Ico s n, ρ / Real.sqrt ((j : ℝ) + 1)
noncomputable def demandSum (d : DemandPath) (s n : ℕ) : ℝ :=
  ∑ j ∈ Ico s n, (d j : ℝ)

lemma queue_nonneg (ρ : ℝ) (d : DemandPath) (t : ℕ) : 0 ≤ auxQueue ρ d t := by
  cases t with
  | zero => simp [auxQueue]
  | succ t => cases t <;> simp [auxQueue]

lemma queue_measurable (ρ : ℝ) (t : ℕ) : Measurable (fun d => auxQueue ρ d t) := by
  induction t using Nat.twoStepInduction with
  | zero => simp only [auxQueue]; fun_prop
  | one => simp only [auxQueue]; fun_prop
  | more t _ ih => simp only [auxQueue]; fun_prop

lemma queue_suffix_witness (ρ : ℝ) (d : DemandPath) (n : ℕ) :
    ∃ s ≤ n, auxQueue ρ d (n+1) = input ρ s n - demandSum d s n := by
  induction n with
  | zero => exact ⟨0, le_rfl, by simp [auxQueue, input, demandSum]⟩
  | succ n ih =>
    obtain ⟨s, hs, he⟩ := ih
    by_cases h : 0 ≤ auxQueue ρ d (n+1) + ρ / Real.sqrt ((n : ℝ)+1) - (d n : ℝ)
    · refine ⟨s, by omega, ?_⟩
      simp only [auxQueue, max_eq_left h, input, demandSum]
      rw [sum_Ico_succ_top hs, sum_Ico_succ_top hs]
      dsimp [input, demandSum] at he
      linarith
    · refine ⟨n+1, le_rfl, ?_⟩
      simp [auxQueue, max_eq_right (le_of_not_ge h), input, demandSum]

lemma queue_le_suffix_sum (ρ : ℝ) (d : DemandPath) (n : ℕ) :
    auxQueue ρ d (n+1) ≤ ∑ s ∈ range n, max (input ρ s n - demandSum d s n) 0 := by
  obtain ⟨s, hs, he⟩ := queue_suffix_witness ρ d n
  by_cases hsn : s=n
  · subst s
    rw [he]
    simp only [input, demandSum, Ico_self, sum_empty, sub_self]
    exact sum_nonneg (fun _ _ => le_max_right _ _)
  · have hmem : s ∈ range n := mem_range.2 (by omega)
    have hterm := single_le_sum (fun i (_ : i ∈ range n) => le_max_right (input ρ i n-demandSum d i n) 0) hmem
    exact he ▸ (le_max_left _ _).trans hterm

end AIMProof
end

section
open CappedBaseStock AIMInventory.Known
namespace AIMProof

lemma clip_drop {Y q a g h : ℝ} (hq : q ≤ Y) (ha : 0 ≤ a) (hg : g ≤ h) (hh : 0 ≤ h) :
    q - projInterval Y (q-a*g) ≤ a*h := by
  have hz : q-a*h ≤ q-a*g := by nlinarith
  have hy : q-a*h ≤ Y := by nlinarith
  have hp : q-a*h ≤ projInterval Y (q-a*g) :=
    (le_min hz hy).trans (le_max_left _ _)
  linarith

lemma step_drop_bound {h b γ Y ρ : ℝ} (hh : 0 < h) (hb : 0 < b)
    (hY : 0 < Y) (hγ : γ ≤ ρ*max b h/(h*Y)) (t : ℕ) (ht : 0 < t) :
    stepSize γ Y b h t * h ≤ ρ / Real.sqrt (t:ℝ) := by
  have hB : 0 < max b h := hb.trans_le (le_max_left _ _)
  have hs : 0 < Real.sqrt (t:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast ht)
  have hm : γ*(h*Y) ≤ ρ*max b h := (le_div_iff₀ (mul_pos hh hY)).1 hγ
  unfold stepSize
  apply (le_div_iff₀ hs).2
  field_simp
  nlinarith

lemma excess_le_queue {Y γ b h q ρ : ℝ} (hq : q ∈ Set.Icc 0 Y)
    (hY : 0 < Y) (hγ0 : 0 < γ) (hh : 0 < h) (hb : 0 < b)
    (hγ : γ ≤ ρ*max b h/(h*Y)) (d : DemandPath) (t : ℕ) :
    aimLevel .nonPerishable Y γ b h q d t - aimTarget .nonPerishable Y γ b h q d t ≤ auxQueue ρ d t := by
  induction t using Nat.twoStepInduction with
  | zero => simp [aimLevel, aimTarget, aimState, auxQueue]
  | one => simp [aimLevel, aimTarget, aimState, auxQueue]
  | more t _ ih =>
    let z := aimTarget .nonPerishable Y γ b h q d (t+1)
    let y := aimLevel .nonPerishable Y γ b h q d (t+1)
    let a := stepSize γ Y b h (t+1)
    let qn := projInterval Y (z-a*gradEst h b (d t) z)
    have ha : 0 ≤ a := by dsimp [a, stepSize]; positivity
    have hg : gradEst h b (d t) z ≤ h := by unfold gradEst; split_ifs <;> linarith
    have hdrop : z-qn ≤ ρ/Real.sqrt ((t:ℝ)+1) := by
      have hd := clip_drop (target_le (γ := γ) (b := b) (h := h) hq .nonPerishable d (t+1)) ha hg hh.le
      have hd2 := step_drop_bound hh hb hY hγ (t+1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hd2
      exact hd.trans hd2
    have hqn : 0 ≤ qn := (clip_bounds hY.le).1
    change y-z ≤ auxQueue ρ d (t+1) at ih
    change max qn (max (y-(d t:ℝ)) 0)-qn ≤ max (auxQueue ρ d (t+1)+ρ/Real.sqrt ((t:ℝ)+1)-(d t:ℝ)) 0
    have hleft := le_max_left (auxQueue ρ d (t+1)+ρ/Real.sqrt ((t:ℝ)+1)-(d t:ℝ)) 0
    have hright := le_max_right (auxQueue ρ d (t+1)+ρ/Real.sqrt ((t:ℝ)+1)-(d t:ℝ)) 0
    apply sub_le_iff_le_add.2
    apply max_le
    · linarith
    · apply max_le <;> linarith

end AIMProof
end

section
open MeasureTheory Finset
open CappedBaseStock AIMInventory.Known
namespace AIMProof

lemma input_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (s n : ℕ) : 0 ≤ input ρ s n :=
  sum_nonneg (fun _ _ => div_nonneg hρ (Real.sqrt_nonneg _))
lemma demandSum_nonneg (d : DemandPath) (s n : ℕ) : 0 ≤ demandSum d s n :=
  sum_nonneg (fun _ _ => NNReal.coe_nonneg _)

lemma input_le_total {ρ : ℝ} (hρ : 0 ≤ ρ) (s n : ℕ) :
    input ρ s n ≤ 2 * ρ * Real.sqrt (n : ℝ) := by
  have hsub : Ico s n ⊆ range n := by intro i hi; exact mem_range.2 (mem_Ico.1 hi).2
  calc
    input ρ s n ≤ ∑ j ∈ range n, ρ / Real.sqrt ((j : ℝ)+1) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ρ * ∑ j ∈ range n, 1 / Real.sqrt ((j : ℝ)+1) := by rw [mul_sum]; congr 1; ext j; ring
    _ ≤ ρ * (2 * Real.sqrt (n : ℝ)) := mul_le_mul_of_nonneg_left (sum_inv_sqrt_range n) hρ
    _ = _ := by ring

lemma queue_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (d : DemandPath) (n : ℕ) :
    auxQueue ρ d (n+1) ≤ 2*ρ*Real.sqrt (n : ℝ) := by
  obtain ⟨s, _, he⟩ := queue_suffix_witness ρ d n
  rw [he]
  exact (sub_le_self _ (demandSum_nonneg d s n)).trans (input_le_total hρ s n)

lemma queue_integrable (P : DemandLaw) {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℕ) :
    Integrable (fun d => auxQueue ρ d t) (demandPathLaw P) := by
  cases t with
  | zero => simp [auxQueue]
  | succ n =>
    apply Integrable.mono' (integrable_const (2*ρ*Real.sqrt (n : ℝ))) (queue_measurable ρ (n+1)).aestronglyMeasurable
    filter_upwards [] with d
    rw [Real.norm_eq_abs, abs_of_nonneg (queue_nonneg ρ d (n+1))]
    exact queue_bound hρ d n

lemma input_late_bound {ρ : ℝ} (hρ : 0 ≤ ρ) {s n : ℕ} (hn : 0 < n) (hs : n ≤ 2*s) :
    input ρ s n ≤ (2*ρ/Real.sqrt (n : ℝ)) * ((n-s : ℕ) : ℝ) := by
  have hp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hpoint : ∀ j ∈ Ico s n, ρ / Real.sqrt ((j : ℝ)+1) ≤ 2*ρ/Real.sqrt (n : ℝ) := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjp : 0 < Real.sqrt ((j : ℝ)+1) := Real.sqrt_pos.2 (by positivity)
    have hnj : (n : ℝ) ≤ 2*(j:ℝ) := by exact_mod_cast (show n ≤ 2*j by have := (mem_Ico.1 hj).1; omega)
    have hsqn := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
    have hsqj := Real.sq_sqrt (show 0 ≤ (j:ℝ)+1 by positivity)
    have hroot : Real.sqrt (n:ℝ) ≤ 2*Real.sqrt ((j:ℝ)+1) := by nlinarith [Real.sqrt_nonneg (n:ℝ)]
    apply (div_le_div_iff₀ hjp hp).2
    nlinarith [mul_le_mul_of_nonneg_left hroot hρ]
  have hsum := sum_le_sum hpoint
  simpa [input, mul_comm] using hsum

end AIMProof
end

section
open MeasureTheory
open scoped NNReal
open CappedBaseStock
namespace AIMProof

noncomputable def laplace (P : DemandLaw) : ℝ := ∫ D : ℝ≥0, Real.exp (-(D : ℝ)) ∂P.law

lemma laplace_integrable (P : DemandLaw) :
    Integrable (fun D : ℝ≥0 => Real.exp (-(D : ℝ))) P.law := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  filter_upwards [] with D
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (neg_nonpos.mpr D.coe_nonneg)

lemma laplace_pos (P : DemandLaw) : 0 < laplace P :=
  integral_exp_pos (laplace_integrable P)

lemma laplace_lt_one (P : DemandLaw) : laplace P < 1 := by
  have hf : Integrable (fun D : ℝ≥0 => 1 - Real.exp (-(D : ℝ))) P.law :=
    (integrable_const (1 : ℝ)).sub (laplace_integrable P)
  have hn : ∀ D : ℝ≥0, 0 ≤ 1-Real.exp (-(D : ℝ)) := by
    intro D
    have := Real.exp_le_one_iff.2 (neg_nonpos.mpr D.coe_nonneg)
    linarith
  have hs : Function.support (fun D : ℝ≥0 => 1-Real.exp (-(D : ℝ))) =
      Function.support (fun D : ℝ≥0 => (D : ℝ)) := by
    ext D
    simp only [Function.mem_support, ne_eq]
    apply not_congr
    rw [sub_eq_zero, eq_comm, Real.exp_eq_one_iff, neg_eq_zero]
  have hp : 0 < ∫ D : ℝ≥0, 1-Real.exp (-(D : ℝ)) ∂P.law := by
    apply (integral_pos_iff_support_of_nonneg hn hf).2
    rw [hs]
    exact (integral_pos_iff_support_of_nonneg (fun D : ℝ≥0 => D.coe_nonneg) P.finiteMean).1 P.positiveMean
  rw [integral_sub (integrable_const (1 : ℝ)) (laplace_integrable P)] at hp
  simpa [laplace] using (show (∫ D : ℝ≥0, Real.exp (-(D : ℝ)) ∂P.law) < 1 by simpa using hp)

end AIMProof
end

section
open MeasureTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

lemma finite_integral (P : DemandLaw) (S : Finset ℕ) (f : (S → ℝ≥0) → ℝ)
    (hf : Measurable f) :
    (∫ d, f (S.restrict d) ∂demandPathLaw P) = ∫ v, f v ∂Measure.pi (fun _ : S => P.law) := by
  exact integral_restrict_infinitePi (fun _ : ℕ => P.law) hf.aestronglyMeasurable

lemma laplace_factorization (P : DemandLaw) (s n : ℕ) :
    (∫ d, Real.exp (-(∑ j ∈ Finset.Ico s n, (d j : ℝ))) ∂demandPathLaw P) =
      (∫ D : ℝ≥0, Real.exp (-(D : ℝ)) ∂P.law) ^ (n-s) := by
  let S := Finset.Ico s n
  have hp (d : DemandPath) : Real.exp (-(∑ j ∈ S, (d j : ℝ))) =
      ∏ j : S, Real.exp (-(d j : ℝ)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_coe_sort]
  simp_rw [show Finset.Ico s n = S from rfl, hp]
  have hf := finite_integral P S (fun v => ∏ j : S, Real.exp (-(v j : ℝ))) (by fun_prop)
  simp only [Finset.restrict] at hf
  rw [hf]
  have hh := integral_fintype_prod_eq_prod (μ := fun _ : S => P.law)
    (fun (_ : S) (D : ℝ≥0) => Real.exp (-(D:ℝ)))
  simpa [S, Fintype.card_coe] using hh

end
end AIMProof
end

section
open MeasureTheory Finset
open CappedBaseStock AIMInventory.Known
namespace AIMProof

lemma suffix_exp_integrable (P : DemandLaw) (s n : ℕ) :
    Integrable (fun d => Real.exp (-demandSum d s n)) (demandPathLaw P) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (show AEStronglyMeasurable _ _ from (show Measurable _ by unfold demandSum; fun_prop).aestronglyMeasurable)
  filter_upwards [] with d
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (demandSum_nonneg d s n))

lemma suffix_exp_integral (P : DemandLaw) (ρ : ℝ) (s n : ℕ) :
    (∫ d, input ρ s n * Real.exp (input ρ s n - demandSum d s n) ∂demandPathLaw P) =
      input ρ s n * Real.exp (input ρ s n - (-Real.log (laplace P))*((n-s:ℕ):ℝ)) := by
  have he : (fun d => input ρ s n * Real.exp (input ρ s n - demandSum d s n)) =
      (fun d => (input ρ s n * Real.exp (input ρ s n))*Real.exp (-demandSum d s n)) := by
    funext d
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [he, integral_const_mul]
  have hf := laplace_factorization P s n
  change (∫ d, Real.exp (-demandSum d s n) ∂demandPathLaw P) = laplace P ^ (n-s) at hf
  rw [hf, sub_eq_add_neg, Real.exp_add]
  have hp : Real.exp (-(-Real.log (laplace P) * ((n-s:ℕ):ℝ))) = laplace P^(n-s) := by
    rw [show -(-Real.log (laplace P)*((n-s:ℕ):ℝ)) = ((n-s:ℕ):ℝ)*Real.log (laplace P) by ring,
      Real.exp_nat_mul, Real.exp_log (laplace_pos P)]
  rw [hp]
  ring

lemma queue_expected_le (P : DemandLaw) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    (∫ d, auxQueue ρ d (n+1) ∂demandPathLaw P) ≤
      ∑ s ∈ range n, input ρ s n * Real.exp (input ρ s n - (-Real.log (laplace P))*((n-s:ℕ):ℝ)) := by
  have hi : ∀ s, Integrable (fun d => input ρ s n * Real.exp (input ρ s n - demandSum d s n)) (demandPathLaw P) := by
    intro s
    have he : (fun d => input ρ s n * Real.exp (input ρ s n - demandSum d s n)) =
        (fun d => (input ρ s n * Real.exp (input ρ s n))*Real.exp (-demandSum d s n)) := by
      funext d; rw [sub_eq_add_neg, Real.exp_add]; ring
    rw [he]
    exact (suffix_exp_integrable P s n).const_mul _
  calc
    _ ≤ ∫ d, ∑ s ∈ range n, input ρ s n * Real.exp (input ρ s n-demandSum d s n) ∂demandPathLaw P := by
      apply integral_mono (queue_integrable P hρ (n+1)) (integrable_finsetSum _ (fun s _ => hi s))
      intro d
      exact (queue_le_suffix_sum ρ d n).trans (sum_le_sum (fun s _ => positive_part_exp_bound (input_nonneg hρ s n) (demandSum_nonneg d s n)))
    _ = _ := by rw [integral_finsetSum _ (fun s _ => hi s)]; exact sum_congr rfl (fun s _ => suffix_exp_integral P ρ s n)

end AIMProof
end

section
namespace AIMProof

lemma early_term_bound {ρ c R N L A : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hR : 0 ≤ R) (hRsq : R^2=N) (hL : N ≤ 2*L)
    (hAb : A ≤ 2*ρ*R) (hlarge : 8*ρ ≤ c*R) :
    R*A*Real.exp (A-c*L) ≤ 2*ρ*N*Real.exp (-c*N/4) := by
  have hAN : A ≤ c*N/4 := by nlinarith [mul_le_mul_of_nonneg_right hlarge hR]
  have he : A-c*L ≤ -c*N/4 := by nlinarith [mul_le_mul_of_nonneg_left hL hc]
  have hcoef : R*A ≤ 2*ρ*N := by nlinarith [mul_le_mul_of_nonneg_left hAb hR]
  exact mul_le_mul hcoef (Real.exp_le_exp.2 he) (Real.exp_pos _).le (by nlinarith)

lemma late_term_bound {ρ c R L A : ℝ} (hρ : 0 ≤ ρ)
    (hR : 0 < R) (hL : 0 ≤ L)
    (hAb : R*A ≤ 2*ρ*L) (hlarge : 8*ρ ≤ c*R) :
    R*A*Real.exp (A-c*L) ≤ 2*ρ*L*Real.exp (-c*L/2) := by
  have hAL : A ≤ c*L/2 := by
    have hh : 2*ρ*L ≤ (c*L/2)*R := by nlinarith [mul_le_mul_of_nonneg_right hlarge hL]
    nlinarith
  have he : A-c*L ≤ -c*L/2 := by linarith
  exact mul_le_mul hAb (Real.exp_le_exp.2 he) (Real.exp_pos _).le (by positivity)

end AIMProof
end

section
open Finset
namespace AIMProof

lemma summable_exp_weight {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Summable (fun n : ℕ => (n:ℝ)^k * Real.exp (-c*(n:ℝ))) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.2 (by linarith)
  have hh := summable_pow_mul_geometric_of_norm_lt_one k hr
  simpa only [show ∀ n : ℕ, Real.exp (-c*(n:ℝ)) = Real.exp (-c)^n by intro n; rw [mul_comm, Real.exp_nat_mul]] using hh

noncomputable def tailConstant (ρ c : ℝ) : ℝ :=
  2*ρ*((∑' l : ℕ, (l:ℝ)*Real.exp (-(c/2)*(l:ℝ))) +
    (∑' l : ℕ, (l:ℝ)^2*Real.exp (-(c/4)*(l:ℝ))))

lemma tailConstant_nonneg {ρ c : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ tailConstant ρ c := by
  unfold tailConstant
  positivity

lemma coefficient_bound {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 < c) {n : ℕ} (hn : 0 < n)
    (hlarge : 8*ρ ≤ c*Real.sqrt (n:ℝ)) :
    Real.sqrt (n:ℝ) * (∑ s ∈ range n, input ρ s n * Real.exp (input ρ s n-c*((n-s:ℕ):ℝ))) ≤ tailConstant ρ c := by
  have hR : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hRsq := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
  have hterm : ∀ s ∈ range n,
      Real.sqrt (n:ℝ)*input ρ s n*Real.exp (input ρ s n-c*((n-s:ℕ):ℝ)) ≤
        2*ρ*(n:ℝ)*Real.exp (-c*(n:ℝ)/4) +
        2*ρ*((n-s:ℕ):ℝ)*Real.exp (-c*((n-s:ℕ):ℝ)/2) := by
    intro s hs
    have hsn : s ≤ n := (mem_range.1 hs).le
    have hcast : ((n-s:ℕ):ℝ) = (n:ℝ)-(s:ℝ) := Nat.cast_sub hsn
    by_cases hh : n ≤ 2*s
    · have hi := input_late_bound hρ hn hh
      have hi' : Real.sqrt (n:ℝ)*input ρ s n ≤ 2*ρ*((n-s:ℕ):ℝ) := by
        have := (le_div_iff₀ hR).1 (show input ρ s n ≤ (2*ρ*((n-s:ℕ):ℝ))/Real.sqrt (n:ℝ) by simpa [div_mul_eq_mul_div] using hi)
        nlinarith
      have he := late_term_bound hρ hR (show 0 ≤ ((n-s:ℕ):ℝ) by positivity) hi' hlarge
      exact he.trans (le_add_of_nonneg_left (by positivity))
    · have hl : (n:ℝ) ≤ 2*((n-s:ℕ):ℝ) := by rw [hcast]; exact_mod_cast (show n ≤ 2*(n-s) by omega)
      have he := early_term_bound hρ hc.le hR.le hRsq hl (input_le_total hρ s n) hlarge
      exact he.trans (le_add_of_nonneg_right (by positivity))
  have hsum := sum_le_sum hterm

  have h1 : Summable (fun l : ℕ => (l:ℝ)*Real.exp (-(c/2)*(l:ℝ))) := by simpa using summable_exp_weight (show 0<c/2 by positivity) 1
  have h2 := summable_exp_weight (show 0<c/4 by positivity) 2
  have hrev : (∑ s ∈ range n, ((n-s:ℕ):ℝ)*Real.exp (-(c/2)*((n-s:ℕ):ℝ))) ≤
      ∑' l : ℕ, (l:ℝ)*Real.exp (-(c/2)*(l:ℝ)) := by
    rw [← Nat.Ico_zero_eq_range, sum_Ico_reflect (fun l : ℕ => (l:ℝ)*Real.exp (-(c/2)*(l:ℝ))) 0 (show n ≤ n+1 by omega)]
    exact h1.sum_le_tsum _ (fun _ _ => by positivity)
  have hpoint : (n:ℝ)^2*Real.exp (-(c/4)*(n:ℝ)) ≤
      ∑' l : ℕ, (l:ℝ)^2*Real.exp (-(c/4)*(l:ℝ)) := by
        simpa using h2.sum_le_tsum {n} (fun _ _ => by positivity)
  have hcalc : (∑ s ∈ range n, (2*ρ*(n:ℝ)*Real.exp (-c*(n:ℝ)/4) +
        2*ρ*((n-s:ℕ):ℝ)*Real.exp (-c*((n-s:ℕ):ℝ)/2))) =
      2*ρ*((n:ℝ)^2*Real.exp (-(c/4)*(n:ℝ)) +
        ∑ s ∈ range n, ((n-s:ℕ):ℝ)*Real.exp (-(c/2)*((n-s:ℕ):ℝ))) := by
    have he4 : -c*(n:ℝ)/4 = -(c/4)*(n:ℝ) := by ring
    have he2 : ∀ l : ℕ, -c*(l:ℝ)/2 = -(c/2)*(l:ℝ) := by intro l; ring
    simp_rw [he4, he2]
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_add, mul_sum]
    apply congrArg₂ (fun x y : ℝ => x+y)
    · ring
    · apply sum_congr rfl; intro s _; ring
  rw [hcalc] at hsum
  have heq : (∑ s ∈ range n, Real.sqrt (n:ℝ)*input ρ s n*Real.exp (input ρ s n-c*((n-s:ℕ):ℝ))) = Real.sqrt (n:ℝ)*(∑ s ∈ range n, input ρ s n*Real.exp (input ρ s n-c*((n-s:ℕ):ℝ))) := by
    rw [mul_sum]; apply sum_congr rfl; intro s _; ring
  rw [heq] at hsum
  unfold tailConstant
  nlinarith [mul_le_mul_of_nonneg_left hpoint (show 0 ≤ 2*ρ by positivity), mul_le_mul_of_nonneg_left hrev (show 0 ≤ 2*ρ by positivity)]

end AIMProof
end

section
open MeasureTheory Finset
open CappedBaseStock AIMInventory.Known
namespace AIMProof

lemma queue_rate (P : DemandLaw) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      (∫ d, auxQueue ρ d (n+1) ∂demandPathLaw P) ≤ K / Real.sqrt (n:ℝ) := by
  let c := -Real.log (laplace P)
  have hc : 0 < c := neg_pos.2 (Real.log_neg (laplace_pos P) (laplace_lt_one P))
  obtain ⟨N, hN⟩ := exists_nat_gt ((8*ρ/c)^2)
  let K := max (tailConstant ρ c) (2*ρ*(N:ℝ))
  have hK : 0 ≤ K := (tailConstant_nonneg hρ.le).trans (le_max_left _ _)
  refine ⟨K, hK, fun n => ?_⟩
  by_cases hn : n=0
  · subst n; simp [auxQueue]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hR : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
  have hRsq := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
  apply (le_div_iff₀ hR).2
  by_cases hsmall : n < N
  · have he : (∫ d, auxQueue ρ d (n+1) ∂demandPathLaw P) ≤ 2*ρ*Real.sqrt (n:ℝ) := by
      simpa using integral_mono (queue_integrable P hρ.le (n+1)) (integrable_const (2*ρ*Real.sqrt (n:ℝ))) (fun d => queue_bound hρ.le d n)
    have hreal : (n:ℝ) ≤ N := by exact_mod_cast hsmall.le
    have hm := mul_le_mul_of_nonneg_right he hR.le
    have hk : 2*ρ*(N:ℝ) ≤ K := le_max_right _ _
    nlinarith
  · have hlarge : 8*ρ ≤ c*Real.sqrt (n:ℝ) := by
      have hreal : (N:ℝ) ≤ n := by exact_mod_cast (Nat.le_of_not_gt hsmall)
      have hx : 0 ≤ 8*ρ/c := by positivity
      have hxR : 8*ρ/c ≤ Real.sqrt (n:ℝ) := by nlinarith
      simpa [mul_comm] using (div_le_iff₀ hc).1 hxR
    have he := mul_le_mul_of_nonneg_left (queue_expected_le P hρ.le n) hR.le
    have hb := coefficient_bound hρ.le hc hn0 hlarge
    have hk : tailConstant ρ c ≤ K := le_max_left _ _
    dsimp [c] at hb
    nlinarith

lemma workload_bound (P : DemandLaw) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, 1 ≤ T →
      Integrable (fun d => ∑ t ∈ Icc 1 T, auxQueue ρ d t) (demandPathLaw P) ∧
      (∫ d, ∑ t ∈ Icc 1 T, auxQueue ρ d t ∂demandPathLaw P) ≤ C*Real.sqrt T := by
  obtain ⟨K,hK,hbound⟩ := queue_rate P hρ
  refine ⟨4*K, by positivity, fun T hT => ⟨integrable_finsetSum _ (fun t _ => queue_integrable P hρ.le t), ?_⟩⟩
  have hn : ∀ n : ℕ, (∫ d, auxQueue ρ d (n+1) ∂demandPathLaw P) ≤ 2*K/Real.sqrt ((n:ℝ)+1) := by
    intro n
    by_cases hz : n=0
    · subst n; simp [auxQueue]; positivity
    have hn0 : 0 < n := Nat.pos_of_ne_zero hz
    have hR : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
    have hS : 0 < Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
    have hs : Real.sqrt ((n:ℝ)+1) ≤ 2*Real.sqrt (n:ℝ) := by
      have hnat : (1:ℝ) ≤ n := by exact_mod_cast hn0
      nlinarith [Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (n:ℝ)+1 by positivity)]
    refine (hbound n).trans ((div_le_div_iff₀ hR hS).2 ?_)
    nlinarith [mul_le_mul_of_nonneg_left hs hK]
  rw [integral_finsetSum _ (fun t _ => queue_integrable P hρ.le t)]
  have hset : Icc 1 T = Ico 1 (T+1) := by ext t; simp only [mem_Icc,mem_Ico]; omega
  rw [hset, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1] 
  calc
    _ ≤ ∑ n ∈ range T, 2*K/Real.sqrt ((n:ℝ)+1) := sum_le_sum (fun n _ => hn n)
    _ = 2*K*(∑ n ∈ range T, 1/Real.sqrt ((n:ℝ)+1)) := by rw [mul_sum]; apply sum_congr rfl; intro n _; ring
    _ ≤ 2*K*(2*Real.sqrt (T:ℝ)) := mul_le_mul_of_nonneg_left (sum_inv_sqrt_range T) (by positivity)
    _ = _ := by ring

end AIMProof
end

section
open MeasureTheory
open scoped NNReal BigOperators
namespace AIMProof
open CappedBaseStock AIMInventory.Known
noncomputable section

lemma normalize_sqrt {T : ℕ} (hT : 1 ≤ T) (C : ℝ) :
    (1/(T:ℝ))*(C*Real.sqrt T) = C/Real.sqrt T := by
  have ht : (0:ℝ) < T := by exact_mod_cast hT
  have hs : 0 < Real.sqrt (T:ℝ) := Real.sqrt_pos.mpr ht
  have hsq := Real.sq_sqrt ht.le
  field_simp
  rw [hsq]
  ring

lemma perishable_bound (P : DemandLaw) {h b γ Y q u : ℝ}
    (hh : 0 < h) (hb : 0 < b) (hγ : 0 < γ) (hY : 0 < Y)
    (hq : q ∈ Set.Icc 0 Y) (hu : u ∈ Set.Icc 0 Y) {T : ℕ} (hT : 1 ≤ T) :
    avgExpectedCost P .perishable Y γ b h q T - Q P h b u ≤
      (γ+1/γ)*(Y*max b h/Real.sqrt T) := by
  rw [average_regret P hh.le hb.le hq .perishable hT]
  simp_rw [perishable_level hq]
  have hbnd := mul_le_mul_of_nonneg_left (target_regret P hh hb hγ hY hq hu hT)
    (show 0 ≤ 1/(T:ℝ) by positivity)
  refine hbnd.trans_eq ?_
  rw [normalize_sqrt hT ((γ+1/γ)*Y*max b h)]
  ring

lemma nonperishable_bound (P : DemandLaw) {h b γ Y q u ρ : ℝ}
    (hh : 0 < h) (hb : 0 < b) (hγ : 0 < γ) (hY : 0 < Y)
    (hq : q ∈ Set.Icc 0 Y) (hu : u ∈ Set.Icc 0 Y) (hρ : 0 < ρ)
    (hstep : γ ≤ ρ*max b h/(h*Y)) :
    ∃ C : ℝ, ∀ T : ℕ, 1 ≤ T →
      avgExpectedCost P .nonPerishable Y γ b h q T-Q P h b u ≤ C/Real.sqrt T := by
  obtain ⟨K, _, hK⟩ := workload_bound P hρ
  refine ⟨(γ+1/γ)*Y*max b h+h*K, fun T hT => ?_⟩
  have htint : Integrable (fun d => ∑ t ∈ Finset.Icc 1 T,
      (Q P h b (aimTarget .perishable Y γ b h q d t)-Q P h b u)) (demandPathLaw P) := by
    have hi := cumulative_cost_integrable P (γ := γ) hh.le hb.le hq .perishable T (Q P h b u)
    exact hi.congr (ae_of_all _ (fun d => by simp only [perishable_level hq]))
  have he : (∫ d, ∑ t ∈ Finset.Icc 1 T,
      (Q P h b (aimLevel .nonPerishable Y γ b h q d t)-Q P h b u) ∂demandPathLaw P) ≤
      ((γ+1/γ)*Y*max b h+h*K)*Real.sqrt T := by
    calc
      _ ≤ ∫ d, (∑ t ∈ Finset.Icc 1 T,
          (Q P h b (aimTarget .perishable Y γ b h q d t)-Q P h b u)) +
          h*(∑ t ∈ Finset.Icc 1 T, auxQueue ρ d t) ∂demandPathLaw P := by
        apply integral_mono (cumulative_cost_integrable P hh.le hb.le hq .nonPerishable T (Q P h b u))
          (htint.add ((hK T hT).1.const_mul h))
        intro d
        change (∑ t ∈ Finset.Icc 1 T, (Q P h b (aimLevel .nonPerishable Y γ b h q d t)-Q P h b u)) ≤
          (∑ t ∈ Finset.Icc 1 T, (Q P h b (aimTarget .perishable Y γ b h q d t)-Q P h b u)) + h*(∑ t ∈ Finset.Icc 1 T, auxQueue ρ d t)
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro t _
        have hc := Q_upper_difference P (q := aimTarget .nonPerishable Y γ b h q d t)
          (y := aimLevel .nonPerishable Y γ b h q d t) hh.le hb.le (target_nonneg hq .nonPerishable d t)
          (state_bounds hq .nonPerishable d t).2.1
        have hx := mul_le_mul_of_nonneg_left (excess_le_queue hq hY hγ hh hb hstep d t) hh.le
        rw [target_regime .nonPerishable] at hc hx
        linarith
      _ = (∫ d, ∑ t ∈ Finset.Icc 1 T,
          (Q P h b (aimTarget .perishable Y γ b h q d t)-Q P h b u) ∂demandPathLaw P) +
          h*(∫ d, ∑ t ∈ Finset.Icc 1 T, auxQueue ρ d t ∂demandPathLaw P) := by
        rw [integral_add htint ((hK T hT).1.const_mul h), integral_const_mul]
      _ ≤ _ := by
        have hr := target_regret P hh hb hγ hY hq hu hT
        have hw := mul_le_mul_of_nonneg_left (hK T hT).2 hh.le
        nlinarith
  rw [average_regret P hh.le hb.le hq .nonPerishable hT]
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (normalize_sqrt hT _)

end
end AIMProof
end

section
open MeasureTheory
open scoped NNReal
namespace AIMInventory.Known

/-- Theorem 2, p. 7: under Assumption 1 (`y^NV ≤ ȳ`), the AIM run satisfies, for every `T ≥ 1`,
`E[(1/T) Σ_{t=1}^T Q(y_t)] − Q(y^NV) ≤ (γ + 1/γ) ȳ max{b, h} / √T` in the perishable case; and
in the non-perishable case, if moreover `0 < ρ < E[D_1]`, `E[D_1^6] < ∞` and
`γ ≤ ρ max{b, h}/(hȳ)`, there is a constant `C` with
`E[(1/T) Σ_{t=1}^T Q(y_t)] − Q(y^NV) ≤ C / √T` for every `T ≥ 1`. -/
theorem theorem_2 (P : CappedBaseStock.DemandLaw) (h b γ ybar yhat1 : ℝ)
    (hh : 0 < h) (hb : 0 < b) (hγ : 0 < γ) (hybar : 0 < ybar)
    (hyhat1 : yhat1 ∈ Set.Icc 0 ybar)
    (hNV : ((LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ≥0) : ℝ) ≤ ybar) :
    (∀ T : ℕ, 1 ≤ T →
      avgExpectedCost P .perishable ybar γ b h yhat1 T
          - Q P h b (LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ)
        ≤ (γ + 1 / γ) * (ybar * max b h / Real.sqrt T)) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ < CappedBaseStock.mean P →
      Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 6) P.law →
      γ ≤ ρ * max b h / (h * ybar) →
      ∃ C : ℝ, ∀ T : ℕ, 1 ≤ T →
        avgExpectedCost P .nonPerishable ybar γ b h yhat1 T
            - Q P h b (LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ)
          ≤ C / Real.sqrt T) := by
  refine ⟨fun T hT => ?_, fun ρ hρ _ _ hstep => ?_⟩
  · exact AIMProof.perishable_bound P hh hb hγ hybar hyhat1
      ⟨NNReal.coe_nonneg _, hNV⟩ hT
  · exact AIMProof.nonperishable_bound P hh hb hγ hybar hyhat1
      ⟨NNReal.coe_nonneg _, hNV⟩ hρ hstep

end AIMInventory.Known
end

open AIMInventory.Known MeasureTheory
open scoped NNReal

theorem solution (P : CappedBaseStock.DemandLaw) (h b γ ybar yhat1 : ℝ)
    (hh : 0 < h) (hb : 0 < b) (hγ : 0 < γ) (hybar : 0 < ybar)
    (hyhat1 : yhat1 ∈ Set.Icc 0 ybar)
    (hNV : ((LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ≥0) : ℝ) ≤ ybar) :
    (∀ T : ℕ, 1 ≤ T →
      avgExpectedCost P .perishable ybar γ b h yhat1 T
          - Q P h b (LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ)
        ≤ (γ + 1 / γ) * (ybar * max b h / Real.sqrt T)) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ < CappedBaseStock.mean P →
      Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 6) P.law →
      γ ≤ ρ * max b h / (h * ybar) →
      ∃ C : ℝ, ∀ T : ℕ, 1 ≤ T →
        avgExpectedCost P .nonPerishable ybar γ b h yhat1 T
            - Q P h b (LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ)
          ≤ C / Real.sqrt T) := by
  exact AIMInventory.Known.theorem_2 P h b γ ybar yhat1 hh hb hγ hybar hyhat1 hNV
