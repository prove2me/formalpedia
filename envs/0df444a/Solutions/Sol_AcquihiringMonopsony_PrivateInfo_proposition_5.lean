-- Prove2me | solution 1 for AcquihiringMonopsony.PrivateInfo.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T17:37:35.872154+00:00
-- url     : https://prove2.me/submissions/846d9ab4-4fd1-46a1-abcc-b9d340eec826

import Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model

namespace AcquihiringMonopsony.PrivateInfo

open MeasureTheory

lemma acq5_keyLt (c t B : ℝ) (hB : 0 ≤ B) :
    ∫ b in (0:ℝ)..B, (if b < t then c else 0) = c * max 0 (min t B) := by
  rw [intervalIntegral.integral_of_le hB]
  have hf : (fun b : ℝ => if b < t then c else 0) = Set.indicator (Set.Iio t) (fun _ => c) := by
    ext b; simp [Set.indicator_apply]
  rw [hf, MeasureTheory.integral_indicator_const _ measurableSet_Iio, smul_eq_mul,
    Measure.real, Measure.restrict_apply measurableSet_Iio]
  rcases le_total t 0 with h | h
  · have hs : Set.Iio t ∩ Set.Ioc 0 B = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_empty_iff_false,
        iff_false, not_and, not_le]
      intro h1 h2; linarith
    rw [hs, min_eq_left (by linarith), max_eq_left h]; simp
  · rcases le_or_gt t B with h2 | h2
    · have hs : Set.Iio t ∩ Set.Ioc 0 B = Set.Ioo 0 t := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
        constructor
        · rintro ⟨h1, h3, h4⟩; exact ⟨h3, h1⟩
        · rintro ⟨h1, h3⟩; exact ⟨h3, h1, by linarith⟩
      rw [hs, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), min_eq_left h2,
        max_eq_right h]; ring
    · have hs : Set.Iio t ∩ Set.Ioc 0 B = Set.Ioc 0 B := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc]
        constructor
        · rintro ⟨h1, h3, h4⟩; exact ⟨h3, h4⟩
        · rintro ⟨h3, h4⟩; exact ⟨by linarith, h3, h4⟩
      rw [hs, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), min_eq_right h2.le,
        max_eq_right hB]; ring

lemma acq5_keyGe (c u B : ℝ) (hB : 0 ≤ B) :
    ∫ b in (0:ℝ)..B, (if u ≤ b then c else 0) = c * (B - max 0 (min u B)) := by
  rw [intervalIntegral.integral_of_le hB]
  have hf : (fun b : ℝ => if u ≤ b then c else 0) = Set.indicator (Set.Ici u) (fun _ => c) := by
    ext b; simp [Set.indicator_apply]
  rw [hf, MeasureTheory.integral_indicator_const _ measurableSet_Ici, smul_eq_mul,
    Measure.real, Measure.restrict_apply measurableSet_Ici]
  rcases le_total u 0 with h | h
  · have hs : Set.Ici u ∩ Set.Ioc 0 B = Set.Ioc 0 B := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h3, h4⟩; exact ⟨h3, h4⟩
      · rintro ⟨h3, h4⟩; exact ⟨by linarith, h3, h4⟩
    rw [hs, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), min_eq_left (by linarith),
      max_eq_left h]; ring
  · rcases le_or_gt u B with h2 | h2
    · have hs : Set.Ici u ∩ Set.Ioc 0 B ⊆ Set.Icc u B := by
        intro x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
        rintro ⟨h1, h3, h4⟩; exact ⟨h1, h4⟩
      have hs2 : Set.Ioc u B ⊆ Set.Ici u ∩ Set.Ioc 0 B := by
        intro x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc]
        rintro ⟨h1, h4⟩; exact ⟨h1.le, by linarith, h4⟩
      have hv : volume (Set.Ici u ∩ Set.Ioc 0 B) = ENNReal.ofReal (B - u) := by
        apply le_antisymm
        · calc _ ≤ volume (Set.Icc u B) := measure_mono hs
            _ = _ := Real.volume_Icc
        · calc ENNReal.ofReal (B - u) = volume (Set.Ioc u B) := Real.volume_Ioc.symm
            _ ≤ _ := measure_mono hs2
      rw [hv, ENNReal.toReal_ofReal (by linarith), min_eq_left h2, max_eq_right h]; ring
    · have hs : Set.Ici u ∩ Set.Ioc 0 B = ∅ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_empty_iff_false,
          iff_false, not_and, not_le]
        intro h1 h3; linarith
      rw [hs, min_eq_right h2.le, max_eq_right hB]; simp


lemma acq5_clamp (t B : ℝ) (hB : 0 < B) :
    (t ≤ 0 ∧ max 0 (min t B) = 0) ∨ (0 ≤ t ∧ t ≤ B ∧ max 0 (min t B) = t) ∨
      (B ≤ t ∧ max 0 (min t B) = B) := by
  rcases le_total t 0 with h | h
  · left; exact ⟨h, by rw [min_eq_left (by linarith), max_eq_left h]⟩
  · rcases le_total t B with h2 | h2
    · right; left; exact ⟨h, h2, by rw [min_eq_left h2, max_eq_right h]⟩
    · right; right; exact ⟨h2, by rw [min_eq_right h2, max_eq_right hB.le]⟩

lemma acq5_profitA (P : Params) (hB : 0 < P.B) (x ws : ℝ) :
    profitA P x ws = if 0 ≤ x then (1 / P.B) * ((P.va - x) * max 0 (min (x - ws) P.B)) else 0 := by
  unfold profitA
  split_ifs with hx
  · rw [← acq5_keyLt _ _ _ hB.le]
    congr 1
    apply intervalIntegral.integral_congr
    intro b _
    have : (ws + b < x ∧ 0 ≤ x) ↔ b < x - ws :=
      ⟨fun h => by linarith [h.1], fun h => ⟨by linarith, hx⟩⟩
    simp only [JoinsA, this]
  · have : ∀ b : ℝ, ¬ JoinsA x ws b := fun b h => hx h.2
    simp [this]

lemma acq5_poach (P : Params) (hB : 0 < P.B) (x ws : ℝ) (hx : 0 ≤ x) :
    poachProb P x ws = (1 / P.B) * (1 * max 0 (min (x - ws) P.B)) := by
  unfold poachProb
  rw [← acq5_keyLt _ _ _ hB.le]
  congr 1
  apply intervalIntegral.integral_congr
  intro b _
  have : (ws + b < x ∧ 0 ≤ x) ↔ b < x - ws :=
    ⟨fun h => by linarith [h.1], fun h => ⟨by linarith, hx⟩⟩
  simp only [JoinsA, this]

lemma acq5_profitS (P : Params) (hB : 0 < P.B) (wa y : ℝ) (hwa : 0 < wa) :
    profitS P wa y = (1 / P.B) * ((P.vs - y) * (P.B - max 0 (min (wa - y) P.B))) := by
  unfold profitS
  rw [← acq5_keyGe _ _ _ hB.le]
  congr 1
  apply intervalIntegral.integral_congr
  intro b _
  have : (wa ≤ y + b ∧ 0 ≤ y + b) ↔ wa - y ≤ b :=
    ⟨fun h => by linarith [h.1], fun h => ⟨by linarith, by linarith⟩⟩
  simp only [StaysS, this]

theorem proposition_5 (P : Params) (hP : P.Standing) :
    P.vs < vHat P ∧
    IsDHEquilibrium P (waStar P) (wsStar P) ∧
    (vHat P < P.va → profitA P (waStar P) (wsStar P) < ahProfitA P) ∧
    (P.va < vHat P → ahProfitA P < profitA P (waStar P) (wsStar P) ∧
      poachProb P (waStar P) (wsStar P) = (P.va - P.vs + P.B) / (3 * P.B)) ∧
    (∀ b ∈ Set.Icc (0:ℝ) P.B, ahPayoffE P b < dhPayoffE (waStar P) (wsStar P) b) := by
  obtain ⟨hB, hBa, hBs, h1, h2⟩ := hP
  have s5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have s5n : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have s5lt : Real.sqrt 5 < 7 / 3 := by nlinarith
  have s5gt : 5 / 3 < Real.sqrt 5 := by nlinarith
  have hwa : 0 < waStar P := by unfold waStar; linarith
  have hws : 0 < wsStar P := by unfold wsStar; linarith
  have hdiff : waStar P - wsStar P = (P.va - P.vs + P.B) / 3 := by unfold waStar wsStar; ring
  have hbs0 : 0 < (P.va - P.vs + P.B) / 3 := by linarith
  have hbsB : (P.va - P.vs + P.B) / 3 < P.B := by linarith
  have hcl : max 0 (min (waStar P - wsStar P) P.B) = (P.va - P.vs + P.B) / 3 := by
    rw [hdiff, min_eq_left hbsB.le, max_eq_right hbs0.le]
  have hprofA : profitA P (waStar P) (wsStar P) =
      ((P.va - P.vs + P.B) / 3) * ((P.va - P.vs + P.B) / 3) / P.B := by
    rw [acq5_profitA P hB, if_pos hwa.le, hcl]; unfold waStar; field_simp; ring
  have hvhat : vHat P = P.vs + (7 - 3 * Real.sqrt 5) / 2 * P.B := rfl
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hvhat]; nlinarith
  · intro x
    rw [hprofA, acq5_profitA P hB]
    split_ifs with hx
    · rw [show (1 / P.B) * ((P.va - x) * max 0 (min (x - wsStar P) P.B)) =
          ((P.va - x) * max 0 (min (x - wsStar P) P.B)) / P.B by ring]
      apply div_le_div_of_nonneg_right _ hB.le
      have hax : P.va - x = 2 * ((P.va - P.vs + P.B) / 3) - (x - wsStar P) := by
        unfold wsStar; ring
      rw [hax]
      rcases acq5_clamp (x - wsStar P) P.B hB with ⟨ht, hc⟩ | ⟨ht, ht2, hc⟩ | ⟨ht, hc⟩ <;> rw [hc]
      · nlinarith
      · nlinarith [sq_nonneg (x - wsStar P - (P.va - P.vs + P.B) / 3)]
      · nlinarith [sq_nonneg (P.B - (P.va - P.vs + P.B) / 3)]
    · positivity
  · intro y
    rw [acq5_profitS P hB _ _ hwa, acq5_profitS P hB _ _ hwa, hdiff, min_eq_left hbsB.le,
      max_eq_right hbs0.le]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsy : P.vs - y = P.B - 2 * ((P.va - P.vs + P.B) / 3) + (waStar P - y) := by
      unfold waStar; ring
    have hsws : P.vs - wsStar P = P.B - (P.va - P.vs + P.B) / 3 := by unfold wsStar; ring
    rw [hsy, hsws]
    rcases acq5_clamp (waStar P - y) P.B hB with ⟨ht, hc⟩ | ⟨ht, ht2, hc⟩ | ⟨ht, hc⟩ <;> rw [hc]
    · nlinarith [sq_nonneg (P.B - 2 * ((P.va - P.vs + P.B) / 3))]
    · nlinarith [sq_nonneg (waStar P - y - (P.va - P.vs + P.B) / 3)]
    · nlinarith
  · intro hv
    rw [hvhat] at hv
    rw [hprofA, ahProfitA, max_eq_right (by nlinarith), div_lt_iff₀ hB]
    have hp := mul_pos (sub_pos.2 hv)
      (show 0 < P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B - P.va by nlinarith)
    have hid : (P.va - (P.vs + (7 - 3 * Real.sqrt 5) / 2 * P.B)) *
        (P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B - P.va) =
        -((P.va - P.vs)^2 - 7 * P.B * (P.va - P.vs) + P.B^2) := by
      linear_combination (9/4 * P.B^2) * s5
    have he : (P.va - P.vs + P.B) / 3 * ((P.va - P.vs + P.B) / 3) - (P.va - P.vs) * P.B =
        ((P.va - P.vs)^2 - 7 * P.B * (P.va - P.vs) + P.B^2) / 9 := by ring
    linarith
  · intro hv
    rw [hvhat] at hv
    refine ⟨?_, ?_⟩
    · rw [hprofA, ahProfitA, lt_div_iff₀ hB]
      rcases le_total P.va P.vs with hle | hle
      · rw [max_eq_left (by linarith)]; nlinarith [mul_pos hbs0 hbs0]
      · rw [max_eq_right (by linarith)]
        have hp := mul_pos (sub_pos.2 hv)
          (show 0 < P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B - P.va by nlinarith)
        have hid : (P.vs + (7 - 3 * Real.sqrt 5) / 2 * P.B - P.va) *
            (P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B - P.va) =
            (P.va - P.vs)^2 - 7 * P.B * (P.va - P.vs) + P.B^2 := by
          linear_combination (-9/4 * P.B^2) * s5
        have he : (P.va - P.vs + P.B) / 3 * ((P.va - P.vs + P.B) / 3) - (P.va - P.vs) * P.B =
            ((P.va - P.vs)^2 - 7 * P.B * (P.va - P.vs) + P.B^2) / 9 := by ring
        linarith
    · rw [acq5_poach P hB _ _ hwa.le, hcl]; field_simp
  · intro b hb
    unfold ahPayoffE dhPayoffE
    split_ifs
    · exact lt_max_of_lt_left (lt_max_of_lt_left hwa)
    · exact lt_max_of_lt_left (lt_max_of_lt_right (by linarith [hb.1]))

end AcquihiringMonopsony.PrivateInfo


-- Platform entry point: restates the target verbatim.
namespace AcquihiringMonopsony.PrivateInfo

theorem _root_.solution (P : Params) (hP : P.Standing) :
    P.vs < vHat P ∧
    IsDHEquilibrium P (waStar P) (wsStar P) ∧
    (vHat P < P.va → profitA P (waStar P) (wsStar P) < ahProfitA P) ∧
    (P.va < vHat P → ahProfitA P < profitA P (waStar P) (wsStar P) ∧
      poachProb P (waStar P) (wsStar P) = (P.va - P.vs + P.B) / (3 * P.B)) ∧
    (∀ b ∈ Set.Icc (0:ℝ) P.B, ahPayoffE P b < dhPayoffE (waStar P) (wsStar P) b) := by
  apply @AcquihiringMonopsony.PrivateInfo.proposition_5 <;> assumption

end AcquihiringMonopsony.PrivateInfo
