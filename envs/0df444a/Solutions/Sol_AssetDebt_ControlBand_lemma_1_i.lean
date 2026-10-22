-- Prove2me | solution 1 for AssetDebt.ControlBand.lemma_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:22:43.341789+00:00
-- url     : https://prove2.me/submissions/e335f794-60d9-416d-bef1-92385318c6a6

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

open MeasureTheory ProbabilityTheory AssetDebt.ControlBand

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ADCBG

lemma U_unfold (P : Params) (t : ℕ) (x p : ℝ) : U P t x p = if P.T < t then 0
    else sSup (objUStep P t x p (fun x' p' => U P (t + 1) x' p') '' Set.Icc 0 (min x P.ℓ)) := by
  rw [U]; rfl

lemma V_unfold (P : Params) (d : ℕ → ℝ) (m t : ℕ) (x w p : ℝ) : V P d m t x w p =
    if m < t then 0 else if p * min x P.ℓ + w < d t then 0
    else sSup (objV P d m t x w p '' {q | Feasible P d t x w p q}) := by
  rw [V]; rfl

/-- Discounted remaining debt `S_t = ∑_{i=t}^m ρ^{i-t} d_i`. -/
noncomputable def Sd (P : Params) (d : ℕ → ℝ) (m t : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc t m, P.ρ ^ (i - t) * d i

lemma Sd_m (P : Params) (d : ℕ → ℝ) (m : ℕ) : Sd P d m m = d m := by
  simp [Sd]

lemma Sd_succ (P : Params) (d : ℕ → ℝ) (m t : ℕ) (ht : t < m) :
    Sd P d m t = d t + P.ρ * Sd P d m (t + 1) := by
  unfold Sd
  rw [← Finset.insert_Icc_add_one_left_eq_Icc ht.le, Finset.sum_insert (by simp), Nat.sub_self,
    pow_zero, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [show i - t = (i - (t + 1)) + 1 by omega, pow_succ]; ring

lemma Sd_ge (P : Params) (hρ : 0 < P.ρ) (d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i) (m t : ℕ) (ht : t ≤ m) :
    d t ≤ Sd P d m t := by
  rcases lt_or_eq_of_le ht with h | h
  · rw [Sd_succ P d m t h]
    have : 0 ≤ Sd P d m (t + 1) := Finset.sum_nonneg (fun i _ => mul_nonneg (pow_nonneg hρ.le _) (hd i))
    nlinarith
  · subst h; rw [Sd_m]

lemma U_zero (P : Params) (hℓ : 0 < P.ℓ) : ∀ k t, t + k = P.T + 1 → ∀ p, U P t 0 p = 0 := by
  intro k
  induction k with
  | zero => intro t ht p; rw [U_unfold, if_pos (by omega)]
  | succ k ih =>
    intro t ht p
    rw [U_unfold, if_neg (by omega), min_eq_left hℓ.le, Set.Icc_self, Set.image_singleton]
    unfold objUStep
    have : (fun p' => U P (t + 1) (0 - 0) p') = fun _ => 0 := by
      funext p'; rw [sub_self]; exact ih (t + 1) (by omega) p'
    rw [this]; simp

lemma U_zero' (P : Params) (hℓ : 0 < P.ℓ) (t : ℕ) (p : ℝ) : U P t 0 p = 0 := by
  by_cases h : P.T < t
  · rw [U_unfold, if_pos h]
  · exact U_zero P hℓ (P.T + 1 - t) t (by omega) p

lemma V_zero_x (P : Params) (hS : P.Standing) (d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i) (m : ℕ) :
    ∀ k t, t + k = m → ∀ w p, 0 ≤ w → 0 < p → V P d m t 0 w p = max (w - Sd P d m t) 0 := by
  have hℓ : 0 < P.ℓ := hS.2.2.2.1
  have hρ : 0 < P.ρ := hS.2.1
  intro k
  induction k with
  | zero =>
    intro t ht w p hw hp
    have htm : t = m := by omega
    subst htm
    rw [V_unfold, if_neg (lt_irrefl _), min_eq_left hℓ.le, mul_zero, zero_add, Sd_m]
    by_cases hb : w < d t
    · rw [if_pos hb, max_eq_right (by linarith)]
    · rw [if_neg hb]
      have hset : {q | Feasible P d t 0 w p q} = {0} := by
        ext q; simp only [Feasible, Set.mem_setOf_eq, Set.mem_singleton_iff, min_eq_left hℓ.le]
        constructor
        · rintro ⟨a, b, _⟩; linarith
        · rintro rfl; refine ⟨le_rfl, le_rfl, by linarith⟩
      rw [hset, Set.image_singleton, csSup_singleton]
      unfold objV objVStep objU objUStep
      rw [if_pos rfl]
      simp only [mul_zero, sub_zero, zero_add]
      have : (fun p' => U P (t + 1) 0 p') = fun _ => 0 := funext (fun p' => U_zero' P hℓ _ _)
      rw [this]; simp only [integral_zero, mul_zero, zero_add]
      rw [max_eq_left (by linarith)]
  | succ k ih =>
    intro t ht w p hw hp
    have htm : t < m := by omega
    have := hS.2.2.2.2.2.1 t
    rw [V_unfold, if_neg (by omega), min_eq_left hℓ.le, mul_zero, zero_add]
    by_cases hb : w < d t
    · rw [if_pos hb, max_eq_right (by linarith [Sd_ge P hρ d hd m t htm.le])]
    · rw [if_neg hb]
      have hset : {q | Feasible P d t 0 w p q} = {0} := by
        ext q; simp only [Feasible, Set.mem_setOf_eq, Set.mem_singleton_iff, min_eq_left hℓ.le]
        constructor
        · rintro ⟨a, b, _⟩; linarith
        · rintro rfl; refine ⟨le_rfl, le_rfl, by linarith⟩
      rw [hset, Set.image_singleton, csSup_singleton]
      unfold objV objVStep
      rw [if_neg (by omega)]
      simp only [mul_zero, sub_zero, add_zero]
      have hae : (fun p' => V P d m (t + 1) 0 (P.ρ⁻¹ * (w - d t)) p') =ᵐ[P.κ t p]
          fun _ => max (P.ρ⁻¹ * (w - d t) - Sd P d m (t + 1)) 0 := by
        filter_upwards [hS.2.2.2.2.2.2.2.2 t p] with z hz
        exact ih (t + 1) (by omega) _ z (mul_nonneg (inv_nonneg.mpr hρ.le) (by linarith)) hz
      rw [integral_congr_ae hae, integral_const]
      simp only [probReal_univ, one_smul]
      rw [Sd_succ P d m t htm, mul_max_of_nonneg _ _ hρ.le, mul_zero]
      congr 1
      field_simp
      ring

noncomputable def Kt (P : Params) (t : ℕ) : ℕ → Kernel ℝ ℝ
  | 0 => Kernel.id
  | k + 1 => P.κ (t + k) ∘ₖ Kt P t k

lemma lawAhead_eq (P : Params) (t k : ℕ) (p : ℝ) : lawAhead P t k p = Kt P t k p := by
  induction k generalizing p with
  | zero => simp [lawAhead, Kt, Kernel.id_apply]
  | succ k ih =>
    simp only [lawAhead, Kt, Kernel.comp_apply, ih]

lemma Kt_succ (P : Params) (t k : ℕ) : Kt P t (k + 1) = Kt P (t + 1) k ∘ₖ P.κ t := by
  induction k with
  | zero => simp [Kt]
  | succ k ih =>
    show P.κ (t + (k + 1)) ∘ₖ Kt P t (k + 1) = P.κ (t + 1 + k) ∘ₖ Kt P (t + 1) k ∘ₖ P.κ t
    rw [ih, Kernel.comp_assoc, show t + (k + 1) = t + 1 + k by omega]

lemma Kt_one (P : Params) (t : ℕ) : Kt P t 1 = P.κ t := by
  rw [Kt_succ]; simp [Kt]

/-- Potential bounding `Ro`: sum of conditional expected absolute future prices. -/
noncomputable def Npot (P : Params) (s : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.T - s), ∫ z, |z| ∂(Kt P s (k + 1) y)

lemma int_abs_Kt (P : Params) (hS : P.Standing) (s k : ℕ) (hk : s + k < P.T) (y : ℝ) :
    Integrable (fun z : ℝ => |z|) (Kt P s (k + 1) y) := by
  have h := hS.2.2.2.2.2.2.2.1 s k hk y
  rw [lawAhead_eq] at h
  exact h.abs

lemma int_Npot_term (P : Params) (hS : P.Standing) (s k : ℕ) (hk : s + 1 + k < P.T) (y : ℝ) :
    Integrable (fun z => ∫ x, |x| ∂(Kt P (s + 1) (k + 1) z)) (P.κ s y) := by
  have h := int_abs_Kt P hS s (k + 1) (by omega) y
  rw [Kt_succ] at h
  have := ((integrable_comp_iff h.aestronglyMeasurable).1 h).2
  simpa [Real.norm_eq_abs, abs_abs] using this

lemma int_Npot (P : Params) (hS : P.Standing) (s : ℕ) (y : ℝ) :
    Integrable (Npot P (s + 1)) (P.κ s y) := by
  unfold Npot
  refine integrable_finsetSum _ (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  exact int_Npot_term P hS s k (by omega) y

lemma Npot_rec (P : Params) (hS : P.Standing) (s : ℕ) (hs : s < P.T) (y : ℝ) :
    ∫ z, (|z| + Npot P (s + 1) z) ∂(P.κ s y) = Npot P s y := by
  have hI1 : Integrable (fun z : ℝ => |z|) (P.κ s y) := (hS.2.2.2.2.2.2.1 s hs y).abs
  rw [integral_add hI1 (int_Npot P hS s y)]
  unfold Npot
  rw [integral_finsetSum _ (fun k hk => by
    rw [Finset.mem_range] at hk; exact int_Npot_term P hS s k (by omega) y)]
  rw [show P.T - s = (P.T - (s + 1)) + 1 by omega, Finset.sum_range_succ', Kt_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have h := int_abs_Kt P hS s (k + 1) (by omega) y
  rw [Kt_succ] at h
  rw [Kt_succ P s (k + 1), Kernel.integral_comp h]


end ADCBG
namespace ADCBG

lemma Npot_ge (P : Params) (s : ℕ) (hs : P.T ≤ s) (y : ℝ) : Npot P s y = 0 := by
  simp [Npot, Nat.sub_eq_zero_of_le hs]

lemma sup_comb {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty) {a b c : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h : ∀ α ∈ A, ∀ β ∈ B, a * α + b * β ≤ c) : a * sSup A + b * sSup B ≤ c := by
  have step1 : ∀ β ∈ B, a * sSup A ≤ c - b * β := by
    intro β hβ
    rcases eq_or_lt_of_le ha with h0 | hpos
    · obtain ⟨α, hα⟩ := hA; have := h α hα β hβ; rw [← h0] at this ⊢; linarith
    · have : sSup A ≤ (c - b * β) / a :=
        csSup_le hA (fun α hα => by rw [le_div_iff₀ hpos]; linarith [h α hα β hβ])
      rw [le_div_iff₀ hpos] at this; linarith
  rcases eq_or_lt_of_le hb with h0 | hpos
  · obtain ⟨β, hβ⟩ := hB; have := step1 β hβ; rw [← h0] at this ⊢; linarith
  · have : sSup B ≤ (c - a * sSup A) / b :=
      csSup_le hB (fun β hβ => by rw [le_div_iff₀ hpos]; linarith [step1 β hβ])
    rw [le_div_iff₀ hpos] at this; linarith

lemma sSup_add_const' {A : Set ℝ} (hA : A.Nonempty) (hb : BddAbove A) (c : ℝ) :
    sSup ((fun v => v + c) '' A) = sSup A + c := by
  have hb' : BddAbove ((fun v => v + c) '' A) := by
    obtain ⟨M, hM⟩ := hb; exact ⟨M + c, by rintro _ ⟨v, hv, rfl⟩; linarith [hM hv]⟩
  apply le_antisymm
  · apply csSup_le (hA.image _); rintro _ ⟨v, hv, rfl⟩; linarith [le_csSup hb hv]
  · have : sSup A ≤ sSup ((fun v => v + c) '' A) - c :=
      csSup_le hA (fun v hv => by linarith [le_csSup hb' ⟨v, hv, rfl⟩])
    linarith

/-- Regularity facts for the debt-free value with a general capacity `ℓ`. -/
structure UFacts (P : Params) (s : ℕ) : Prop where
  meas : ∀ y, 0 ≤ y → y ≤ 1 → Measurable (U P s y)
  nonneg : ∀ y p, 0 ≤ y → y ≤ 1 → 0 ≤ U P s y p
  bound : ∀ y p, 0 ≤ y → y ≤ 1 → U P s y p ≤ |p| + Npot P s p
  conc : ∀ p, ConcaveOn ℝ (Set.Icc 0 1) (fun y => U P s y p)

lemma UFacts_top (P : Params) (s : ℕ) (hs : P.T < s) : UFacts P s := by
  have h0 : ∀ y p, U P s y p = 0 := fun y p => by rw [U_unfold, if_pos hs]
  have hf : ∀ y, U P s y = fun _ => 0 := fun y => funext (h0 y)
  refine ⟨fun y _ _ => by rw [hf]; exact measurable_const, fun y p _ _ => by rw [h0],
    fun y p _ _ => ?_, fun p => ?_⟩
  · rw [h0]
    exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun k _ => integral_nonneg (fun z => abs_nonneg z)))
  · have : (fun y => U P s y p) = fun _ => (0 : ℝ) := funext (fun y => h0 y p)
    rw [this]; exact concaveOn_const 0 (convex_Icc 0 1)

lemma int_next (P : Params) (hS : P.Standing) (s : ℕ) (h : UFacts P (s + 1)) (y : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (p : ℝ) : Integrable (U P (s + 1) y) (P.κ s p) := by
  have := hS.2.2.2.2.2.1 s
  by_cases hsT : s < P.T
  · refine Integrable.mono' ((hS.2.2.2.2.2.2.1 s hsT p).abs.add (int_Npot P hS s p))
      (h.meas y hy0 hy1).aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg y z hy0 hy1), Pi.add_apply]
    exact h.bound y z hy0 hy1
  · have : U P (s + 1) y = fun _ => 0 := funext (fun z => by rw [U_unfold, if_pos (by omega)])
    rw [this]; exact integrable_zero _ _ _

lemma int_bound (P : Params) (hS : P.Standing) (s : ℕ) (h : UFacts P (s + 1)) (y : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (p : ℝ) :
    0 ≤ ∫ z, U P (s + 1) y z ∂(P.κ s p) ∧ P.ρ * ∫ z, U P (s + 1) y z ∂(P.κ s p) ≤ Npot P s p := by
  have := hS.2.2.2.2.2.1 s
  have hnn : 0 ≤ ∫ z, U P (s + 1) y z ∂(P.κ s p) := integral_nonneg (fun z => h.nonneg y z hy0 hy1)
  refine ⟨hnn, ?_⟩
  by_cases hsT : s < P.T
  · have hI1 : Integrable (fun z : ℝ => |z|) (P.κ s p) := (hS.2.2.2.2.2.2.1 s hsT p).abs
    have hle : ∫ z, U P (s + 1) y z ∂(P.κ s p) ≤ ∫ z, (|z| + Npot P (s + 1) z) ∂(P.κ s p) :=
      integral_mono (int_next P hS s h y hy0 hy1 p) (hI1.add (int_Npot P hS s p))
        (fun z => h.bound y z hy0 hy1)
    rw [Npot_rec P hS s hsT p] at hle
    have := hS.2.2.2.1
    nlinarith [hS.2.1, hS.2.2.1]
  · have : U P (s + 1) y = fun _ => 0 := funext (fun z => by rw [U_unfold, if_pos (by omega)])
    rw [this]; simp only [integral_zero, mul_zero]
    exact Finset.sum_nonneg (fun k _ => integral_nonneg (fun z => abs_nonneg z))

lemma phi_eq (P : Params) (s : ℕ) (y p q : ℝ) :
    objUStep P s y p (fun x' p' => U P (s + 1) x' p') q =
      p * q + P.ρ * ∫ z, U P (s + 1) (y - q) z ∂(P.κ s p) := rfl

lemma phi_bound (P : Params) (hS : P.Standing) (s : ℕ) (h : UFacts P (s + 1)) (y p q : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hq : q ∈ Set.Icc 0 (min y P.ℓ)) :
    objUStep P s y p (fun x' p' => U P (s + 1) x' p') q ≤ |p| + Npot P s p := by
  rw [phi_eq]
  have hqy : q ≤ y := le_trans hq.2 (min_le_left _ _)
  have := (int_bound P hS s h (y - q) (by linarith) (by linarith [hq.1]) p).2
  have hpq : p * q ≤ |p| := by
    calc p * q ≤ |p| * q := mul_le_mul_of_nonneg_right (le_abs_self p) hq.1
      _ ≤ |p| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg p)
      _ = |p| := mul_one _
  linarith

lemma U_step (P : Params) (hS : P.Standing) (s : ℕ) (hs : s ≤ P.T) (h : UFacts P (s + 1)) :
    UFacts P s := by
  have hℓ : 0 < P.ℓ := hS.2.2.2.1
  have hℓ1 : P.ℓ ≤ 1 := hS.2.2.2.2.1
  have hρ0 : 0 < P.ρ := hS.2.1
  have := hS.2.2.2.2.2.1 s
  set φ := fun y p q => objUStep P s y p (fun x' p' => U P (s + 1) x' p') q with hφ
  have hU : ∀ y p, U P s y p = sSup (φ y p '' Set.Icc 0 (min y P.ℓ)) := by
    intro y p; rw [U_unfold, if_neg (by omega)]
  have hne : ∀ y, 0 ≤ y → (Set.Icc (0:ℝ) (min y P.ℓ)).Nonempty :=
    fun y hy => ⟨0, le_rfl, le_min hy hℓ.le⟩
  have hbdd : ∀ y p, 0 ≤ y → y ≤ 1 → BddAbove (φ y p '' Set.Icc 0 (min y P.ℓ)) := by
    intro y p hy0 hy1
    exact ⟨|p| + Npot P s p, by rintro _ ⟨q, hq, rfl⟩; exact phi_bound P hS s h y p q hy0 hy1 hq⟩
  -- concavity of the expected continuation
  have hG : ∀ p, ConcaveOn ℝ (Set.Icc 0 1) (fun y' => ∫ z, U P (s + 1) y' z ∂(P.κ s p)) := by
    intro p
    refine ⟨convex_Icc 0 1, fun y1 hy1 y2 hy2 a b ha hb hab => ?_⟩
    have hc : a • y1 + b • y2 ∈ Set.Icc (0:ℝ) 1 := convex_Icc 0 1 hy1 hy2 ha hb hab
    have hI1 := int_next P hS s h y1 hy1.1 hy1.2 p
    have hI2 := int_next P hS s h y2 hy2.1 hy2.2 p
    have hI := int_next P hS s h _ hc.1 hc.2 p
    simp only [smul_eq_mul] at hc ⊢
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hI1.const_mul a) (hI2.const_mul b)]
    apply integral_mono ((hI1.const_mul a).add (hI2.const_mul b)) hI
    intro z
    have := (h.conc z).2 hy1 hy2 ha hb hab
    simp only [Pi.add_apply]
    simpa only [smul_eq_mul] using this
  have hφc : ∀ y p, 0 ≤ y → y ≤ 1 → ConcaveOn ℝ (Set.Icc 0 (min y P.ℓ)) (φ y p) := by
    intro y p hy0 hy1
    refine ⟨convex_Icc _ _, fun q1 hq1 q2 hq2 a b ha hb hab => ?_⟩
    have hq1y : q1 ≤ y := le_trans hq1.2 (min_le_left _ _)
    have hq2y : q2 ≤ y := le_trans hq2.2 (min_le_left _ _)
    have m1 : y - q1 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith [hq1.1]⟩
    have m2 : y - q2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith [hq2.1]⟩
    have hGc := (hG p).2 m1 m2 ha hb hab
    simp only [smul_eq_mul] at hGc ⊢
    simp only [hφ, phi_eq]
    have he : y - (a * q1 + b * q2) = a * (y - q1) + b * (y - q2) := by
      have : b = 1 - a := by linarith
      rw [this]; ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hGc hρ0.le]
  refine ⟨fun y hy0 hy1 => ?_, fun y p hy0 hy1 => ?_, fun y p hy0 hy1 => ?_, fun p => ?_⟩
  · -- measurability via a countable supremum
    set b := min y P.ℓ with hbdef
    have hb0 : 0 ≤ b := le_min hy0 hℓ.le
    have hby : b ≤ y := min_le_left _ _
    set Qs : Set ℝ := ({0, b} : Set ℝ) ∪ (Set.Ioo 0 b ∩ Set.range ((↑) : ℚ → ℝ)) with hQs
    have hQc : Qs.Countable :=
      ((Set.countable_singleton _).insert _).union ((Set.countable_range _).mono Set.inter_subset_right)
    have : Countable Qs := hQc.to_subtype
    have h0Q : (0:ℝ) ∈ Qs := Or.inl (Set.mem_insert _ _)
    have hbQ : b ∈ Qs := Or.inl (Set.mem_insert_of_mem _ rfl)
    have hQsub : Qs ⊆ Set.Icc 0 b := by
      rintro r (hr | hr)
      · rcases hr with hr | hr
        · rw [hr]; exact ⟨le_rfl, hb0⟩
        · rw [Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hb0, le_rfl⟩
      · exact Set.Ioo_subset_Icc_self hr.1
    have : Nonempty Qs := ⟨⟨0, h0Q⟩⟩
    have hmφ : ∀ r : Qs, Measurable (fun p => φ y p r) := by
      intro r
      have hr := hQsub r.2
      have hm := h.meas (y - r) (by linarith [hr.2]) (by linarith [hr.1])
      simp only [hφ, phi_eq]
      exact (measurable_id.mul_const _).add
        ((StronglyMeasurable.integral_kernel (κ := P.κ s) hm.stronglyMeasurable).measurable.const_mul _)
    have heq : ∀ p, U P s y p = ⨆ r : Qs, φ y p r := by
      intro p
      have hbr : BddAbove (Set.range fun r : Qs => φ y p r) :=
        ⟨|p| + Npot P s p, by rintro _ ⟨r, rfl⟩; exact phi_bound P hS s h y p r hy0 hy1 (hQsub r.2)⟩
      rw [hU]
      apply le_antisymm
      · apply csSup_le ((hne y hy0).image _)
        rintro _ ⟨q, hq, rfl⟩
        rcases eq_or_lt_of_le hq.1 with h0 | hq0
        · rw [← h0]; exact le_ciSup hbr ⟨0, h0Q⟩
        rcases eq_or_lt_of_le hq.2 with hb' | hqb
        · have : q = b := hb'
          rw [this]; exact le_ciSup hbr ⟨b, hbQ⟩
        · have hcont : ContinuousOn (φ y p) (Set.Ioo 0 b) :=
            ((hφc y p hy0 hy1).subset Set.Ioo_subset_Icc_self (convex_Ioo 0 b)).continuousOn isOpen_Ioo
          have hcl : q ∈ closure (Set.Ioo 0 b ∩ Set.range ((↑) : ℚ → ℝ)) :=
            Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo ⟨hq0, hqb⟩
          have hmem := ((hcont q ⟨hq0, hqb⟩).mono Set.inter_subset_left).mem_closure_image hcl
          have hsub : φ y p '' (Set.Ioo 0 b ∩ Set.range ((↑) : ℚ → ℝ)) ⊆
              Set.Iic (⨆ r : Qs, φ y p r) := by
            rintro _ ⟨r, hr, rfl⟩; exact le_ciSup hbr ⟨r, Or.inr hr⟩
          exact (isClosed_Iic.closure_subset_iff.mpr hsub) hmem
      · apply ciSup_le; intro r
        exact le_csSup (hbdd y p hy0 hy1) ⟨r, hQsub r.2, rfl⟩
    rw [show U P s y = fun p => ⨆ r : Qs, φ y p r from funext heq]
    exact Measurable.iSup hmφ
  · rw [hU]
    refine le_trans ?_ (le_csSup (hbdd y p hy0 hy1) ⟨0, ⟨le_rfl, le_min hy0 hℓ.le⟩, rfl⟩)
    simp only [hφ, phi_eq, mul_zero, zero_add, sub_zero]
    exact mul_nonneg hρ0.le (int_bound P hS s h y hy0 hy1 p).1
  · rw [hU]
    exact csSup_le ((hne y hy0).image _) (by
      rintro _ ⟨q, hq, rfl⟩; exact phi_bound P hS s h y p q hy0 hy1 hq)
  · refine ⟨convex_Icc 0 1, fun y1 hy1 y2 hy2 a b ha hb hab => ?_⟩
    have hc : a • y1 + b • y2 ∈ Set.Icc (0:ℝ) 1 := convex_Icc 0 1 hy1 hy2 ha hb hab
    simp only [smul_eq_mul] at hc ⊢
    rw [hU y1, hU y2, hU]
    apply sup_comb ((hne y1 hy1.1).image _) ((hne y2 hy2.1).image _) ha hb
    rintro _ ⟨q1, hq1, rfl⟩ _ ⟨q2, hq2, rfl⟩
    have hq : a * q1 + b * q2 ∈ Set.Icc (0:ℝ) (min (a * y1 + b * y2) P.ℓ) := by
      refine ⟨by nlinarith [hq1.1, hq2.1], le_min ?_ ?_⟩
      · nlinarith [hq1.2, hq2.2, min_le_left y1 P.ℓ, min_le_left y2 P.ℓ]
      · nlinarith [hq1.2, hq2.2, min_le_right y1 P.ℓ, min_le_right y2 P.ℓ]
    refine le_trans ?_ (le_csSup (hbdd _ p hc.1 hc.2) ⟨_, hq, rfl⟩)
    have hq1y : q1 ≤ y1 := le_trans hq1.2 (min_le_left _ _)
    have hq2y : q2 ≤ y2 := le_trans hq2.2 (min_le_left _ _)
    have m1 : y1 - q1 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith [hq1.1, hy1.2]⟩
    have m2 : y2 - q2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith [hq2.1, hy2.2]⟩
    have hGc := (hG p).2 m1 m2 ha hb hab
    simp only [smul_eq_mul] at hGc
    simp only [hφ, phi_eq]
    have he : a * y1 + b * y2 - (a * q1 + b * q2) = a * (y1 - q1) + b * (y2 - q2) := by ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hGc hρ0.le]

lemma U_facts (P : Params) (hS : P.Standing) : ∀ k s, s + k = P.T + 1 → UFacts P s := by
  intro k
  induction k with
  | zero => intro s hs; exact UFacts_top P s (by omega)
  | succ k ih => intro s hs; exact U_step P hS s (by omega) (ih (s + 1) (by omega))

lemma U_facts' (P : Params) (hS : P.Standing) (s : ℕ) : UFacts P s := by
  by_cases h : P.T < s
  · exact UFacts_top P s h
  · exact U_facts P hS (P.T + 1 - s) s (by omega)

/-- Lemma 1(i). -/
lemma V_cover (P : Params) (hS : P.Standing) (d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i) (m : ℕ)
    (hmT : m ≤ P.T) : ∀ k t, t + k = m → ∀ x w p, 0 ≤ x → x ≤ 1 → 0 ≤ w → 0 < p →
      Sd P d m t ≤ w → V P d m t x w p = U P t x p + w - Sd P d m t := by
  have hℓ : 0 < P.ℓ := hS.2.2.2.1
  have hρ : 0 < P.ρ := hS.2.1
  intro k
  induction k with
  | zero =>
    intro t ht x w p hx0 hx1 hw hp hcov
    have htm : t = m := by omega
    subst htm
    have hdS := Sd_ge P hρ d hd t t le_rfl
    rw [V_unfold, if_neg (lt_irrefl _), if_neg (by nlinarith [le_min hx0 hℓ.le])]
    have hset : {q | Feasible P d t x w p q} = Set.Icc 0 (min x P.ℓ) := by
      ext q; simp only [Feasible, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨a, b, _⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨a, b, by nlinarith⟩
    rw [hset]
    have hobj : objV P d t t x w p = fun q => objUStep P t x p (fun x' p' => U P (t + 1) x' p') q +
        (w - Sd P d t t) := by
      funext q; unfold objV objVStep objU; rw [if_pos rfl, Sd_m]; ring
    have hbd : BddAbove ((fun q => objUStep P t x p (fun x' p' => U P (t + 1) x' p') q) ''
        Set.Icc 0 (min x P.ℓ)) := ⟨|p| + Npot P t p, by
          rintro _ ⟨q, hq, rfl⟩; exact phi_bound P hS t (U_facts' P hS (t + 1)) x p q hx0 hx1 hq⟩
    have hnei : ((fun q => objUStep P t x p (fun x' p' => U P (t + 1) x' p') q) ''
        Set.Icc 0 (min x P.ℓ)).Nonempty := ⟨_, ⟨0, ⟨le_rfl, le_min hx0 hℓ.le⟩, rfl⟩⟩
    rw [hobj, ← Set.image_image (fun v => v + (w - Sd P d t t)),
      sSup_add_const' hnei hbd,
      U_unfold, if_neg (by omega)]
    ring
  | succ k ih =>
    intro t ht x w p hx0 hx1 hw hp hcov
    have htm : t < m := by omega
    have := hS.2.2.2.2.2.1 t
    have hdS := Sd_ge P hρ d hd m t htm.le
    have hrec := Sd_succ P d m t htm
    have hS1 : 0 ≤ Sd P d m (t + 1) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (pow_nonneg hρ.le _) (hd i))
    rw [V_unfold, if_neg (by omega), if_neg (by nlinarith [le_min hx0 hℓ.le])]
    have hset : {q | Feasible P d t x w p q} = Set.Icc 0 (min x P.ℓ) := by
      ext q; simp only [Feasible, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨a, b, _⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨a, b, by nlinarith⟩
    rw [hset]
    have hF := U_facts' P hS (t + 1)
    have hobj : ∀ q ∈ Set.Icc (0:ℝ) (min x P.ℓ), objV P d m t x w p q =
        objUStep P t x p (fun x' p' => U P (t + 1) x' p') q + (w - Sd P d m t) := by
      intro q hq
      have hqx : q ≤ x := le_trans hq.2 (min_le_left _ _)
      unfold objV objVStep
      rw [if_neg (by omega), phi_eq]
      have hw' : Sd P d m (t + 1) ≤ P.ρ⁻¹ * (w + p * q - d t) := by
        rw [le_inv_mul_iff₀ hρ]; nlinarith [hq.1]
      have hae : (fun z => V P d m (t + 1) (x - q) (P.ρ⁻¹ * (w + p * q - d t)) z) =ᵐ[P.κ t p]
          fun z => U P (t + 1) (x - q) z + (P.ρ⁻¹ * (w + p * q - d t) - Sd P d m (t + 1)) := by
        filter_upwards [hS.2.2.2.2.2.2.2.2 t p] with z hz
        rw [ih (t + 1) (by omega) (x - q) _ z (by linarith) (by linarith [hq.1])
          (le_trans hS1 hw') hz hw']
        ring
      rw [integral_congr_ae hae, integral_add (int_next P hS t hF (x - q) (by linarith)
        (by linarith [hq.1]) p) (integrable_const _), integral_const]
      simp only [probReal_univ, one_smul]
      rw [hrec]
      field_simp
      ring
    have himg : objV P d m t x w p '' Set.Icc 0 (min x P.ℓ) =
        (fun v => v + (w - Sd P d m t)) ''
          ((fun q => objUStep P t x p (fun x' p' => U P (t + 1) x' p') q) '' Set.Icc 0 (min x P.ℓ)) := by
      rw [Set.image_image]
      exact Set.image_congr hobj
    have hbd : BddAbove ((fun q => objUStep P t x p (fun x' p' => U P (t + 1) x' p') q) ''
        Set.Icc 0 (min x P.ℓ)) := ⟨|p| + Npot P t p, by
          rintro _ ⟨q, hq, rfl⟩; exact phi_bound P hS t hF x p q hx0 hx1 hq⟩
    have hnei : ((fun q => objUStep P t x p (fun x' p' => U P (t + 1) x' p') q) ''
        Set.Icc 0 (min x P.ℓ)).Nonempty := ⟨_, ⟨0, ⟨le_rfl, le_min hx0 hℓ.le⟩, rfl⟩⟩
    rw [himg, sSup_add_const' hnei hbd, U_unfold P t, if_neg (by omega)]
    ring

end ADCBG

open ADCBG in
theorem solution (P : Params) (hS : P.Standing) (d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (m : ℕ) (hm : 1 ≤ m ∧ m ≤ P.T) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ m)
    (x w p : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hw : 0 ≤ w) (hp : 0 < p)
    (hcover : ∑ i ∈ Finset.Icc t m, P.ρ ^ (i - t) * d i ≤ w) :
    V P d m t x w p = U P t x p + w - ∑ i ∈ Finset.Icc t m, P.ρ ^ (i - t) * d i :=
  V_cover P hS d hd m hm.2 (m - t) t (by omega) x w p hx.1 hx.2 hw hp hcover
