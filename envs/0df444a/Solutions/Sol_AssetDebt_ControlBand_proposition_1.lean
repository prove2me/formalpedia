-- Prove2me | solution 1 for AssetDebt.ControlBand.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:08:08.610445+00:00
-- url     : https://prove2.me/submissions/48f5dcd3-c546-4996-b400-2a04c65039b5

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

open MeasureTheory ProbabilityTheory AssetDebt.ControlBand

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ADCBSol

/-! ## Part 1: the debt-free value `U` is linear in `x`. -/

lemma U_unfold (P : Params) (t : ℕ) (x p : ℝ) : U P t x p = if P.T < t then 0
    else sSup (objUStep P t x p (fun x' p' => U P (t + 1) x' p') '' Set.Icc 0 (min x P.ℓ)) := by
  rw [U]; rfl

lemma U_gt (P : Params) (t : ℕ) (ht : P.T < t) (x p : ℝ) : U P t x p = 0 := by
  rw [U_unfold, if_pos ht]

/-- Linearity of `U` in `x ∈ [0,1]` and `U_t(1,p) = max p (Ro_t p)`. -/
lemma U_lin_aux (P : Params) (hℓ : P.ℓ = 1) :
    ∀ k t, t + k = P.T + 1 →
      (∀ y p, 0 ≤ y → y ≤ 1 → U P t y p = y * U P t 1 p) ∧
      (t ≤ P.T → ∀ p, U P t 1 p = max p (Ro P t p)) := by
  intro k
  induction k with
  | zero =>
    intro t ht
    refine ⟨fun y p _ _ => ?_, fun h => by omega⟩
    rw [U_gt P t (by omega), U_gt P t (by omega)]; ring
  | succ k ih =>
    intro t ht
    have ih' := (ih (t + 1) (by omega)).1
    have key : ∀ y p, 0 ≤ y → y ≤ 1 →
        IsGreatest (objUStep P t y p (fun x' p' => U P (t + 1) x' p') '' Set.Icc 0 (min y P.ℓ))
          (y * max p (Ro P t p)) := by
      intro y p hy0 hy1
      rw [hℓ, min_eq_left hy1]
      have hobj : ∀ q ∈ Set.Icc (0:ℝ) y,
          objUStep P t y p (fun x' p' => U P (t + 1) x' p') q = p * q + (y - q) * Ro P t p := by
        intro q hq
        unfold objUStep Ro
        have : (fun p' => U P (t + 1) (y - q) p') = fun p' => (y - q) * U P (t + 1) 1 p' := by
          funext p'
          exact ih' (y - q) p' (by linarith [hq.2]) (by linarith [hq.1])
        rw [this, integral_const_mul]; ring
      constructor
      · by_cases hpR : Ro P t p ≤ p
        · refine ⟨y, ⟨hy0, le_rfl⟩, ?_⟩
          rw [hobj y ⟨hy0, le_rfl⟩, max_eq_left hpR]; ring
        · refine ⟨0, ⟨le_rfl, hy0⟩, ?_⟩
          rw [hobj 0 ⟨le_rfl, hy0⟩, max_eq_right (le_of_lt (not_le.mp hpR))]; ring
      · rintro v ⟨q, hq, rfl⟩
        rw [hobj q hq]
        have h1 : p ≤ max p (Ro P t p) := le_max_left _ _
        have h2 : Ro P t p ≤ max p (Ro P t p) := le_max_right _ _
        nlinarith [hq.1, hq.2, mul_le_mul_of_nonneg_left h1 hq.1,
          mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hq.2)]
    have hle : t ≤ P.T := by omega
    have hval : ∀ y p, 0 ≤ y → y ≤ 1 → U P t y p = y * max p (Ro P t p) := by
      intro y p hy0 hy1
      rw [U_unfold, if_neg (by omega)]
      exact (key y p hy0 hy1).csSup_eq
    refine ⟨fun y p hy0 hy1 => ?_, fun _ p => ?_⟩
    · rw [hval y p hy0 hy1, hval 1 p zero_le_one le_rfl]; ring
    · rw [hval 1 p zero_le_one le_rfl]; ring

lemma U_lin (P : Params) (hℓ : P.ℓ = 1) (t : ℕ) (y p : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    U P t y p = y * U P t 1 p := by
  by_cases h : P.T < t
  · rw [U_gt P t h, U_gt P t h]; ring
  · exact (U_lin_aux P hℓ (P.T + 1 - t) t (by omega)).1 y p hy0 hy1

lemma U_one (P : Params) (hℓ : P.ℓ = 1) (t : ℕ) (ht : t ≤ P.T) (p : ℝ) :
    U P t 1 p = max p (Ro P t p) :=
  (U_lin_aux P hℓ (P.T + 1 - t) t (by omega)).2 ht p

lemma U_formula (P : Params) (hℓ : P.ℓ = 1) (t : ℕ) (ht : t ≤ P.T) (y p : ℝ) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) : U P t y p = max p (Ro P t p) * y := by
  rw [U_lin P hℓ t y p hy0 hy1, U_one P hℓ t ht]; ring

lemma objU_eq (P : Params) (hℓ : P.ℓ = 1) (t : ℕ) (x p q : ℝ) (hq0 : 0 ≤ q) (hqx : q ≤ x)
    (hx1 : x ≤ 1) : objU P t x p q = p * q + (x - q) * Ro P t p := by
  unfold objU objUStep Ro
  have : (fun p' => U P (t + 1) (x - q) p') = fun p' => (x - q) * U P (t + 1) 1 p' := by
    funext p'
    exact U_lin P hℓ (t + 1) (x - q) p' (by linarith) (by linarith)
  rw [this, integral_const_mul]; ring

lemma Ro_T (P : Params) (p : ℝ) : Ro P P.T p = 0 := by
  unfold Ro
  simp [U_gt P (P.T + 1) (by omega)]

lemma Ro_rec (P : Params) (hℓ : P.ℓ = 1) (t : ℕ) (ht : t < P.T) (p : ℝ) :
    Ro P t p = P.ρ * ∫ p', max p' (Ro P (t + 1) p') ∂(P.κ t p) := by
  unfold Ro
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p' => U_one P hℓ (t + 1) (by omega) p')


/-! ## Part 2: kernels, measurability and integrability of `Ro`. -/

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

/-- Measurability, nonnegativity, bound and integrability for `Ro`. -/
lemma Ro_props_aux (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) :
    ∀ k s, s + k = P.T →
      Measurable (Ro P s) ∧ (∀ y, 0 ≤ Ro P s y) ∧ (∀ y, Ro P s y ≤ Npot P s y) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    have h0 : Ro P s = fun _ => 0 := funext (fun y => by rw [show s = P.T by omega]; exact Ro_T P y)
    refine ⟨by rw [h0]; exact measurable_const, fun y => by rw [h0], fun y => ?_⟩
    rw [h0]; simp [Npot, show P.T - s = 0 by omega]
  | succ k ih =>
    intro s hs
    obtain ⟨ihm, ih0, ihb⟩ := ih (s + 1) (by omega)
    have hsT : s < P.T := by omega
    have hmeasg : Measurable (fun z : ℝ => max z (Ro P (s + 1) z)) := measurable_id.max ihm
    have hrec : Ro P s = fun y => P.ρ * ∫ z, max z (Ro P (s + 1) z) ∂(P.κ s y) :=
      funext (fun y => Ro_rec P hℓ s hsT y)
    have hρ0 : 0 < P.ρ := hS.2.1
    have hρ1 : P.ρ < 1 := hS.2.2.1
    have hint : ∀ y, Integrable (fun z : ℝ => max z (Ro P (s + 1) z)) (P.κ s y) := by
      intro y
      have hI1 : Integrable (fun z : ℝ => |z|) (P.κ s y) := (hS.2.2.2.2.2.2.1 s hsT y).abs
      refine Integrable.mono' (hI1.add (int_Npot P hS s y)) hmeasg.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      rw [Real.norm_eq_abs, Pi.add_apply]
      have := ih0 z; have := ihb z
      rw [abs_le]; constructor
      · have := abs_nonneg z; have := le_max_right z (Ro P (s + 1) z); linarith
      · exact max_le (by linarith [le_abs_self z]) (by linarith [abs_nonneg z])
    have hnn : ∀ y, 0 ≤ ∫ z, max z (Ro P (s + 1) z) ∂(P.κ s y) := fun y =>
      integral_nonneg (fun z => le_trans (ih0 z) (le_max_right _ _))
    refine ⟨?_, fun y => ?_, fun y => ?_⟩
    · rw [hrec]
      exact ((StronglyMeasurable.integral_kernel (κ := P.κ s)
        hmeasg.stronglyMeasurable).measurable).const_mul _
    · rw [hrec]; exact mul_nonneg hρ0.le (hnn y)
    · rw [hrec, ← Npot_rec P hS s hsT y]
      have hI1 : Integrable (fun z : ℝ => |z|) (P.κ s y) := (hS.2.2.2.2.2.2.1 s hsT y).abs
      have hle : ∫ z, max z (Ro P (s + 1) z) ∂(P.κ s y) ≤ ∫ z, (|z| + Npot P (s + 1) z) ∂(P.κ s y) := by
        apply integral_mono (hint y) (hI1.add (int_Npot P hS s y))
        intro z
        have := ih0 z; have := ihb z
        show max z _ ≤ |z| + Npot P (s + 1) z
        exact max_le (by linarith [le_abs_self z]) (by linarith [abs_nonneg z])
      have := hnn y
      nlinarith

lemma Ro_meas (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (s : ℕ) (hs : s ≤ P.T) :
    Measurable (Ro P s) := (Ro_props_aux P hS hℓ (P.T - s) s (by omega)).1

lemma Ro_nonneg (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (s : ℕ) (hs : s ≤ P.T) (y : ℝ) :
    0 ≤ Ro P s y := (Ro_props_aux P hS hℓ (P.T - s) s (by omega)).2.1 y

/-- `Mx s y = max y (Ro s y) = U_s(1, y)`. -/
noncomputable def Mx (P : Params) (s : ℕ) (y : ℝ) : ℝ := max y (Ro P s y)

lemma Mx_meas (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (s : ℕ) (hs : s ≤ P.T) :
    Measurable (Mx P s) := measurable_id.max (Ro_meas P hS hℓ s hs)

lemma Mx_nonneg (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (s : ℕ) (hs : s ≤ P.T) (y : ℝ) :
    0 ≤ Mx P s y := le_trans (Ro_nonneg P hS hℓ s hs y) (le_max_right _ _)

lemma Mx_int (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (s : ℕ) (hs : s < P.T) (y : ℝ) :
    Integrable (Mx P (s + 1)) (P.κ s y) := by
  obtain ⟨ihm, ih0, ihb⟩ := Ro_props_aux P hS hℓ (P.T - (s + 1)) (s + 1) (by omega)
  have hI1 : Integrable (fun z : ℝ => |z|) (P.κ s y) := (hS.2.2.2.2.2.2.1 s hs y).abs
  refine Integrable.mono' (hI1.add (int_Npot P hS s y)) (Mx_meas P hS hℓ (s + 1) (by omega)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply]
  have := ih0 z; have := ihb z
  unfold Mx
  rw [abs_le]; constructor
  · have := abs_nonneg z; have := le_max_right z (Ro P (s + 1) z); linarith
  · exact max_le (by linarith [le_abs_self z]) (by linarith [abs_nonneg z])

lemma Ro_eq_Mx (P : Params) (hℓ : P.ℓ = 1) (s : ℕ) (hs : s < P.T) (y : ℝ) :
    Ro P s y = P.ρ * ∫ z, Mx P (s + 1) z ∂(P.κ s y) := Ro_rec P hℓ s hs y

lemma Ro_pos (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (s : ℕ) (hs : s < P.T) (y : ℝ) :
    0 < Ro P s y := by
  have := hS.2.2.2.2.2.1 s
  rw [Ro_eq_Mx P hℓ s hs]
  refine mul_pos hS.2.1 ?_
  have hI1 : Integrable (fun z : ℝ => z) (P.κ s y) := hS.2.2.2.2.2.2.1 s hs y
  have hpos : 0 < ∫ z, z ∂(P.κ s y) := by
    rw [integral_pos_iff_support_of_nonneg_ae _ hI1]
    · have : (Function.support fun z : ℝ => z) = {z | z ≠ 0} := rfl
      have hae := hS.2.2.2.2.2.2.2.2 s y
      have h1 : (P.κ s y) {z : ℝ | ¬ (z ≠ 0)} = 0 := by
        rw [ae_iff] at hae
        exact measure_mono_null (fun z hz => by simp at hz ⊢; simp [hz]) hae
      have h2 : (P.κ s y) Set.univ ≤ (P.κ s y) {z : ℝ | z ≠ 0} + (P.κ s y) {z : ℝ | ¬ (z ≠ 0)} := by
        calc (P.κ s y) Set.univ = (P.κ s y) ({z : ℝ | z ≠ 0} ∪ {z | ¬ (z ≠ 0)}) := by
              congr 1; ext z; simp [em]
          _ ≤ _ := measure_union_le _ _
      rw [h1, add_zero, measure_univ] at h2
      rw [this]
      exact lt_of_lt_of_le zero_lt_one h2
    · filter_upwards [hS.2.2.2.2.2.2.2.2 s y] with z hz using hz.le
  calc 0 < ∫ z, z ∂(P.κ s y) := hpos
    _ ≤ ∫ z, Mx P (s + 1) z ∂(P.κ s y) :=
      integral_mono hI1 (Mx_int P hS hℓ s hs y) (fun z => le_max_left _ _)


/-! ## Part 3: the explicit candidate value function `Phi`. -/

noncomputable def dl (P : Params) (m : ℕ) (D : ℝ) (s : ℕ) : ℝ := P.ρ ^ (m - s) * D

noncomputable def Phi (P : Params) (m : ℕ) (D : ℝ) : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _, _ => 0
  | n + 1, s, x, w, y =>
    if dl P m D s ≤ w then x * Mx P s y + w - dl P m D s
    else max (P.ρ * ∫ z, Phi P m D n (s + 1) x (P.ρ⁻¹ * w) z ∂(P.κ s y))
      (max (Ro P s y * (x - (dl P m D s - w) / y)) (y * x + w - dl P m D s))

lemma Phi_zero (P : Params) (m : ℕ) (D : ℝ) (s : ℕ) (x w y : ℝ) : Phi P m D 0 s x w y = 0 := rfl

lemma Phi_succ (P : Params) (m : ℕ) (D : ℝ) (n s : ℕ) (x w y : ℝ) : Phi P m D (n + 1) s x w y =
    if dl P m D s ≤ w then x * Mx P s y + w - dl P m D s
    else max (P.ρ * ∫ z, Phi P m D n (s + 1) x (P.ρ⁻¹ * w) z ∂(P.κ s y))
      (max (Ro P s y * (x - (dl P m D s - w) / y)) (y * x + w - dl P m D s)) := rfl

lemma max3_conv {a b u u1 u2 v v1 v2 r r1 r2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : u ≤ a * u1 + b * u2) (hv : v ≤ a * v1 + b * v2) (hr : r ≤ a * r1 + b * r2) :
    max u (max v r) ≤ a * max u1 (max v1 r1) + b * max u2 (max v2 r2) := by
  have h1 : ∀ c c' : ℝ, c ≤ c' → a * c ≤ a * c' := fun c c' h => mul_le_mul_of_nonneg_left h ha
  have h2 : ∀ c c' : ℝ, c ≤ c' → b * c ≤ b * c' := fun c c' h => mul_le_mul_of_nonneg_left h hb
  refine max_le ?_ (max_le ?_ ?_)
  · exact le_trans hu (add_le_add (h1 _ _ (le_max_left _ _)) (h2 _ _ (le_max_left _ _)))
  · exact le_trans hv (add_le_add (h1 _ _ (le_trans (le_max_left _ _) (le_max_right _ _)))
      (h2 _ _ (le_trans (le_max_left _ _) (le_max_right _ _))))
  · exact le_trans hr (add_le_add (h1 _ _ (le_trans (le_max_right _ _) (le_max_right _ _)))
      (h2 _ _ (le_trans (le_max_right _ _) (le_max_right _ _))))

section PhiProps

variable (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (m : ℕ) (hmT : m < P.T) (D : ℝ)
  (hD : 0 ≤ D)

include hS hℓ hmT hD

lemma dl_nonneg (s : ℕ) : 0 ≤ dl P m D s := mul_nonneg (pow_nonneg hS.2.1.le _) hD

lemma dl_succ (s : ℕ) (hs : s < m) : P.ρ⁻¹ * dl P m D s = dl P m D (s + 1) := by
  unfold dl
  have hρ : P.ρ ≠ 0 := hS.2.1.ne'
  rw [show m - s = (m - (s + 1)) + 1 by omega, pow_succ]
  field_simp

lemma Phi_meas : ∀ n s, s + n = m + 1 → ∀ x w, Measurable (Phi P m D n s x w) := by
  intro n
  induction n with
  | zero => intro s _ x w; exact measurable_const
  | succ n ih =>
    intro s hs x w
    have hsT : s ≤ P.T := by omega
    show Measurable (fun y => Phi P m D (n + 1) s x w y)
    simp only [Phi_succ]
    split_ifs with h
    · exact ((measurable_const.mul (Mx_meas P hS hℓ s hsT)).add_const _).sub_const _
    · refine Measurable.max ?_ (Measurable.max ?_ ?_)
      · exact ((StronglyMeasurable.integral_kernel (κ := P.κ s)
          (ih (s + 1) (by omega) x (P.ρ⁻¹ * w)).stronglyMeasurable).measurable).const_mul _
      · exact (Ro_meas P hS hℓ s hsT).mul (measurable_const.sub (measurable_const.div measurable_id))
      · exact ((measurable_id.mul_const x).add_const _).sub_const _

lemma Phi_bounds : ∀ n s, s + n = m + 1 → ∀ x w y, 0 ≤ x → x ≤ 1 → 0 ≤ w → 0 < y →
    0 ≤ Phi P m D n s x w y ∧ Phi P m D n s x w y ≤ Mx P s y + w := by
  intro n
  induction n with
  | zero =>
    intro s hs x w y _ _ hw _
    rw [Phi_zero]
    exact ⟨le_rfl, by linarith [Mx_nonneg P hS hℓ s (by omega) y]⟩
  | succ n ih =>
    intro s hs x w y hx0 hx1 hw hy
    have hsT : s < P.T := by omega
    have hMx := Mx_nonneg P hS hℓ s hsT.le y
    have hRo := Ro_nonneg P hS hℓ s hsT.le y
    have hdl := dl_nonneg P hS hℓ m hmT D hD s
    have hyM : y ≤ Mx P s y := le_max_left _ _
    have hRM : Ro P s y ≤ Mx P s y := le_max_right _ _
    rw [Phi_succ]
    split_ifs with h
    · constructor
      · nlinarith [mul_nonneg hx0 hMx]
      · nlinarith [mul_le_mul_of_nonneg_right hx1 hMx]
    · have hρ0 : 0 < P.ρ := hS.2.1
      have hw' : 0 ≤ P.ρ⁻¹ * w := mul_nonneg (inv_nonneg.mpr hρ0.le) hw
      have hae := hS.2.2.2.2.2.2.2.2 s y
      have : IsMarkovKernel (P.κ s) := hS.2.2.2.2.2.1 s
      have hC0 : 0 ≤ P.ρ * ∫ z, Phi P m D n (s + 1) x (P.ρ⁻¹ * w) z ∂(P.κ s y) := by
        refine mul_nonneg hρ0.le (integral_nonneg_of_ae ?_)
        filter_upwards [hae] with z hz
        exact (ih (s + 1) (by omega) x _ z hx0 hx1 hw' hz).1
      constructor
      · exact le_trans hC0 (le_max_left _ _)
      · refine max_le ?_ (max_le ?_ ?_)
        · have hI : Integrable (fun z => Mx P (s + 1) z + P.ρ⁻¹ * w) (P.κ s y) :=
            (Mx_int P hS hℓ s hsT y).add (integrable_const _)
          have hle : ∫ z, Phi P m D n (s + 1) x (P.ρ⁻¹ * w) z ∂(P.κ s y) ≤
              ∫ z, (Mx P (s + 1) z + P.ρ⁻¹ * w) ∂(P.κ s y) := by
            apply integral_mono_of_nonneg
            · filter_upwards [hae] with z hz
              exact (ih (s + 1) (by omega) x _ z hx0 hx1 hw' hz).1
            · exact hI
            · filter_upwards [hae] with z hz
              exact (ih (s + 1) (by omega) x _ z hx0 hx1 hw' hz).2
          rw [integral_add (Mx_int P hS hℓ s hsT y) (integrable_const _)] at hle
          simp only [integral_const, probReal_univ, one_smul] at hle
          have hR := Ro_eq_Mx P hℓ s hsT y
          have : P.ρ * (P.ρ⁻¹ * w) = w := by field_simp
          nlinarith [mul_le_mul_of_nonneg_left hle hρ0.le]
        · have he : 0 ≤ (dl P m D s - w) / y := div_nonneg (by linarith) hy.le
          have : Ro P s y * (x - (dl P m D s - w) / y) ≤ Ro P s y * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) hRo
          linarith
        · nlinarith [mul_le_mul_of_nonneg_left hx1 hy.le]

lemma Phi_int (n s : ℕ) (hs : s + 1 + n = m + 1) (x w : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hw : 0 ≤ w) (y : ℝ) : Integrable (Phi P m D n (s + 1) x w) (P.κ s y) := by
  have hsT : s < P.T := by omega
  have := hS.2.2.2.2.2.1 s
  refine Integrable.mono' ((Mx_int P hS hℓ s hsT y).add (integrable_const w))
    (Phi_meas P hS hℓ m hmT D hD n (s + 1) hs x w).aestronglyMeasurable ?_
  filter_upwards [hS.2.2.2.2.2.2.2.2 s y] with z hz
  obtain ⟨h0, h1⟩ := Phi_bounds P hS hℓ m hmT D hD n (s + 1) hs x w z hx0 hx1 hw hz
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- The max-form of `Phi` holds on the whole region `w ≤ dl s` (including the boundary). -/
lemma Phi_maxform (n s : ℕ) (hs : s + (n + 1) = m + 1) (x w y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hw : 0 ≤ w) (hwd : w ≤ dl P m D s) (hy : 0 < y) :
    Phi P m D (n + 1) s x w y =
    max (P.ρ * ∫ z, Phi P m D n (s + 1) x (P.ρ⁻¹ * w) z ∂(P.κ s y))
      (max (Ro P s y * (x - (dl P m D s - w) / y)) (y * x + w - dl P m D s)) := by
  rw [Phi_succ]
  split_ifs with h
  · have hweq : w = dl P m D s := le_antisymm hwd h
    subst hweq
    have hsT : s < P.T := by omega
    have hC : P.ρ * ∫ z, Phi P m D n (s + 1) x (P.ρ⁻¹ * dl P m D s) z ∂(P.κ s y) ≤
        Ro P s y * x := by
      cases n with
      | zero =>
        simp only [Phi_zero, integral_zero, mul_zero]
        exact mul_nonneg (Ro_nonneg P hS hℓ s hsT.le y) hx0
      | succ n =>
        have hsm : s < m := by omega
        rw [dl_succ P hS hℓ m hmT D hD s hsm]
        have : (fun z => Phi P m D (n + 1) (s + 1) x (dl P m D (s + 1)) z) =
            fun z => x * Mx P (s + 1) z := by
          funext z; rw [Phi_succ, if_pos le_rfl]; ring
        rw [this, integral_const_mul, Ro_eq_Mx P hℓ s hsT y]; apply le_of_eq; ring
    simp only [sub_self, zero_div, sub_zero, add_sub_cancel_right]
    rw [max_eq_right (le_trans hC (le_max_left _ _))]
    unfold Mx
    rw [mul_comm (Ro P s y) x, mul_comm y x, ← mul_max_of_nonneg _ _ hx0, max_comm]
  · rfl

lemma Phi_conv : ∀ n s, s + n = m + 1 → ∀ y, 0 < y → ∀ x1 w1 x2 w2 a b : ℝ,
    0 ≤ x1 → x1 ≤ 1 → 0 ≤ x2 → x2 ≤ 1 → 0 ≤ w1 → w1 ≤ dl P m D s → 0 ≤ w2 → w2 ≤ dl P m D s →
    0 ≤ a → 0 ≤ b → a + b = 1 →
    Phi P m D n s (a * x1 + b * x2) (a * w1 + b * w2) y ≤
      a * Phi P m D n s x1 w1 y + b * Phi P m D n s x2 w2 y := by
  intro n
  induction n with
  | zero => intro s _ y _ x1 w1 x2 w2 a b _ _ _ _ _ _ _ _ _ _ _; simp [Phi_zero]
  | succ n ih =>
    intro s hs y hy x1 w1 x2 w2 a b hx10 hx11 hx20 hx21 hw10 hw1d hw20 hw2d ha hb hab
    have hb' : b = 1 - a := by linarith
    have hx0 : 0 ≤ a * x1 + b * x2 := by positivity
    have hx1 : a * x1 + b * x2 ≤ 1 := by nlinarith
    have hw0 : 0 ≤ a * w1 + b * w2 := by positivity
    have hwd : a * w1 + b * w2 ≤ dl P m D s := by nlinarith
    rw [Phi_maxform P hS hℓ m hmT D hD n s hs _ _ y hx0 hx1 hw0 hwd hy,
      Phi_maxform P hS hℓ m hmT D hD n s hs _ _ y hx10 hx11 hw10 hw1d hy,
      Phi_maxform P hS hℓ m hmT D hD n s hs _ _ y hx20 hx21 hw20 hw2d hy]
    refine max3_conv ha hb ?_ ?_ ?_
    · cases n with
      | zero => simp [Phi_zero]
      | succ n =>
        have hsm : s < m := by omega
        have hsT : s < P.T := by omega
        have hρ0 : 0 < P.ρ := hS.2.1
        have hρi : 0 < P.ρ⁻¹ := inv_pos.mpr hρ0
        have := hS.2.2.2.2.2.1 s
        have hdl := dl_succ P hS hℓ m hmT D hD s hsm
        have hI1 := Phi_int P hS hℓ m hmT D hD (n + 1) s (by omega) x1 (P.ρ⁻¹ * w1) hx10 hx11
          (by positivity) y
        have hI2 := Phi_int P hS hℓ m hmT D hD (n + 1) s (by omega) x2 (P.ρ⁻¹ * w2) hx20 hx21
          (by positivity) y
        have hle : ∫ z, Phi P m D (n + 1) (s + 1) (a * x1 + b * x2) (P.ρ⁻¹ * (a * w1 + b * w2)) z
            ∂(P.κ s y) ≤ ∫ z, (a * Phi P m D (n + 1) (s + 1) x1 (P.ρ⁻¹ * w1) z +
              b * Phi P m D (n + 1) (s + 1) x2 (P.ρ⁻¹ * w2) z) ∂(P.κ s y) := by
          apply integral_mono_of_nonneg
          · filter_upwards [hS.2.2.2.2.2.2.2.2 s y] with z hz
            exact (Phi_bounds P hS hℓ m hmT D hD (n + 1) (s + 1) (by omega) _ _ z hx0 hx1
              (by positivity) hz).1
          · exact (hI1.const_mul a).add (hI2.const_mul b)
          · filter_upwards [hS.2.2.2.2.2.2.2.2 s y] with z hz
            rw [show P.ρ⁻¹ * (a * w1 + b * w2) = a * (P.ρ⁻¹ * w1) + b * (P.ρ⁻¹ * w2) by ring]
            refine ih (s + 1) (by omega) z hz x1 _ x2 _ a b hx10 hx11 hx20 hx21 (by positivity)
              ?_ (by positivity) ?_ ha hb hab
            · rw [← hdl]; exact mul_le_mul_of_nonneg_left hw1d hρi.le
            · rw [← hdl]; exact mul_le_mul_of_nonneg_left hw2d hρi.le
        rw [integral_add (hI1.const_mul a) (hI2.const_mul b), integral_const_mul,
          integral_const_mul] at hle
        nlinarith [mul_le_mul_of_nonneg_left hle hρ0.le]
    · apply le_of_eq; rw [hb']; ring
    · apply le_of_eq; rw [hb']; ring

lemma Phi_zero_x : ∀ n s, s + n = m + 1 → ∀ w y, 0 ≤ w → w < dl P m D s → 0 < y →
    Phi P m D n s 0 w y = 0 := by
  intro n
  induction n with
  | zero => intro s _ w y _ _ _; rfl
  | succ n ih =>
    intro s hs w y hw hwd hy
    have hsT : s < P.T := by omega
    rw [Phi_succ, if_neg (not_le.mpr hwd)]
    have hC : P.ρ * ∫ z, Phi P m D n (s + 1) 0 (P.ρ⁻¹ * w) z ∂(P.κ s y) = 0 := by
      cases n with
      | zero => simp [Phi_zero]
      | succ n =>
        have hsm : s < m := by omega
        have hρi : 0 < P.ρ⁻¹ := inv_pos.mpr hS.2.1
        have hdl := dl_succ P hS hℓ m hmT D hD s hsm
        have : (fun z => Phi P m D (n + 1) (s + 1) 0 (P.ρ⁻¹ * w) z) =ᵐ[P.κ s y] fun _ => 0 := by
          filter_upwards [hS.2.2.2.2.2.2.2.2 s y] with z hz
          refine ih (s + 1) (by omega) _ z (by positivity) ?_ hz
          rw [← hdl]; exact mul_lt_mul_of_pos_left hwd hρi
        rw [integral_congr_ae this]; simp
    rw [hC]
    have hRo := Ro_nonneg P hS hℓ s hsT.le y
    have he : 0 ≤ (dl P m D s - w) / y := div_nonneg (by linarith) hy.le
    apply max_eq_left
    refine max_le ?_ (by linarith)
    nlinarith [mul_nonneg hRo he]

end PhiProps


/-! ## Part 4: the equity value `V` equals `Phi`. -/

lemma V_unfold (P : Params) (d : ℕ → ℝ) (m t : ℕ) (x w p : ℝ) : V P d m t x w p =
    if m < t then 0 else if p * min x P.ℓ + w < d t then 0
    else sSup (objV P d m t x w p '' {q | Feasible P d t x w p q}) := by
  rw [V]; rfl

lemma V_gt (P : Params) (d : ℕ → ℝ) (m t : ℕ) (ht : m < t) (x w p : ℝ) : V P d m t x w p = 0 := by
  rw [V_unfold, if_pos ht]

lemma sp_ne (m : ℕ) (D : ℝ) (s : ℕ) (h : s ≠ m) : singlePayment m D s = 0 := by
  simp [singlePayment, h]

lemma sp_eq (m : ℕ) (D : ℝ) : singlePayment m D m = D := by simp [singlePayment]

section VPhi

variable (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (m : ℕ) (hmT : m < P.T) (D : ℝ)
  (hD : 0 ≤ D)

include hS hℓ hmT hD

lemma objV_lt (n s : ℕ) (hsm : s < m)
    (IH : ∀ x' w' z, 0 ≤ x' → x' ≤ 1 → 0 ≤ w' → 0 < z →
      V P (singlePayment m D) m (s + 1) x' w' z = Phi P m D n (s + 1) x' w' z)
    (x w p q : ℝ) (hq0 : 0 ≤ q) (hqx : q ≤ x) (hx1 : x ≤ 1) (hw : 0 ≤ w) (hp : 0 < p) :
    objV P (singlePayment m D) m s x w p q =
      P.ρ * ∫ z, Phi P m D n (s + 1) (x - q) (P.ρ⁻¹ * (w + p * q)) z ∂(P.κ s p) := by
  unfold objV objVStep
  rw [if_neg (by omega), sp_ne m D s (by omega), sub_zero]
  congr 1
  apply integral_congr_ae
  filter_upwards [hS.2.2.2.2.2.2.2.2 s p] with z hz
  exact IH _ _ z (by linarith) (by linarith) (mul_nonneg (inv_nonneg.mpr hS.2.1.le)
    (by nlinarith)) hz

lemma objV_m (x w p q : ℝ) (hq0 : 0 ≤ q) (hqx : q ≤ x) (hx1 : x ≤ 1) :
    objV P (singlePayment m D) m m x w p q = p * q + (x - q) * Ro P m p + w - D := by
  unfold objV objVStep
  rw [if_pos rfl, sp_eq, objU_eq P hℓ m x p q hq0 hqx hx1]

/-- Linear evaluation once the debt is secured. -/
lemma objV_lin (n s : ℕ) (hs : s + (n + 1 + 1) = m + 1)
    (IH : ∀ x' w' z, 0 ≤ x' → x' ≤ 1 → 0 ≤ w' → 0 < z →
      V P (singlePayment m D) m (s + 1) x' w' z = Phi P m D (n + 1) (s + 1) x' w' z)
    (x w p q : ℝ) (hq0 : 0 ≤ q) (hqx : q ≤ x) (hx1 : x ≤ 1) (hw : 0 ≤ w) (hp : 0 < p)
    (hsec : dl P m D s ≤ w + p * q) :
    objV P (singlePayment m D) m s x w p q = (x - q) * Ro P s p + (w + p * q) - dl P m D s := by
  have hsm : s < m := by omega
  have hsT : s < P.T := by omega
  have := hS.2.2.2.2.2.1 s
  have hρ0 : 0 < P.ρ := hS.2.1
  have hdl := dl_succ P hS hℓ m hmT D hD s hsm
  rw [objV_lt P hS hℓ m hmT D hD (n + 1) s hsm IH x w p q hq0 hqx hx1 hw hp]
  have hge : dl P m D (s + 1) ≤ P.ρ⁻¹ * (w + p * q) := by
    rw [← hdl]; exact mul_le_mul_of_nonneg_left hsec (inv_nonneg.mpr hρ0.le)
  have hfun : (fun z => Phi P m D (n + 1) (s + 1) (x - q) (P.ρ⁻¹ * (w + p * q)) z) =
      fun z => (x - q) * Mx P (s + 1) z + (P.ρ⁻¹ * (w + p * q) - dl P m D (s + 1)) := by
    funext z; rw [Phi_succ, if_pos hge]; ring
  rw [hfun, integral_add ((Mx_int P hS hℓ s hsT p).const_mul _) (integrable_const _),
    integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  rw [Ro_eq_Mx P hℓ s hsT p, ← hdl]
  field_simp
  ring

/-- Convexity bound along the selling segment before the debt is secured. -/
lemma objV_conv (n s : ℕ) (hs : s + (n + 1) = m + 1) (hsm : s < m)
    (IH : ∀ x' w' z, 0 ≤ x' → x' ≤ 1 → 0 ≤ w' → 0 < z →
      V P (singlePayment m D) m (s + 1) x' w' z = Phi P m D n (s + 1) x' w' z)
    (x w p q q1 : ℝ) (hq0 : 0 ≤ q) (hqq1 : q ≤ q1) (hq1x : q1 ≤ x) (hx1 : x ≤ 1) (hw : 0 ≤ w)
    (hp : 0 < p) (hq1d : w + p * q1 ≤ dl P m D s) :
    objV P (singlePayment m D) m s x w p q ≤
      max (objV P (singlePayment m D) m s x w p 0) (objV P (singlePayment m D) m s x w p q1) := by
  have hsT : s < P.T := by omega
  have := hS.2.2.2.2.2.1 s
  have hρ0 : 0 < P.ρ := hS.2.1
  have hρi : 0 < P.ρ⁻¹ := inv_pos.mpr hρ0
  have hdl := dl_succ P hS hℓ m hmT D hD s hsm
  rcases eq_or_lt_of_le (le_trans hq0 hqq1) with h1 | h1
  · have : q = 0 := by linarith
    rw [this]; exact le_max_left _ _
  set b := q / q1 with hbdef
  set a := 1 - b with hadef
  have hb0 : 0 ≤ b := div_nonneg hq0 h1.le
  have hb1 : b ≤ 1 := (div_le_one h1).mpr hqq1
  have hbq : b * q1 = q := by rw [hbdef]; field_simp
  have hx0 : 0 ≤ x := by linarith
  rw [objV_lt P hS hℓ m hmT D hD n s hsm IH x w p q hq0 (by linarith) hx1 hw hp,
    objV_lt P hS hℓ m hmT D hD n s hsm IH x w p 0 le_rfl hx0 hx1 hw hp,
    objV_lt P hS hℓ m hmT D hD n s hsm IH x w p q1 (by linarith) hq1x hx1 hw hp]
  have hI0 := Phi_int P hS hℓ m hmT D hD n s (by omega) (x - 0) (P.ρ⁻¹ * (w + p * 0))
    (by linarith) (by linarith) (by positivity) p
  have hI1 := Phi_int P hS hℓ m hmT D hD n s (by omega) (x - q1) (P.ρ⁻¹ * (w + p * q1))
    (by linarith) (by linarith) (by positivity) p
  have hle : ∫ z, Phi P m D n (s + 1) (x - q) (P.ρ⁻¹ * (w + p * q)) z ∂(P.κ s p) ≤
      ∫ z, (a * Phi P m D n (s + 1) (x - 0) (P.ρ⁻¹ * (w + p * 0)) z +
        b * Phi P m D n (s + 1) (x - q1) (P.ρ⁻¹ * (w + p * q1)) z) ∂(P.κ s p) := by
    apply integral_mono_of_nonneg
    · filter_upwards [hS.2.2.2.2.2.2.2.2 s p] with z hz
      exact (Phi_bounds P hS hℓ m hmT D hD n (s + 1) (by omega) _ _ z (by linarith) (by linarith)
        (by positivity) hz).1
    · exact (hI0.const_mul a).add (hI1.const_mul b)
    · filter_upwards [hS.2.2.2.2.2.2.2.2 s p] with z hz
      have e1 : x - q = a * (x - 0) + b * (x - q1) := by rw [hadef]; nlinarith
      have e2 : P.ρ⁻¹ * (w + p * q) = a * (P.ρ⁻¹ * (w + p * 0)) + b * (P.ρ⁻¹ * (w + p * q1)) := by
        rw [hadef, ← hbq]; ring
      rw [e1, e2]
      have hwd0 : P.ρ⁻¹ * (w + p * 0) ≤ dl P m D (s + 1) := by
        rw [← hdl]; exact mul_le_mul_of_nonneg_left (by nlinarith) hρi.le
      have hwd1 : P.ρ⁻¹ * (w + p * q1) ≤ dl P m D (s + 1) := by
        rw [← hdl]; exact mul_le_mul_of_nonneg_left hq1d hρi.le
      exact Phi_conv P hS hℓ m hmT D hD n (s + 1) (by omega) z hz _ _ _ _ a b (by linarith)
        (by linarith) (by linarith) (by linarith) (by positivity) hwd0 (by positivity) hwd1
        (by linarith) hb0 (by ring)
  rw [integral_add (hI0.const_mul a) (hI1.const_mul b), integral_const_mul,
    integral_const_mul] at hle
  set G0 := ∫ z, Phi P m D n (s + 1) (x - 0) (P.ρ⁻¹ * (w + p * 0)) z ∂(P.κ s p)
  set G1 := ∫ z, Phi P m D n (s + 1) (x - q1) (P.ρ⁻¹ * (w + p * q1)) z ∂(P.κ s p)
  have hm0 : P.ρ * G0 ≤ max (P.ρ * G0) (P.ρ * G1) := le_max_left _ _
  have hm1 : P.ρ * G1 ≤ max (P.ρ * G0) (P.ρ * G1) := le_max_right _ _
  have ha0 : 0 ≤ a := by rw [hadef]; linarith
  nlinarith [mul_le_mul_of_nonneg_left hle hρ0.le, mul_le_mul_of_nonneg_left hm0 ha0,
    mul_le_mul_of_nonneg_left hm1 hb0]

/-- The one-period step before maturity: `Phi` is the maximum of the objective over `[0, x]`. -/
lemma step_lt (n s : ℕ) (hs : s + (n + 1 + 1) = m + 1)
    (IH : ∀ x' w' z, 0 ≤ x' → x' ≤ 1 → 0 ≤ w' → 0 < z →
      V P (singlePayment m D) m (s + 1) x' w' z = Phi P m D (n + 1) (s + 1) x' w' z)
    (x w p : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hw : 0 ≤ w) (hp : 0 < p) :
    (∀ q, 0 ≤ q → q ≤ x → objV P (singlePayment m D) m s x w p q ≤ Phi P m D (n + 1 + 1) s x w p) ∧
    (∃ q, 0 ≤ q ∧ q ≤ x ∧ objV P (singlePayment m D) m s x w p q = Phi P m D (n + 1 + 1) s x w p) := by
  have hsm : s < m := by omega
  have hsT : s < P.T := by omega
  have hRo := Ro_nonneg P hS hℓ s hsT.le p
  have hρ0 : 0 < P.ρ := hS.2.1
  have hρi : 0 < P.ρ⁻¹ := inv_pos.mpr hρ0
  have hdl := dl_succ P hS hℓ m hmT D hD s hsm
  have := hS.2.2.2.2.2.1 s
  have hlin := objV_lin P hS hℓ m hmT D hD n s hs IH x w p
  by_cases hwd : dl P m D s ≤ w
  · -- debt already secured: linear objective
    have hPhi : Phi P m D (n + 1 + 1) s x w p = x * Mx P s p + w - dl P m D s := by
      rw [Phi_succ, if_pos hwd]
    rw [hPhi]
    refine ⟨fun q hq0 hqx => ?_, ?_⟩
    · rw [hlin q hq0 hqx hx1 hw hp (by nlinarith)]
      have h1 : p ≤ Mx P s p := le_max_left _ _
      have h2 : Ro P s p ≤ Mx P s p := le_max_right _ _
      nlinarith [mul_le_mul_of_nonneg_left h1 hq0, mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hqx)]
    · by_cases hpR : Ro P s p ≤ p
      · refine ⟨x, hx0, le_rfl, ?_⟩
        rw [hlin x hx0 le_rfl hx1 hw hp (by nlinarith)]
        unfold Mx; rw [max_eq_left hpR]; ring
      · refine ⟨0, le_rfl, hx0, ?_⟩
        rw [hlin 0 le_rfl hx0 hx1 hw hp (by nlinarith)]
        unfold Mx; rw [max_eq_right (le_of_lt (not_le.mp hpR))]; ring
  · have hwd' : w < dl P m D s := lt_of_not_ge hwd
    set e := dl P m D s - w with he
    have he0 : 0 < e := by rw [he]; linarith
    set u := e / p with hu
    have hpu : p * u = e := by rw [hu]; field_simp
    have hu0 : 0 < u := div_pos he0 hp
    have hPhi : Phi P m D (n + 1 + 1) s x w p =
        max (objV P (singlePayment m D) m s x w p 0)
          (max (Ro P s p * (x - u)) (p * x + w - dl P m D s)) := by
      rw [Phi_succ, if_neg hwd, objV_lt P hS hℓ m hmT D hD (n + 1) s hsm IH x w p 0 le_rfl hx0 hx1
        hw hp]
      simp only [sub_zero, mul_zero, add_zero, hu, he]
    have hC0 : 0 ≤ objV P (singlePayment m D) m s x w p 0 := by
      rw [objV_lt P hS hℓ m hmT D hD (n + 1) s hsm IH x w p 0 le_rfl hx0 hx1 hw hp]
      refine mul_nonneg hρ0.le (integral_nonneg_of_ae ?_)
      filter_upwards [hS.2.2.2.2.2.2.2.2 s p] with z hz
      exact (Phi_bounds P hS hℓ m hmT D hD (n + 1) (s + 1) (by omega) _ _ z (by linarith)
        (by linarith) (by positivity) hz).1
    -- value at `q = u` when `u ≤ x`
    have hvalu : u ≤ x → objV P (singlePayment m D) m s x w p u = Ro P s p * (x - u) := by
      intro hux
      rw [hlin u hu0.le hux hx1 hw hp (by rw [hpu, he]; linarith), hpu, he]; ring
    have hvalx : u ≤ x → objV P (singlePayment m D) m s x w p x = p * x + w - dl P m D s := by
      intro hux
      have : e ≤ p * x := by rw [← hpu]; exact mul_le_mul_of_nonneg_left hux hp.le
      rw [hlin x hx0 le_rfl hx1 hw hp (by rw [he] at this; linarith)]; ring
    have hval0 : x < u → objV P (singlePayment m D) m s x w p x = 0 := by
      intro hxu
      have hpx : p * x < e := by rw [← hpu]; exact mul_lt_mul_of_pos_left hxu hp
      rw [objV_lt P hS hℓ m hmT D hD (n + 1) s hsm IH x w p x hx0 le_rfl hx1 hw hp]
      have : (fun z => Phi P m D (n + 1) (s + 1) (x - x) (P.ρ⁻¹ * (w + p * x)) z) =ᵐ[P.κ s p]
          fun _ => 0 := by
        filter_upwards [hS.2.2.2.2.2.2.2.2 s p] with z hz
        rw [sub_self]
        refine Phi_zero_x P hS hℓ m hmT D hD (n + 1) (s + 1) (by omega) _ z (by positivity) ?_ hz
        rw [← hdl]; exact mul_lt_mul_of_pos_left (by rw [he] at hpx; linarith) hρi
      rw [integral_congr_ae this]; simp
    rw [hPhi]
    refine ⟨fun q hq0 hqx => ?_, ?_⟩
    · by_cases hqu : w + p * q ≤ dl P m D s
      · have hq1 : q ≤ min x u := le_min hqx (by
          rw [hu, le_div_iff₀ hp]; rw [he]; linarith)
        have hb := objV_conv P hS hℓ m hmT D hD (n + 1) s (by omega) hsm IH x w p q (min x u) hq0
          hq1 (min_le_left _ _) hx1 hw hp (by
            have : p * min x u ≤ p * u := mul_le_mul_of_nonneg_left (min_le_right _ _) hp.le
            rw [hpu, he] at this; linarith)
        refine le_trans hb (max_le (le_max_left _ _) ?_)
        rcases le_or_gt u x with hux | hxu
        · rw [min_eq_right hux, hvalu hux]
          exact le_trans (le_max_left _ _) (le_max_right _ _)
        · rw [min_eq_left hxu.le, hval0 hxu]
          exact le_trans hC0 (le_max_left _ _)
      · rw [hlin q hq0 hqx hx1 hw hp (by linarith)]
        refine le_trans ?_ (le_max_right _ _)
        have hqu' : u ≤ q := by
          rw [hu, div_le_iff₀ hp, he]; linarith
        by_cases hpR : Ro P s p ≤ p
        · refine le_trans ?_ (le_max_right _ _)
          nlinarith [mul_le_mul_of_nonneg_left hpR (sub_nonneg.mpr hqx)]
        · refine le_trans ?_ (le_max_left _ _)
          have hpR' : p ≤ Ro P s p := le_of_lt (not_le.mp hpR)
          have : (x - q) * Ro P s p + (w + p * q) - dl P m D s - Ro P s p * (x - u) =
              (q - u) * (p - Ro P s p) := by
            have : w - dl P m D s = - (p * u) := by rw [hpu, he]; ring
            linear_combination this
          nlinarith [mul_le_mul_of_nonneg_left hpR' (sub_nonneg.mpr hqu')]
    · rcases le_or_gt u x with hux | hxu
      · rcases max_choice (objV P (singlePayment m D) m s x w p 0)
            (max (Ro P s p * (x - u)) (p * x + w - dl P m D s)) with h | h
        · exact ⟨0, le_rfl, hx0, h.symm⟩
        · rw [h]
          rcases max_choice (Ro P s p * (x - u)) (p * x + w - dl P m D s) with h' | h'
          · exact ⟨u, hu0.le, hux, by rw [h', hvalu hux]⟩
          · exact ⟨x, hx0, le_rfl, by rw [h', hvalx hux]⟩
      · refine ⟨0, le_rfl, hx0, ?_⟩
        symm; apply max_eq_left
        refine max_le ?_ ?_
        · nlinarith [mul_nonneg hRo (sub_nonneg.mpr hxu.le)]
        · have : p * x < e := by rw [← hpu]; exact mul_lt_mul_of_pos_left hxu hp
          rw [he] at this; linarith

lemma dl_m : dl P m D m = D := by simp [dl]

lemma step_eq (x w p : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hw : 0 ≤ w) (hp : 0 < p) :
    V P (singlePayment m D) m m x w p = Phi P m D 1 m x w p := by
  have hmT' : m ≤ P.T := hmT.le
  have hRo := Ro_nonneg P hS hℓ m hmT' p
  have hdm := dl_m P hS hℓ m hmT D hD
  rw [V_unfold, if_neg (lt_irrefl m), hℓ, min_eq_left hx1, sp_eq]
  rw [show (1 : ℕ) = 0 + 1 from rfl, Phi_succ, hdm]
  simp only [Phi_zero, integral_zero, mul_zero]
  by_cases hb : p * x + w < D
  · rw [if_pos hb, if_neg (by nlinarith)]
    symm; apply max_eq_left
    refine max_le ?_ (by linarith)
    have : x - (D - w) / p ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hp]; linarith
    nlinarith
  · rw [if_neg hb]
    have hobj := objV_m P hS hℓ m hmT D hD x w p
    have hfeas : ∀ q, Feasible P (singlePayment m D) m x w p q ↔ 0 ≤ q ∧ q ≤ x ∧ D ≤ w + p * q := by
      intro q; unfold Feasible; rw [hℓ, min_eq_left hx1, sp_eq]
    apply IsGreatest.csSup_eq
    by_cases hwD : D ≤ w
    · rw [if_pos hwD]
      constructor
      · by_cases hpR : Ro P m p ≤ p
        · refine ⟨x, (hfeas x).2 ⟨hx0, le_rfl, by nlinarith⟩, ?_⟩
          rw [hobj x hx0 le_rfl hx1]; unfold Mx; rw [max_eq_left hpR]; ring
        · refine ⟨0, (hfeas 0).2 ⟨le_rfl, hx0, by linarith⟩, ?_⟩
          rw [hobj 0 le_rfl hx0 hx1]; unfold Mx; rw [max_eq_right (le_of_lt (not_le.mp hpR))]; ring
      · rintro v ⟨q, hq, rfl⟩
        obtain ⟨hq0, hqx, _⟩ := (hfeas q).1 hq
        rw [hobj q hq0 hqx hx1]
        have h1 : p ≤ Mx P m p := le_max_left _ _
        have h2 : Ro P m p ≤ Mx P m p := le_max_right _ _
        nlinarith [mul_le_mul_of_nonneg_left h1 hq0, mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hqx)]
    · rw [if_neg hwD]
      set u := (D - w) / p with hu
      have hpu : p * u = D - w := by rw [hu]; field_simp
      have hux : u ≤ x := by rw [hu, div_le_iff₀ hp]; linarith
      have hu0 : 0 ≤ u := div_nonneg (by linarith) hp.le
      have hB0 : 0 ≤ p * x + w - D := by linarith
      clear_value u
      rw [max_eq_right (le_trans hB0 (le_max_right _ _))]
      constructor
      · rcases max_choice (Ro P m p * (x - u)) (p * x + w - D) with h' | h'
        · refine ⟨u, (hfeas u).2 ⟨hu0, hux, by linarith⟩, ?_⟩
          rw [h', hobj u hu0 hux hx1, hpu]; ring
        · refine ⟨x, (hfeas x).2 ⟨hx0, le_rfl, by linarith⟩, ?_⟩
          rw [h', hobj x hx0 le_rfl hx1]; ring
      · rintro v ⟨q, hq, rfl⟩
        obtain ⟨hq0, hqx, hqD⟩ := (hfeas q).1 hq
        rw [hobj q hq0 hqx hx1]
        have hqu' : u ≤ q := le_of_mul_le_mul_left (by linarith : p * u ≤ p * q) hp
        by_cases hpR : Ro P m p ≤ p
        · refine le_trans ?_ (le_max_right _ _)
          nlinarith [mul_le_mul_of_nonneg_left hpR (sub_nonneg.mpr hqx)]
        · refine le_trans ?_ (le_max_left _ _)
          have hpR' : p ≤ Ro P m p := le_of_lt (not_le.mp hpR)
          have : p * q + (x - q) * Ro P m p + w - D - Ro P m p * (x - u) =
              (q - u) * (p - Ro P m p) := by
            linear_combination hpu
          nlinarith [mul_le_mul_of_nonneg_left hpR' (sub_nonneg.mpr hqu')]

lemma V_eq_Phi : ∀ n s, s + n = m + 1 → ∀ x w y, 0 ≤ x → x ≤ 1 → 0 ≤ w → 0 < y →
    V P (singlePayment m D) m s x w y = Phi P m D n s x w y := by
  intro n
  induction n with
  | zero => intro s hs x w y _ _ _ _; rw [V_gt _ _ _ _ (by omega), Phi_zero]
  | succ n ih =>
    intro s hs x w y hx0 hx1 hw hy
    cases n with
    | zero =>
      have hsm : s = m := by omega
      subst hsm
      exact step_eq P hS hℓ s hmT D hD x w y hx0 hx1 hw hy
    | succ n =>
      have hsm : s < m := by omega
      have IH := ih (s + 1) (by omega)
      obtain ⟨hub, q, hq0, hqx, hqv⟩ := step_lt P hS hℓ m hmT D hD n s hs IH x w y hx0 hx1 hw hy
      have hfeas : ∀ q, Feasible P (singlePayment m D) s x w y q ↔ 0 ≤ q ∧ q ≤ x := by
        intro q; unfold Feasible; rw [hℓ, min_eq_left hx1, sp_ne m D s (by omega)]
        constructor
        · rintro ⟨a, b, _⟩; exact ⟨a, b⟩
        · rintro ⟨a, b⟩; exact ⟨a, b, by nlinarith⟩
      rw [V_unfold, if_neg (by omega), if_neg (by rw [hℓ, min_eq_left hx1, sp_ne m D s (by omega)]; nlinarith)]
      apply IsGreatest.csSup_eq
      refine ⟨⟨q, (hfeas q).2 ⟨hq0, hqx⟩, hqv⟩, ?_⟩
      rintro v ⟨q', hq', rfl⟩
      obtain ⟨a, b⟩ := (hfeas q').1 hq'
      exact hub q' a b

end VPhi


/-! ## Part 5: the state `(1, 0)` and the proposition. -/

lemma integral_lt_of_ae_lt {μ : Measure ℝ} [IsProbabilityMeasure μ] {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ᵐ z ∂μ, f z < g z) :
    ∫ z, f z ∂μ < ∫ z, g z ∂μ := by
  have hpos : 0 < ∫ z, (g - f) z ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae _ (hg.sub hf)]
    · have h1 : μ {z | ¬ ((g - f) z ≠ 0)} = 0 := by
        rw [ae_iff] at h
        exact measure_mono_null (fun z hz => by
          simp only [Set.mem_setOf_eq, ne_eq, not_not, Pi.sub_apply] at hz ⊢; linarith) h
      have h2 : μ Set.univ ≤ μ (Function.support (g - f)) + μ {z | ¬ ((g - f) z ≠ 0)} := by
        calc μ Set.univ = μ ((Function.support (g - f)) ∪ {z | ¬ ((g - f) z ≠ 0)}) := by
              congr 1; ext z; simp only [Function.mem_support, Set.mem_union, Set.mem_univ, true_iff]; exact (em _).symm.imp_left id |>.symm
          _ ≤ _ := measure_union_le _ _
      rw [h1, add_zero, measure_univ] at h2
      exact lt_of_lt_of_le zero_lt_one h2
    · filter_upwards [h] with z hz
      simp only [Pi.zero_apply, Pi.sub_apply]; linarith
  simp only [Pi.sub_apply] at hpos
  rw [integral_sub hg hf] at hpos
  linarith

section FinalNN

variable (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (m : ℕ) (hmT : m < P.T) (D : ℝ)
  (hD : 0 ≤ D)

include hS hℓ hmT hD

/-- `V_{t+1}(1, 0, ·)` agrees a.e. with `Phi`, so `C` is an integral of `Phi`. -/
lemma C_eq (t : ℕ) (ht : t ≤ m) (p : ℝ) :
    C P m D t p = P.ρ * ∫ z, Phi P m D (m - t) (t + 1) 1 0 z ∂(P.κ t p) := by
  unfold C
  congr 1
  apply integral_congr_ae
  filter_upwards [hS.2.2.2.2.2.2.2.2 t p] with z hz
  exact V_eq_Phi P hS hℓ m hmT D hD (m - t) (t + 1) (by omega) 1 0 z zero_le_one le_rfl le_rfl hz

lemma C_m (p : ℝ) : C P m D m p = 0 := by
  unfold C; simp [V_gt P (singlePayment m D) m (m + 1) (by omega)]

/-- (A.9)-type facts at the state `(1, 0)`: objective bound and candidate values. -/
lemma state10 (t : ℕ) (ht : t ≤ m) (p : ℝ) (hp : 0 < p) :
    (∀ q, Feasible P (singlePayment m D) t 1 0 p q →
      objV P (singlePayment m D) m t 1 0 p q ≤
        max (C P m D t p) (max (Ro P t p * (1 - P.ρ ^ (m - t) * D / p)) (p - P.ρ ^ (m - t) * D))) ∧
    (t < m → Feasible P (singlePayment m D) t 1 0 p 0 ∧
      objV P (singlePayment m D) m t 1 0 p 0 = C P m D t p) ∧
    (P.ρ ^ (m - t) * D ≤ p →
      Feasible P (singlePayment m D) t 1 0 p (P.ρ ^ (m - t) * D / p) ∧
      objV P (singlePayment m D) m t 1 0 p (P.ρ ^ (m - t) * D / p) =
        Ro P t p * (1 - P.ρ ^ (m - t) * D / p) ∧
      Feasible P (singlePayment m D) t 1 0 p 1 ∧
      objV P (singlePayment m D) m t 1 0 p 1 = p - P.ρ ^ (m - t) * D) := by
  have hδ : dl P m D t = P.ρ ^ (m - t) * D := rfl
  have hδ0 := dl_nonneg P hS hℓ m hmT D hD t
  rw [← hδ] at *
  set δ := dl P m D t with hδdef
  have hfeas : ∀ q, Feasible P (singlePayment m D) t 1 0 p q ↔
      0 ≤ q ∧ q ≤ 1 ∧ singlePayment m D t ≤ p * q := by
    intro q; unfold Feasible; rw [hℓ, min_self, zero_add]
  have hdt : singlePayment m D t ≤ δ := by
    by_cases h : t = m
    · subst h; rw [sp_eq, hδdef, dl_m P hS hℓ t hmT D hD]
    · rw [sp_ne m D t h]; exact hδ0
  have hval : δ ≤ p → 0 ≤ δ / p ∧ δ / p ≤ 1 ∧ p * (δ / p) = δ := by
    intro h
    exact ⟨div_nonneg hδ0 hp.le, (div_le_one hp).mpr h, by field_simp⟩
  rcases lt_or_eq_of_le ht with htm | htm
  · -- before maturity
    obtain ⟨n, hn⟩ : ∃ n, t + (n + 1 + 1) = m + 1 := ⟨m - t - 1, by omega⟩
    have IH := V_eq_Phi P hS hℓ m hmT D hD (n + 1) (t + 1) (by omega)
    obtain ⟨hub, -⟩ := step_lt P hS hℓ m hmT D hD n t hn IH 1 0 p zero_le_one le_rfl le_rfl hp
    have hlin := objV_lin P hS hℓ m hmT D hD n t hn IH 1 0 p
    have h0 : objV P (singlePayment m D) m t 1 0 p 0 = C P m D t p := by
      simp [objV, objVStep, C, sp_ne m D t (by omega), show t ≠ m by omega]
    refine ⟨fun q hq => ?_, fun _ => ⟨(hfeas 0).2 ⟨le_rfl, zero_le_one, by
      rw [sp_ne m D t (by omega)]; simp⟩, h0⟩, fun hδp => ?_⟩
    · obtain ⟨hq0, hq1, -⟩ := (hfeas q).1 hq
      refine le_trans (hub q hq0 hq1) (le_of_eq ?_)
      rw [Phi_maxform P hS hℓ m hmT D hD (n + 1) t hn 1 0 p zero_le_one le_rfl le_rfl hδ0 hp]
      rw [C_eq P hS hℓ m hmT D hD t ht p, show m - t = n + 1 by omega]
      simp only [mul_zero, sub_zero, add_zero, mul_one]
      rfl
    · obtain ⟨hv0, hv1, hv2⟩ := hval hδp
      refine ⟨(hfeas _).2 ⟨hv0, hv1, by rw [hv2]; exact hdt⟩, ?_, (hfeas 1).2 ⟨zero_le_one, le_rfl,
        by rw [mul_one]; linarith⟩, ?_⟩
      · rw [hlin (δ / p) hv0 hv1 le_rfl le_rfl hp (by rw [zero_add, hv2])]; rw [hv2]; ring
      · rw [hlin 1 zero_le_one le_rfl le_rfl le_rfl hp (by rw [zero_add, mul_one]; exact hδp)]; ring
  · -- at maturity
    subst htm
    have hδm : δ = D := by rw [hδdef, dl_m P hS hℓ t hmT D hD]
    have hobj := objV_m P hS hℓ t hmT D hD 1 0 p
    rw [C_m P hS hℓ t hmT D hD]
    refine ⟨fun q hq => ?_, fun h => absurd h (lt_irrefl _), fun hδp => ?_⟩
    · obtain ⟨hq0, hq1, hqD⟩ := (hfeas q).1 hq
      rw [sp_eq] at hqD
      rw [hobj q hq0 hq1 le_rfl, hδm]
      have hRo := Ro_nonneg P hS hℓ t hmT.le p
      set u := D / p with hu
      have hpu : p * u = D := by rw [hu]; field_simp
      clear_value u
      have hqu' : u ≤ q := le_of_mul_le_mul_left (by linarith : p * u ≤ p * q) hp
      refine le_trans ?_ (le_max_right _ _)
      by_cases hpR : Ro P t p ≤ p
      · refine le_trans ?_ (le_max_right _ _)
        nlinarith [mul_le_mul_of_nonneg_left hpR (sub_nonneg.mpr hq1)]
      · refine le_trans ?_ (le_max_left _ _)
        have hpR' : p ≤ Ro P t p := le_of_lt (not_le.mp hpR)
        have : p * q + (1 - q) * Ro P t p + 0 - D - Ro P t p * (1 - u) =
            (q - u) * (p - Ro P t p) := by linear_combination hpu
        nlinarith [mul_le_mul_of_nonneg_left hpR' (sub_nonneg.mpr hqu')]
    · obtain ⟨hv0, hv1, hv2⟩ := hval hδp
      refine ⟨(hfeas _).2 ⟨hv0, hv1, by rw [hv2]; exact hdt⟩, ?_, (hfeas 1).2 ⟨zero_le_one, le_rfl,
        by rw [mul_one]; linarith⟩, ?_⟩
      · rw [hobj _ hv0 hv1 le_rfl, hv2, hδm]; ring
      · rw [hobj 1 zero_le_one le_rfl le_rfl, hδm]; ring

lemma EDelta_eq (t : ℕ) (ht : t ≤ m) (p : ℝ) :
    P.ρ * EDelta P m D t p = C P m D t p - Ro P t p + P.ρ ^ (m - t) * D := by
  have htT : t < P.T := by omega
  have := hS.2.2.2.2.2.1 t
  have hρne : P.ρ ≠ 0 := hS.2.1.ne'
  have hV : Integrable (fun z => V P (singlePayment m D) m (t + 1) 1 0 z) (P.κ t p) := by
    refine (Phi_int P hS hℓ m hmT D hD (m - t) t (by omega) 1 0 zero_le_one le_rfl le_rfl p).congr ?_
    filter_upwards [hS.2.2.2.2.2.2.2.2 t p] with z hz
    exact (V_eq_Phi P hS hℓ m hmT D hD (m - t) (t + 1) (by omega) 1 0 z zero_le_one le_rfl
      le_rfl hz).symm
  have hUf : (fun z => U P (t + 1) 1 z) = Mx P (t + 1) := funext (fun z => U_one P hℓ (t + 1) (by omega) z)
  have hU : Integrable (fun z => U P (t + 1) 1 z) (P.κ t p) := by
    rw [hUf]; exact Mx_int P hS hℓ t htT p
  unfold EDelta
  set c := P.ρ ^ ((m : ℤ) - (t : ℤ) - 1) * D with hc
  have hU' : Integrable (fun z => U P (t + 1) 1 z - c) (P.κ t p) := hU.sub (integrable_const c)
  rw [integral_sub hV hU', integral_sub hU (integrable_const c), integral_const]
  simp only [probReal_univ, one_smul]
  have hz : P.ρ * P.ρ ^ ((m : ℤ) - (t : ℤ) - 1) = P.ρ ^ (m - t) := by
    rw [← zpow_one_add₀ hρne, show (1 : ℤ) + ((m : ℤ) - t - 1) = ((m - t : ℕ) : ℤ) by
      rw [Nat.cast_sub ht]; ring, zpow_natCast]
  unfold C Ro
  rw [← hz]
  ring

lemma secured (s : ℕ) (hs : s ≤ m) (x w p' : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hw : P.ρ ^ (m - s) * D ≤ w) (hp' : 0 < p') (q : ℝ) :
    IsOptimal P (singlePayment m D) m s x w p' q ↔ IsOptimalU P s x p' q := by
  have hdl0 := dl_nonneg P hS hℓ m hmT D hD s
  have hw' : dl P m D s ≤ w := hw
  have hw0 : 0 ≤ w := le_trans hdl0 hw'
  have hfe : ∀ q, Feasible P (singlePayment m D) s x w p' q ↔ q ∈ Set.Icc 0 (min x P.ℓ) := by
    intro q
    unfold Feasible
    rw [hℓ, min_eq_left hx1]
    constructor
    · rintro ⟨a, b, _⟩; exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      refine ⟨a, b, ?_⟩
      by_cases h : s = m
      · subst h; rw [sp_eq]; rw [dl_m P hS hℓ s hmT D hD] at hw'; nlinarith
      · rw [sp_ne m D s h]; nlinarith
  have hobj : ∀ q ∈ Set.Icc (0:ℝ) (min x P.ℓ), objV P (singlePayment m D) m s x w p' q =
      objU P s x p' q + w - dl P m D s := by
    intro q hq
    rw [hℓ, min_eq_left hx1] at hq
    rcases lt_or_eq_of_le hs with hsm | hsm
    · obtain ⟨n, hn⟩ : ∃ n, s + (n + 1 + 1) = m + 1 := ⟨m - s - 1, by omega⟩
      have IH := V_eq_Phi P hS hℓ m hmT D hD (n + 1) (s + 1) (by omega)
      rw [objV_lin P hS hℓ m hmT D hD n s hn IH x w p' q hq.1 hq.2 hx1 hw0 hp'
        (by nlinarith [hq.1]), objU_eq P hℓ s x p' q hq.1 hq.2 hx1]
      ring
    · subst hsm
      unfold objV objVStep
      rw [if_pos rfl, sp_eq, dl_m P hS hℓ s hmT D hD]
  unfold IsOptimal IsOptimalU
  constructor
  · rintro ⟨hq, hmax⟩
    have hq' := (hfe q).1 hq
    refine ⟨hq', fun q' hq'' => ?_⟩
    have := hmax q' ((hfe q').2 hq'')
    rw [hobj q' hq'', hobj q hq'] at this
    linarith
  · rintro ⟨hq, hmax⟩
    refine ⟨(hfe q).2 hq, fun q' hq'' => ?_⟩
    have hq3 := (hfe q').1 hq''
    rw [hobj q' hq3, hobj q hq]
    linarith [hmax q' hq3]

end FinalNN

section Final

variable (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) (m : ℕ) (hmT : m < P.T) (D : ℝ)
  (hD : 0 < D)

include hS hℓ hmT hD

lemma dl_pos (s : ℕ) : 0 < dl P m D s := mul_pos (pow_pos hS.2.1 _) hD

lemma Phi_lt_Mx : ∀ n s, s + n = m + 1 → ∀ z, 0 < z → Phi P m D n s 1 0 z < Mx P s z := by
  intro n
  induction n with
  | zero => intro s hs z hz; rw [Phi_zero]; exact lt_of_lt_of_le hz (le_max_left _ _)
  | succ n ih =>
    intro s hs z hz
    have hsT : s < P.T := by omega
    have hdl := dl_pos P hS hℓ m hmT D hD s
    rw [Phi_maxform P hS hℓ m hmT D hD.le n s hs 1 0 z zero_le_one le_rfl le_rfl hdl.le hz]
    have hRpos := Ro_pos P hS hℓ s hsT z
    have hRM : Ro P s z ≤ Mx P s z := le_max_right _ _
    have hzM : z ≤ Mx P s z := le_max_left _ _
    refine max_lt ?_ (max_lt ?_ (by linarith))
    · have := hS.2.2.2.2.2.1 s
      rw [mul_zero]
      have hlt : ∫ z', Phi P m D n (s + 1) 1 0 z' ∂(P.κ s z) < ∫ z', Mx P (s + 1) z' ∂(P.κ s z) := by
        apply integral_lt_of_ae_lt
        · exact Phi_int P hS hℓ m hmT D hD.le n s (by omega) 1 0 zero_le_one le_rfl le_rfl z
        · exact Mx_int P hS hℓ s hsT z
        · filter_upwards [hS.2.2.2.2.2.2.2.2 s z] with z' hz'
          exact ih (s + 1) (by omega) z' hz'
      have := Ro_eq_Mx P hℓ s hsT z
      nlinarith [mul_lt_mul_of_pos_left hlt hS.2.1]
    · have : 0 < (dl P m D s - 0) / z := div_pos (by linarith) hz
      nlinarith

lemma C_props (t : ℕ) (ht : t ≤ m) (p : ℝ) :
    0 ≤ C P m D t p ∧ C P m D t p < Ro P t p ∧ 0 < Ro P t p := by
  have htT : t < P.T := by omega
  have := hS.2.2.2.2.2.1 t
  rw [C_eq P hS hℓ m hmT D hD.le t ht p]
  refine ⟨?_, ?_, Ro_pos P hS hℓ t htT p⟩
  · refine mul_nonneg hS.2.1.le (integral_nonneg_of_ae ?_)
    filter_upwards [hS.2.2.2.2.2.2.2.2 t p] with z hz
    exact (Phi_bounds P hS hℓ m hmT D hD.le (m - t) (t + 1) (by omega) 1 0 z zero_le_one le_rfl
      le_rfl hz).1
  · have hlt : ∫ z, Phi P m D (m - t) (t + 1) 1 0 z ∂(P.κ t p) < ∫ z, Mx P (t + 1) z ∂(P.κ t p) := by
      apply integral_lt_of_ae_lt
      · exact Phi_int P hS hℓ m hmT D hD.le (m - t) t (by omega) 1 0 zero_le_one le_rfl le_rfl p
      · exact Mx_int P hS hℓ t htT p
      · filter_upwards [hS.2.2.2.2.2.2.2.2 t p] with z hz
        exact Phi_lt_Mx P hS hℓ m hmT D hD (m - t) (t + 1) (by omega) z hz
    rw [Ro_eq_Mx P hℓ t htT p]
    exact mul_lt_mul_of_pos_left hlt hS.2.1

end Final

lemma alg (p R C δ : ℝ) (hp : 0 < p) (hR : 0 < R) (hC0 : 0 ≤ C) (hCR : C < R) (hδ : 0 < δ) :
    min (δ * R / (R - C)) (C + δ) ≤ max R (C + δ) ∧
    (p < min (δ * R / (R - C)) (C + δ) →
      max C (max (R * (1 - δ / p)) (p - δ)) = C ∧ p < C + δ) ∧
    (min (δ * R / (R - C)) (C + δ) ≤ p → p < max R (C + δ) →
      δ ≤ p ∧ max C (max (R * (1 - δ / p)) (p - δ)) = R * (1 - δ / p)) ∧
    (max R (C + δ) ≤ p → δ ≤ p ∧ max C (max (R * (1 - δ / p)) (p - δ)) = p - δ) ∧
    (C + δ < R → min (δ * R / (R - C)) (C + δ) < max R (C + δ) ∧ max R (C + δ) = R) ∧
    (R ≤ C + δ → min (δ * R / (R - C)) (C + δ) = max R (C + δ) ∧ R ≤ max R (C + δ)) ∧
    (R = C + δ → min (δ * R / (R - C)) (C + δ) = R ∧ max R (C + δ) = R) := by
  have hRC : 0 < R - C := by linarith
  set X := δ * R / (R - C) with hXdef
  have hX : X * (R - C) = δ * R := by rw [hXdef]; field_simp
  clear_value X
  have hXδ : δ ≤ X := by nlinarith
  have key : (C + δ - X) * (R - C) = C * (R - C - δ) := by linear_combination -hX
  set v := δ / p with hvdef
  have hv : p * v = δ := by rw [hvdef]; field_simp
  clear_value v
  have hf : R ≤ C + δ → min X (C + δ) = max R (C + δ) := by
    intro h
    have : C * (R - C - δ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC0 (by linarith)
    have : C + δ ≤ X := by nlinarith
    rw [min_eq_right this, max_eq_right h]
  refine ⟨le_trans (min_le_right _ _) (le_max_right _ _), fun h => ?_, fun h1 h2 => ?_,
    fun h => ?_, fun h => ?_, fun h => ⟨hf h, le_max_left _ _⟩, fun h => ?_⟩
  · have hpX : p < X := lt_of_lt_of_le h (min_le_left _ _)
    have hpC : p < C + δ := lt_of_lt_of_le h (min_le_right _ _)
    refine ⟨max_eq_left (max_le ?_ (by linarith)), hpC⟩
    -- R (1 - v) ≤ C  ⟸  p (R - C) < X (R - C) = δ R = p v R
    have : p * (R - C) < p * v * R := by rw [hv, ← hX]; exact mul_lt_mul_of_pos_right hpX hRC
    have : R * (1 - v) < C := by nlinarith
    linarith
  · by_cases hRCd : R ≤ C + δ
    · exfalso; rw [hf hRCd] at h1; linarith
    · have hlt : C + δ < R := lt_of_not_ge hRCd
      have hXle : X ≤ C + δ := by
        have : 0 ≤ C * (R - C - δ) := mul_nonneg hC0 (by linarith)
        nlinarith
      rw [min_eq_left hXle] at h1
      rw [max_eq_left hlt.le] at h2
      have hδp : δ ≤ p := le_trans hXδ h1
      refine ⟨hδp, ?_⟩
      have hv1 : v ≤ 1 := by nlinarith
      have hA : C ≤ R * (1 - v) := by
        have : X * (R - C) ≤ p * (R - C) := mul_le_mul_of_nonneg_right h1 hRC.le
        rw [hX, ← hv] at this
        nlinarith
      have hB : p - δ ≤ R * (1 - v) := by
        rw [← hv]; nlinarith [mul_le_mul_of_nonneg_right h2.le (sub_nonneg.mpr hv1)]
      rw [max_eq_left hB, max_eq_right hA]
  · have hRp : R ≤ p := le_trans (le_max_left _ _) h
    have hCp : C + δ ≤ p := le_trans (le_max_right _ _) h
    have hδp : δ ≤ p := by linarith
    refine ⟨hδp, ?_⟩
    have hv1 : v ≤ 1 := by nlinarith
    have hB : R * (1 - v) ≤ p - δ := by
      rw [← hv]; nlinarith [mul_le_mul_of_nonneg_right hRp (sub_nonneg.mpr hv1)]
    rw [max_eq_right hB, max_eq_right (by linarith)]
  · have hmax : max R (C + δ) = R := max_eq_left h.le
    refine ⟨?_, hmax⟩
    rw [hmax]
    have hXR : X < R := by nlinarith
    exact lt_of_le_of_lt (min_le_left _ _) hXR
  · have h1 := hf h.le
    have h2 : max R (C + δ) = R := max_eq_left h.ge
    exact ⟨h1.trans h2, h2⟩


end ADCBSol


open ADCBSol in
theorem solution (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1) :
    (∀ t, 1 ≤ t → t ≤ P.T → ∀ x p : ℝ, 0 ≤ x → x ≤ 1 → 0 < p →
        U P t x p = max p (Ro P t p) * x) ∧
    (∀ t, 1 ≤ t → t ≤ P.T → ∀ x p : ℝ, 0 ≤ x → x ≤ 1 → 0 < p →
        (Ro P t p ≤ p → IsOptimalU P t x p x) ∧ (p < Ro P t p → IsOptimalU P t x p 0)) ∧
    (∀ p : ℝ, 0 < p → Ro P P.T p = 0) ∧
    (∀ t, 1 ≤ t → t < P.T → ∀ p : ℝ, 0 < p →
        Ro P t p = P.ρ * ∫ p', max p' (Ro P (t + 1) p') ∂(P.κ t p)) := by
  refine ⟨fun t _ ht x p hx0 hx1 _ => U_formula P hℓ t ht x p hx0 hx1,
    fun t _ ht x p hx0 hx1 hp => ⟨fun h => ?_, fun h => ?_⟩,
    fun p _ => Ro_T P p, fun t _ ht p _ => Ro_rec P hℓ t ht p⟩
  · refine ⟨by rw [hℓ, min_eq_left hx1]; exact ⟨hx0, le_rfl⟩, fun q' hq' => ?_⟩
    rw [hℓ, min_eq_left hx1] at hq'
    rw [objU_eq P hℓ t x p q' hq'.1 hq'.2 hx1, objU_eq P hℓ t x p x hx0 le_rfl hx1]
    nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hq'.2)]
  · refine ⟨by rw [hℓ, min_eq_left hx1]; exact ⟨le_rfl, hx0⟩, fun q' hq' => ?_⟩
    rw [hℓ, min_eq_left hx1] at hq'
    rw [objU_eq P hℓ t x p q' hq'.1 hq'.2 hx1, objU_eq P hℓ t x p 0 le_rfl hx0 hx1]
    nlinarith [mul_le_mul_of_nonneg_left h.le hq'.1]
