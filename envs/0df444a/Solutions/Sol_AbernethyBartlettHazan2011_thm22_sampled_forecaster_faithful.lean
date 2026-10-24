-- Prove2me | solution 1 for AbernethyBartlettHazan2011.thm22_sampled_forecaster_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:24:26.232077+00:00
-- url     : https://prove2.me/submissions/96184366-eb3a-461f-8bc4-645b68777801

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game
import Definitions.Def_ApproachRegret_Calibration_Algorithms
import Theorems.Thm_ApproachRegret_Calibration_theorem22_calibration_rate

open ApproachRegret.Calibration

namespace AB87

theorem alg3_prob (m : ℕ) (θ : ApproachRegret.ToOLO.E (m + 1)) (w : Fin (m + 1) → ℝ)
    (h : IsAlg3Output m θ w) : (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, i, hi, hi1, h0, hne⟩
  · refine ⟨fun a => ?_, by simp⟩
    by_cases ha : a = 0 <;> simp [Pi.single_apply, ha]
  · refine ⟨fun a => ?_, by simp⟩
    by_cases ha : a = Fin.last m <;> simp [Pi.single_apply, ha]
  · by_cases hz : θ i.succ = 0
    · rw [h0 hz]
      refine ⟨fun a => ?_, by simp⟩
      by_cases ha : a = i.succ <;> simp [Pi.single_apply, ha]
    · rw [hne hz]
      have hlt : θ i.succ < 0 := lt_of_le_of_ne hi1 hz
      have ha' : 0 < (θ i.castSucc)⁻¹ := inv_pos.mpr hi
      have hb' : (θ i.succ)⁻¹ < 0 := inv_lt_zero.mpr hlt
      have hD : 0 < (θ i.castSucc)⁻¹ - (θ i.succ)⁻¹ := by linarith
      have hne' : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
      refine ⟨fun a => ?_, ?_⟩
      · apply div_nonneg _ hD.le
        by_cases h1 : a = i.castSucc
        · subst h1; simp [Pi.single_apply, hne', ha'.le]
        · by_cases h2 : a = i.succ
          · subst h2; simp [Pi.single_apply, hne'.symm]; linarith
          · simp [Pi.single_apply, h1, h2]
      · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [Finset.sum_pi_single', Finset.mem_univ, if_true, mul_one]
        exact div_self hD.ne'

/-- product-measure expectation of a product of functions -/
theorem sum_prod_mul {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P h : ι → α → ℝ) :
    ∑ s : ι → α, (∏ u, P u (s u)) * ∏ u, h u (s u) = ∏ u, ∑ a, P u a * h u a := by
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

theorem exp_one {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → α → ℝ) (hP : ∀ u, ∑ a, P u a = 1) :
    ∑ s : ι → α, (∏ u, P u (s u)) = 1 := by
  have := sum_prod_mul P (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at this
  rw [this]; simp [hP]

theorem exp_single {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → α → ℝ) (hP : ∀ u, ∑ a, P u a = 1) (t : ι) (f : α → ℝ) :
    ∑ s : ι → α, (∏ u, P u (s u)) * f (s t) = ∑ a, P t a * f a := by
  have := sum_prod_mul P (fun u a => if u = t then f a else 1)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at this
  rw [this]
  rw [Finset.prod_eq_single t]
  · simp
  · intro u _ hu; simp [hu, hP]
  · simp

theorem exp_pair {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → α → ℝ) (hP : ∀ u, ∑ a, P u a = 1) (t t' : ι) (htt : t ≠ t') (f g : α → ℝ) :
    ∑ s : ι → α, (∏ u, P u (s u)) * (f (s t) * g (s t')) =
      (∑ a, P t a * f a) * ∑ a, P t' a * g a := by
  have := sum_prod_mul P (fun u a => (if u = t then f a else 1) * (if u = t' then g a else 1))
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true] at this
  rw [this]
  have hφ : ∀ u, ∑ a, P u a * ((if u = t then f a else 1) * (if u = t' then g a else 1)) =
      (if u = t then ∑ a, P t a * f a else 1) * (if u = t' then ∑ a, P t' a * g a else 1) := by
    intro u
    by_cases h1 : u = t
    · subst h1; simp [htt]
    · by_cases h2 : u = t'
      · subst h2; simp [h1]
      · simp [h1, h2, hP]
  simp only [hφ, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem var_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (P : ι → α → ℝ) (hP0 : ∀ u a, 0 ≤ P u a) (hP : ∀ u, ∑ a, P u a = 1) (i : α)
    (c : ι → ℝ) (hc : ∀ u, |c u| ≤ 1) :
    ∑ s : ι → α, (∏ u, P u (s u)) *
      (∑ t, ((if s t = i then (1 : ℝ) else 0) - P t i) * c t) ^ 2 ≤ ∑ t, P t i := by
  set X : ι → α → ℝ := fun t a => ((if a = i then (1 : ℝ) else 0) - P t i) * c t with hX
  have hmean : ∀ t, ∑ a, P t a * X t a = 0 := by
    intro t
    simp only [hX, ← mul_assoc, ← Finset.sum_mul, mul_sub, Finset.sum_sub_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hP,
      one_mul, sub_self, zero_mul]
  have hvar : ∀ t, ∑ a, P t a * (X t a * X t a) ≤ P t i := by
    intro t
    have hq1 : P t i ≤ 1 := by
      rw [← hP t]
      exact Finset.single_le_sum (fun a _ => hP0 t a) (Finset.mem_univ i)
    have hq0 := hP0 t i
    have hc2 : c t ^ 2 ≤ 1 := by
      have := hc t
      nlinarith [abs_nonneg (c t), sq_abs (c t)]
    have key : ∀ a, P t a * (X t a * X t a) =
        c t ^ 2 * ((1 - 2 * P t i) * (P t a * (if a = i then 1 else 0)) + P t i ^ 2 * P t a) := by
      intro a; simp only [hX]; split_ifs <;> ring
    simp only [key, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hP]
    have h1 : 0 ≤ P t i - P t i ^ 2 := by nlinarith
    have h2 : (1 - 2 * P t i) * P t i + P t i ^ 2 = P t i - P t i ^ 2 := by ring
    rw [h2]
    calc c t ^ 2 * (P t i - P t i ^ 2) ≤ 1 * (P t i - P t i ^ 2) :=
          mul_le_mul_of_nonneg_right hc2 h1
      _ ≤ P t i := by nlinarith
  have hexp : ∀ s : ι → α, (∑ t, ((if s t = i then (1 : ℝ) else 0) - P t i) * c t) ^ 2 =
      ∑ t, ∑ t', X t (s t) * X t' (s t') := by
    intro s; rw [sq, Finset.sum_mul_sum]
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single t]
  · rw [exp_single P hP t (fun a => X t a * X t a)]
    exact hvar t
  · intro t' _ ht'
    rw [exp_pair P hP t t' (Ne.symm ht') (X t) (X t'), hmean t, zero_mul]
  · simp

theorem cs_weighted {β : Type*} [Fintype β] (W g : β → ℝ) (hW : ∀ s, 0 ≤ W s)
    (hW1 : ∑ s, W s = 1) : ∑ s, W s * |g s| ≤ Real.sqrt (∑ s, W s * g s ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (r := fun s => W s * |g s|)
    (f := W) (g := fun s => W s * g s ^ 2) Finset.univ (fun s _ => hW s)
    (fun s _ => mul_nonneg (hW s) (sq_nonneg _)) (fun s _ => by
      show (W s * |g s|) ^ 2 ≤ W s * (W s * g s ^ 2); rw [mul_pow, sq_abs]; nlinarith [hW s])
  rw [hW1, one_mul] at h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

theorem reindex (T : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ Finset.Icc 1 T, f t = ∑ t : Fin T, f (t.val + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range (fun k => f (1 + k))]
  simp [add_comm]

theorem abs_aux (a b : ℝ) : |a| ≤ |b| + |a - b| := by
  linarith [abs_sub_abs_le_abs_sub a b]

theorem max_aux (a b d : ℝ) (hd : 0 ≤ d) (h : a ≤ b + d) : max 0 a ≤ max 0 b + d :=
  max_le (by have := le_max_left 0 b; linarith) (by have := le_max_right 0 b; linarith)

theorem sum_sqrt_bound (m T : ℕ) (hT : 1 ≤ T) (g : Fin (m + 1) → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hs : ∑ i, g i = T) :
    ∑ i, (1 / (T : ℝ)) * Real.sqrt (g i) ≤ Real.sqrt (((m : ℝ) + 1) / T) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (m + 1) => (1 : ℝ))
    (fun i => Real.sqrt (g i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Real.sq_sqrt (hg _), hs] at h
  apply (le_abs_self _).trans (Real.abs_le_sqrt _)
  rw [← Finset.mul_sum, mul_pow]
  push_cast at h
  calc (1 / (T : ℝ)) ^ 2 * (∑ i, Real.sqrt (g i)) ^ 2 ≤ (1 / (T : ℝ)) ^ 2 * ((m + 1) * T) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = ((m : ℝ) + 1) / T := by field_simp

end AB87

open AB87 in
theorem solution (m T : ℕ) (hm : 1 ≤ m) (hT : 1 ≤ T)
    (y : ℕ → ℝ) (hy : ∀ t, 1 ≤ t → t ≤ T → y t = 0 ∨ y t = 1)
    (w : ℕ → Fin (m + 1) → ℝ) (θ : ℕ → ApproachRegret.ToOLO.E (m + 1))
    (hrun : IsAlg5Run m (Real.sqrt (((m : ℝ) + 1) / T)) T y w θ) :
    ∑ s : Fin T → Fin (m + 1), (∏ t : Fin T, w (t.val + 1) (s t)) *
      max 0 ((∑ i : Fin (m + 1),
          |(1 / (T : ℝ)) * ∑ t : Fin T,
            (if s t = i then (1 : ℝ) else 0) * (((i : ℕ) : ℝ) / (m : ℝ) - y (t.val + 1))|)
        - eps m / 2)
      ≤ 2 * Real.sqrt (2 / (eps m * T)) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set p : Fin T → Fin (m + 1) → ℝ := fun t => w (t.val + 1) with hpdef
  have hprob : ∀ t : Fin T, (∀ a, 0 ≤ p t a) ∧ ∑ a, p t a = 1 := by
    intro t
    rcases Nat.eq_zero_or_pos t.val with h0 | hpos
    · have := hrun.2.1
      simp only [hpdef, h0, zero_add]
      exact this
    · obtain ⟨k, hk⟩ : ∃ k, t.val = k + 1 := ⟨t.val - 1, by omega⟩
      have := hrun.2.2.2 (k + 1) (by omega) (by omega)
      simp only [hpdef, hk]
      exact alg3_prob m _ _ this
  have hp0 : ∀ t a, 0 ≤ p t a := fun t => (hprob t).1
  have hp1 : ∀ t, ∑ a, p t a = 1 := fun t => (hprob t).2
  set c : Fin T → Fin (m + 1) → ℝ := fun t i => ((i : ℕ) : ℝ) / (m : ℝ) - y (t.val + 1) with hcdef
  have hc : ∀ t i, |c t i| ≤ 1 := by
    intro t i
    have hi : ((i : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
    have h1 : 0 ≤ ((i : ℕ) : ℝ) / (m : ℝ) := by positivity
    have h2 : ((i : ℕ) : ℝ) / (m : ℝ) ≤ 1 := (div_le_one hmpos).mpr hi
    rcases hy (t.val + 1) (by omega) (by omega) with h | h <;>
      · simp only [hcdef, h]; rw [abs_le]; constructor <;> linarith
  set W : (Fin T → Fin (m + 1)) → ℝ := fun s => ∏ t, p t (s t) with hWdef
  have hW0 : ∀ s, 0 ≤ W s := fun s => Finset.prod_nonneg (fun t _ => hp0 t (s t))
  have hW1 : ∑ s, W s = 1 := exp_one p hp1
  set C := calibRate m T w y with hC
  set S : Fin (m + 1) → (Fin T → Fin (m + 1)) → ℝ :=
    fun i s => ∑ t, ((if s t = i then (1 : ℝ) else 0) - p t i) * c t i with hSdef
  -- pointwise bound
  have hpt : ∀ s, max 0 ((∑ i : Fin (m + 1),
          |(1 / (T : ℝ)) * ∑ t : Fin T,
            (if s t = i then (1 : ℝ) else 0) * (((i : ℕ) : ℝ) / (m : ℝ) - y (t.val + 1))|)
        - eps m / 2) ≤ C + ∑ i, (1 / (T : ℝ)) * |S i s| := by
    intro s
    rw [hC]; unfold calibRate
    apply max_aux _ _ _ (Finset.sum_nonneg (fun i _ => by positivity))
    have hsplit : ∀ i, |(1 / (T : ℝ)) * ∑ t : Fin T,
            (if s t = i then (1 : ℝ) else 0) * (((i : ℕ) : ℝ) / (m : ℝ) - y (t.val + 1))| ≤
        |(1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, w t i * (((i : ℕ) : ℝ) / (m : ℝ) - y t)|
          + (1 / (T : ℝ)) * |S i s| := by
      intro i
      rw [reindex T (fun t => w t i * (((i : ℕ) : ℝ) / (m : ℝ) - y t))]
      have : (1 / (T : ℝ)) * |S i s| = |(1 / (T : ℝ)) * ∑ t : Fin T,
            (if s t = i then (1 : ℝ) else 0) * (((i : ℕ) : ℝ) / (m : ℝ) - y (t.val + 1)) -
            (1 / (T : ℝ)) * ∑ t : Fin T, w (t.val + 1) i * (((i : ℕ) : ℝ) / (m : ℝ) - y (t.val + 1))| := by
        rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / T), ← Finset.sum_sub_distrib]
        simp only [hSdef, hcdef, hpdef, sub_mul]
      rw [this]
      exact abs_aux _ _
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsplit i)
    rw [Finset.sum_add_distrib] at this
    linarith
  have hvar : ∀ i, ∑ s, W s * S i s ^ 2 ≤ ∑ t, p t i := fun i =>
    var_bound p hp0 hp1 i (fun t => c t i) (fun t => hc t i)
  have hsum : ∑ i, ∑ t, p t i = (T : ℝ) := by
    rw [Finset.sum_comm]; simp [hp1]
  have hthm := ApproachRegret.Calibration.theorem22_calibration_rate m T hm hT y hy w θ hrun
  have hlast : Real.sqrt (((m : ℝ) + 1) / T) ≤ Real.sqrt (2 / (eps m * T)) := by
    apply Real.sqrt_le_sqrt
    have : 2 / (eps m * T) = 2 * m / T := by
      unfold eps; field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ hTpos.le
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  calc _ ≤ ∑ s, W s * (C + ∑ i, (1 / (T : ℝ)) * |S i s|) :=
        Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hpt s) (hW0 s))
    _ = C + ∑ i, (1 / (T : ℝ)) * ∑ s, W s * |S i s| := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hW1, one_mul]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun s _ => by ring))
    _ ≤ C + ∑ i, (1 / (T : ℝ)) * Real.sqrt (∑ t, p t i) := by
        gcongr with i
        exact (cs_weighted W (S i) hW0 hW1).trans (Real.sqrt_le_sqrt (hvar i))
    _ ≤ C + Real.sqrt (((m : ℝ) + 1) / T) := by
        gcongr
        exact sum_sqrt_bound m T hT (fun i => ∑ t, p t i)
          (fun i => Finset.sum_nonneg (fun t _ => hp0 t i)) hsum
    _ ≤ 2 * Real.sqrt (2 / (eps m * T)) := by linarith
