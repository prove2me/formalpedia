-- Prove2me | solution 1 for ApproachRegret.Calibration.theorem22_calibration_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T15:16:42.274694+00:00
-- url     : https://prove2.me/submissions/f888731e-effe-4acb-9daf-85575dc5a636

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game
import Definitions.Def_ApproachRegret_Calibration_Algorithms

set_option autoImplicit false

open ApproachRegret.Calibration in
lemma p5da_inner_eq {n : ℕ} (v x : ApproachRegret.ToOLO.E n) :
    inner ℝ v x = ∑ i, v i * x i := by
  simp [PiLp.inner_apply, mul_comm]

open ApproachRegret.Calibration in
lemma p5da_cube_convex (n : ℕ) : Convex ℝ (cube n) := by
  intro x hx z hz a b ha hb hab i
  have h1 : |x i| ≤ 1 := hx i
  have h2 : |z i| ≤ 1 := hz i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  calc |a * x i + b * z i| ≤ |a * x i| + |b * z i| := abs_add_le _ _
    _ = a * |x i| + b * |z i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by linarith

lemma p5da_proj_le {n : ℕ} (K : Set (ApproachRegret.ToOLO.E n)) (hK : Convex ℝ K)
    (p z : ApproachRegret.ToOLO.E n) (hz : z ∈ K) (hmin : ∀ x ∈ K, ‖z - p‖ ≤ ‖x - p‖)
    (x : ApproachRegret.ToOLO.E n) (hx : x ∈ K) : ‖z - x‖ ^ 2 ≤ ‖p - x‖ ^ 2 := by
  have : Nonempty K := ⟨⟨z, hz⟩⟩
  have hb : BddBelow (Set.range fun w : K => ‖p - (w : ApproachRegret.ToOLO.E n)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have hinf : ‖p - z‖ = ⨅ w : K, ‖p - (w : ApproachRegret.ToOLO.E n)‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      rw [norm_sub_rev p z, norm_sub_rev p w]
      exact hmin w w.2
    · exact ciInf_le hb ⟨z, hz⟩
  have hvi : inner ℝ (p - z) (x - z) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hK hz).1 hinf x hx
  have key : ‖(p - z) + (z - x)‖ ^ 2
      = ‖p - z‖ ^ 2 + 2 * inner ℝ (p - z) (z - x) + ‖z - x‖ ^ 2 := norm_add_sq_real _ _
  have hexp : (p - z) + (z - x) = p - x := by abel
  rw [hexp] at key
  rw [key]
  have : inner ℝ (p - z) (z - x) = - inner ℝ (p - z) (x - z) := by
    rw [← inner_neg_right, neg_sub]
  nlinarith [sq_nonneg ‖p - z‖]

lemma p5da_sum_single {n : ℕ} (k : Fin n) (g : Fin n → ℝ) :
    ∑ j, (Pi.single k (1 : ℝ) : Fin n → ℝ) j * g j = g k := by
  simp [Pi.single_apply]

lemma p5da_sum_two {n : ℕ} (a b : ℝ) (i k : Fin n) (g : Fin n → ℝ) :
    ∑ j, ((a * (Pi.single i (1 : ℝ) : Fin n → ℝ) j - b * (Pi.single k (1 : ℝ) : Fin n → ℝ) j)
      / (a - b)) * g j = (a * g i - b * g k) / (a - b) := by
  have h : ∀ j, ((a * (Pi.single i (1 : ℝ) : Fin n → ℝ) j - b * (Pi.single k (1 : ℝ) : Fin n → ℝ) j)
      / (a - b)) * g j = (a / (a - b)) * ((Pi.single i (1 : ℝ) : Fin n → ℝ) j * g j)
        - (b / (a - b)) * ((Pi.single k (1 : ℝ) : Fin n → ℝ) j * g j) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, p5da_sum_single, p5da_sum_single]
  ring

open ApproachRegret.Calibration in
lemma p5da_inner_payoff (m : ℕ) (w : Fin (m + 1) → ℝ) (y : ℝ) (θ : ApproachRegret.ToOLO.E (m + 1)) :
    inner ℝ (payoff m w y) θ = ∑ j, w j * ((y - ((j : ℕ) : ℝ) / (m : ℝ)) * θ j) := by
  rw [p5da_inner_eq]
  apply Finset.sum_congr rfl
  intro j _
  simp only [payoff, PiLp.toLp_apply]
  ring

open ApproachRegret.Calibration in
lemma p5da_alg3_simplex (m : ℕ) (θ : ApproachRegret.ToOLO.E (m + 1)) (w : Fin (m + 1) → ℝ)
    (hw : IsAlg3Output m θ w) : w ∈ stdSimplex ℝ (Fin (m + 1)) := by
  rcases hw with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, i, hi, hk, hz, hnz⟩
  · exact single_mem_stdSimplex ℝ 0
  · exact single_mem_stdSimplex ℝ _
  · by_cases h0 : θ i.succ = 0
    · rw [hz h0]; exact single_mem_stdSimplex ℝ _
    · rw [hnz h0]
      have hk' : θ i.succ < 0 := lt_of_le_of_ne hk h0
      have ha : 0 < (θ i.castSucc)⁻¹ := inv_pos.2 hi
      have hb : (θ i.succ)⁻¹ < 0 := inv_lt_zero.2 hk'
      have hd : 0 < (θ i.castSucc)⁻¹ - (θ i.succ)⁻¹ := by linarith
      refine ⟨fun j => ?_, ?_⟩
      · apply div_nonneg _ hd.le
        have h1 : 0 ≤ (Pi.single i.castSucc (1 : ℝ) : Fin (m + 1) → ℝ) j := by
          simp only [Pi.single_apply]; split_ifs <;> norm_num
        have h2 : 0 ≤ (Pi.single i.succ (1 : ℝ) : Fin (m + 1) → ℝ) j := by
          simp only [Pi.single_apply]; split_ifs <;> norm_num
        nlinarith
      · have := p5da_sum_two (θ i.castSucc)⁻¹ (θ i.succ)⁻¹ i.castSucc i.succ (fun _ => (1 : ℝ))
        simp only [mul_one] at this
        rw [this, div_self hd.ne']

open ApproachRegret.Calibration in
lemma p5da_oracle (m : ℕ) (hm : 1 ≤ m) (θ : ApproachRegret.ToOLO.E (m + 1))
    (hθ : θ ∈ cube (m + 1)) (w : Fin (m + 1) → ℝ) (hw : IsAlg3Output m θ w) (y : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : inner ℝ (payoff m w y) θ ≤ eps m / 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have heps : 0 ≤ eps m / 2 := by unfold eps; positivity
  rw [p5da_inner_payoff]
  rcases hw with ⟨h0, rfl⟩ | ⟨_, hl, rfl⟩ | ⟨_, _, i, hi, hk, hz, hnz⟩
  · rw [p5da_sum_single]
    simp only [Fin.val_zero, Nat.cast_zero, zero_div, sub_zero]
    nlinarith
  · rw [p5da_sum_single]
    simp only [Fin.val_last, div_self hmpos.ne']
    nlinarith
  · by_cases h0 : θ i.succ = 0
    · rw [hz h0, p5da_sum_single, h0]; simpa using heps
    · rw [hnz h0, p5da_sum_two]
      have hk' : θ i.succ < 0 := lt_of_le_of_ne hk h0
      have hi1 : θ i.castSucc ≤ 1 := (abs_le.1 (hθ i.castSucc)).2
      have hk1 : -1 ≤ θ i.succ := (abs_le.1 (hθ i.succ)).1
      have ha1 : 1 ≤ (θ i.castSucc)⁻¹ := one_le_inv₀ hi |>.2 hi1
      have hb1 : (θ i.succ)⁻¹ ≤ -1 := by
        have hm1 : θ i.succ * (θ i.succ)⁻¹ = 1 := mul_inv_cancel₀ h0
        have hneg : (θ i.succ)⁻¹ < 0 := inv_lt_zero.2 hk'
        nlinarith
      have hd : 2 ≤ (θ i.castSucc)⁻¹ - (θ i.succ)⁻¹ := by linarith
      have hnum : (θ i.castSucc)⁻¹ * ((y - ((i.castSucc : ℕ) : ℝ) / (m : ℝ)) * θ i.castSucc)
          - (θ i.succ)⁻¹ * ((y - ((i.succ : ℕ) : ℝ) / (m : ℝ)) * θ i.succ) = 1 / (m : ℝ) := by
        simp only [Fin.val_castSucc, Fin.val_succ]
        field_simp
        push_cast
        ring
      rw [hnum, eps]
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hd

open ApproachRegret.Calibration in
lemma p5da_payoff_sq (m : ℕ) (hm : 1 ≤ m) (w : Fin (m + 1) → ℝ)
    (hw : w ∈ stdSimplex ℝ (Fin (m + 1))) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖payoff m w y‖ ^ 2 ≤ 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ j, ‖(payoff m w y) j‖ ^ 2 ≤ ∑ j, w j := by
        apply Finset.sum_le_sum
        intro j _
        simp only [payoff, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
        have hw0 : 0 ≤ w j := hw.1 j
        have hw1 : w j ≤ 1 := by
          rw [← hw.2]
          exact Finset.single_le_sum (fun k _ => hw.1 k) (Finset.mem_univ j)
        have hj : ((j : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 j.is_lt
        have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) / m := by positivity
        have hj1 : ((j : ℕ) : ℝ) / m ≤ 1 := by rw [div_le_one hmpos]; exact hj
        have hc : (y - ((j : ℕ) : ℝ) / m) ^ 2 ≤ 1 := by nlinarith
        rw [mul_pow]
        nlinarith [sq_nonneg (y - ((j : ℕ) : ℝ) / m)]
    _ = 1 := hw.2

open ApproachRegret.Calibration in
theorem solution (m T : ℕ) (hm : 1 ≤ m) (hT : 1 ≤ T) (y : ℕ → ℝ)
    (hy : ∀ t, 1 ≤ t → t ≤ T → y t = 0 ∨ y t = 1)
    (w : ℕ → Fin (m + 1) → ℝ) (θ : ℕ → ApproachRegret.ToOLO.E (m + 1))
    (hrun : IsAlg5Run m (Real.sqrt (((m : ℝ) + 1) / T)) T y w θ) :
    calibRate m T w y ≤ Real.sqrt (2 / (eps m * T)) := by
  obtain ⟨h1, hw1, hogd, halg⟩ := hrun
  set η := Real.sqrt (((m : ℝ) + 1) / T) with hη
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hηpos : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hηsq : η ^ 2 = ((m : ℝ) + 1) / T := Real.sq_sqrt (by positivity)
  have heps : 0 ≤ eps m := by unfold eps; positivity
  have hy01 : ∀ t, 1 ≤ t → t ≤ T → 0 ≤ y t ∧ y t ≤ 1 := by
    intro t ht1 htT
    rcases hy t ht1 htT with h | h <;> rw [h] <;> norm_num
  have hcube : ∀ t, 1 ≤ t → t ≤ T → θ t ∈ cube (m + 1) := by
    intro t ht1 htT
    rcases Nat.lt_or_ge 1 t with h | h
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact (hogd s (by omega) (by omega)).1
    · have : t = 1 := by omega
      subst this; rw [h1]; intro i; simp
  have hsimp : ∀ t, 1 ≤ t → t ≤ T → w t ∈ stdSimplex ℝ (Fin (m + 1)) := by
    intro t ht1 htT
    rcases Nat.lt_or_ge 1 t with h | h
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact p5da_alg3_simplex m _ _ (halg s (by omega) (by omega))
    · have : t = 1 := by omega
      subst this; exact hw1
  have horacle : ∀ t, 1 ≤ t → t ≤ T → inner ℝ (payoff m (w t) (y t)) (θ t) ≤ eps m / 2 := by
    intro t ht1 htT
    rcases Nat.lt_or_ge 1 t with h | h
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact p5da_oracle m hm _ (hcube _ ht1 htT) _ (halg s (by omega) (by omega)) _
        (hy01 _ ht1 htT).1 (hy01 _ ht1 htT).2
    · have : t = 1 := by omega
      subst this; rw [h1, inner_zero_right]; linarith
  have hnorm : ∀ t, 1 ≤ t → t ≤ T → ‖payoff m (w t) (y t)‖ ^ 2 ≤ 1 := fun t ht1 htT =>
    p5da_payoff_sq m hm _ (hsimp t ht1 htT) _ (hy01 _ ht1 htT).1 (hy01 _ ht1 htT).2
  -- one OGD step
  have hstep : ∀ x ∈ cube (m + 1), ∀ t, 1 ≤ t → t ≤ T →
      ‖θ (t + 1) - x‖ ^ 2 + 2 * η * inner ℝ (payoff m (w t) (y t)) x
        ≤ ‖θ t - x‖ ^ 2 + η * eps m + η ^ 2 := by
    intro x hx t ht1 htT
    have hp := hogd t ht1 htT
    have h := p5da_proj_le _ (p5da_cube_convex _) _ _ hp.1 hp.2 x hx
    have hexp : θ t - η • (fun t => -payoff m (w t) (y t)) t - x
        = (θ t - x) + η • payoff m (w t) (y t) := by
      simp only [smul_neg, sub_neg_eq_add]; abel
    rw [hexp, norm_add_sq_real, norm_smul, inner_smul_right, inner_sub_left,
      Real.norm_eq_abs, abs_of_pos hηpos] at h
    have ho := horacle t ht1 htT
    have hn := hnorm t ht1 htT
    rw [real_inner_comm (payoff m (w t) (y t)) (θ t), real_inner_comm (payoff m (w t) (y t)) x,
      mul_pow] at h
    have e1 : η * inner ℝ (payoff m (w t) (y t)) (θ t) ≤ η * (eps m / 2) :=
      mul_le_mul_of_nonneg_left ho hηpos.le
    have e2 : η ^ 2 * ‖payoff m (w t) (y t)‖ ^ 2 ≤ η ^ 2 :=
      mul_le_of_le_one_right (sq_nonneg η) hn
    nlinarith
  -- telescoping
  have hind : ∀ x ∈ cube (m + 1), ∀ n, n ≤ T →
      ‖θ (n + 1) - x‖ ^ 2 + 2 * η * ∑ t ∈ Finset.Icc 1 n, inner ℝ (payoff m (w t) (y t)) x
        ≤ ‖x‖ ^ 2 + n * (η * eps m + η ^ 2) := by
    intro x hx n
    induction n with
    | zero => intro _; simp [h1]
    | succ k ih =>
      intro hk
      rw [Finset.sum_Icc_succ_top (by omega), mul_add]
      have := ih (by omega)
      have := hstep x hx (k + 1) (by omega) hk
      push_cast
      nlinarith
  -- the sign vector
  set S : Fin (m + 1) → ℝ := fun i =>
    ∑ t ∈ Finset.Icc 1 T, w t i * (y t - ((i : ℕ) : ℝ) / (m : ℝ)) with hS
  set x : ApproachRegret.ToOLO.E (m + 1) :=
    WithLp.toLp 2 (fun i => if 0 ≤ S i then (1 : ℝ) else -1) with hxdef
  have hxc : x ∈ cube (m + 1) := by
    intro i
    simp only [hxdef, PiLp.toLp_apply]
    split_ifs <;> simp
  have hxn : ‖x‖ ^ 2 = (m : ℝ) + 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hxdef, PiLp.toLp_apply]
    have : ∀ i : Fin (m + 1), ‖(if 0 ≤ S i then (1 : ℝ) else -1)‖ ^ 2 = 1 := by
      intro i; split_ifs <;> simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast; ring
  have hsumx : ∑ t ∈ Finset.Icc 1 T, inner ℝ (payoff m (w t) (y t)) x = ∑ i, |S i| := by
    simp only [p5da_inner_eq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    have : ∑ t ∈ Finset.Icc 1 T, (payoff m (w t) (y t)) i = S i := by
      simp only [hS, payoff, PiLp.toLp_apply]
    rw [this]
    simp only [hxdef, PiLp.toLp_apply]
    split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hcal : (∑ i : Fin (m + 1),
      |(1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, w t i * (((i : ℕ) : ℝ) / (m : ℝ) - y t)|)
        = (1 / (T : ℝ)) * ∑ i, |S i| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / T)]
    congr 1
    rw [← abs_neg]
    congr 1
    simp only [hS, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hfin := hind x hxc T le_rfl
  rw [hsumx, hxn] at hfin
  have hA : ∑ i, |S i| ≤ η * T + T * eps m / 2 := by
    have hm1 : (m : ℝ) + 1 = η ^ 2 * T := by rw [hηsq]; field_simp
    rw [hm1] at hfin
    have h0 := sq_nonneg ‖θ (T + 1) - x‖
    have : 2 * η * (∑ i, |S i| - (η * T + T * eps m / 2)) ≤ 0 := by nlinarith
    have := (mul_nonpos_iff.1 this)
    rcases this with ⟨h2, _⟩ | ⟨h2, h3⟩
    · nlinarith
    · linarith
  have hrate : calibRate m T w y ≤ η := by
    unfold calibRate
    rw [hcal]
    apply max_le hηpos.le
    have : (1 / (T : ℝ)) * ∑ i, |S i| ≤ (1 / (T : ℝ)) * (η * T + T * eps m / 2) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have h2 : (1 / (T : ℝ)) * (η * T + T * eps m / 2) = η + eps m / 2 := by
      field_simp
    linarith
  refine hrate.trans (Real.sqrt_le_sqrt ?_)
  unfold eps
  rw [div_le_div_iff₀ hTpos (by positivity)]
  have hm2 : ((m : ℝ) + 1) * (1 / m) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ hmpos]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  nlinarith
