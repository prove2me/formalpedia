-- Prove2me | solution 1 for ABOThreshold.sparse_prob_ge
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:34:44.640138+00:00
-- url     : https://prove2.me/submissions/acdba7de-4d94-4d9e-a492-c757a8a9d361

import Definitions.Def_ABOThreshold_model

open ABOThreshold Finset

namespace Ag2Aux_ABOSparseGe

theorem sum0 (A : ℕ) (g : FaultPattern A 0 → ℝ) : ∑ p, g p = g true + g false :=
  (Fintype.sum_equiv (Equiv.refl Bool : FaultPattern A 0 ≃ Bool) g (fun b : Bool => g b)
    (fun _ => rfl)).trans (Fintype.sum_bool _)

theorem sz (A k : ℕ) (η : ℝ) : sparseProb A k η 0 = 1 - η := by
  unfold sparseProb
  rw [Finset.sum_filter]
  refine (sum0 A _).trans ?_
  simp [IsSparse, weight]

theorem cond_of_lt (D x : ℝ) (k : ℕ) (hk : 1 ≤ k) (hD : 0 ≤ D) (hx : 0 < x)
    (hlt : x < D ^ (-(1 : ℝ) / (k : ℝ))) : D * x ^ (k + 1) < x := by
  rcases hD.lt_or_eq with hD' | hD'
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have h1 : x ^ k < (D ^ (-(1 : ℝ) / (k : ℝ))) ^ k :=
      pow_lt_pow_left₀ hlt hx.le (by omega)
    have h2 : (D ^ (-(1 : ℝ) / (k : ℝ))) ^ k = D⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD'.le]
      rw [show -(1 : ℝ) / k * k = -1 by field_simp, Real.rpow_neg_one]
    rw [h2] at h1
    have h3 : D * x ^ k < 1 := by
      calc D * x ^ k < D * D⁻¹ := mul_lt_mul_of_pos_left h1 hD'
        _ = 1 := mul_inv_cancel₀ hD'.ne'
    calc D * x ^ (k + 1) = (D * x ^ k) * x := by ring
      _ < 1 * x := mul_lt_mul_of_pos_right h3 hx
      _ = x := one_mul x
  · subst hD'; simpa using hx

theorem tlc (A k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η)
    (hlt : η < thresholdProb A k) : ThresholdCondition A k η :=
  cond_of_lt _ η k hk (Nat.cast_nonneg _) hη hlt

theorem edc (A k : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hc : ThresholdCondition A k η) :
    ∃ δ : ℝ, 0 < δ ∧ (A.choose (k + 1) : ℝ) * η ^ (k + 1) < η ^ (1 + δ) := by
  have h1 : Filter.Tendsto (fun δ : ℝ => 1 + δ) (nhds 0) (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := nhds (0 : ℝ))).add
      (Filter.tendsto_id (x := nhds (0 : ℝ)))
    simpa using h
  have h2 : Filter.Tendsto (fun δ : ℝ => η ^ (1 + δ)) (nhds 0) (nhds η) := by
    have := ((Real.continuousAt_const_rpow (b := 1) hη.ne').tendsto).comp h1
    rw [Real.rpow_one] at this
    exact this
  have h3 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (A.choose (k + 1) : ℝ) * η ^ (k + 1) < η ^ (1 + δ) :=
    (h2.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hc)
  have h4 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ1, hδ2⟩ := (h4.and h3).exists
  exact ⟨δ, hδ1, hδ2⟩

theorem weight_total (A : ℕ) (η : ℝ) : ∀ r, ∑ p : FaultPattern A r, weight A η r p = 1
  | 0 => by
      refine (sum0 A _).trans ?_
      simp [weight]
  | r + 1 => by
      show ∑ p : (Fin A → FaultPattern A r), ∏ i : Fin A, weight A η r (p i) = 1
      rw [← Fintype.prod_sum]
      simp [weight_total A η r]

theorem weight_nonneg (A : ℕ) (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    ∀ r (p : FaultPattern A r), 0 ≤ weight A η r p
  | 0, b => by
      revert b
      show ∀ b : Bool, 0 ≤ weight A η 0 b
      intro b; cases b <;> simp [weight] <;> linarith
  | r + 1, p => by
      show 0 ≤ ∏ i : Fin A, weight A η r (p i)
      exact Finset.prod_nonneg fun i _ => weight_nonneg A η h0 h1 r (p i)

theorem badProb_eq (A k : ℕ) (η : ℝ) (r : ℕ) :
    badProb A k η r = ∑ p ∈ univ.filter (fun p : FaultPattern A r => IsSparse A k r p = false),
      weight A η r p := by
  unfold badProb sparseProb
  have h := Finset.sum_filter_add_sum_filter_not (univ : Finset (FaultPattern A r))
    (fun p => IsSparse A k r p = true) (weight A η r)
  rw [weight_total] at h
  simp only [Bool.not_eq_true] at h
  linarith

theorem badProb_nonneg (A k : ℕ) (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) (r : ℕ) :
    0 ≤ badProb A k η r := by
  rw [badProb_eq]
  exact Finset.sum_nonneg fun p _ => weight_nonneg A η h0 h1 r p

theorem bsl (A k : ℕ) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (r : ℕ) :
    badProb A k η (r + 1) ≤ (A.choose (k + 1) : ℝ) * badProb A k η r ^ (k + 1) := by
  classical
  set b := badProb A k η r with hb
  set bad : FaultPattern A r → ℝ := fun q => if IsSparse A k r q = false then 1 else 0 with hbad
  have hbsum : ∑ q : FaultPattern A r, weight A η r q * bad q = b := by
    rw [hb, badProb_eq, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : IsSparse A k r q = false <;> simp [hbad, hq]
  have hbad_nn : ∀ q, 0 ≤ bad q := fun q => by
    simp only [hbad]; split_ifs <;> norm_num
  set g : Finset (Fin A) → Fin A → FaultPattern A r → ℝ :=
    fun S i q => weight A η r q * (if i ∈ S then bad q else 1) with hg
  have hg_nn : ∀ S i q, 0 ≤ g S i q := fun S i q => by
    simp only [hg]
    apply mul_nonneg (weight_nonneg A η hη hη1 r q)
    split_ifs
    · exact hbad_nn q
    · norm_num
  rw [badProb_eq, Finset.sum_filter]
  change ∑ p : (Fin A → FaultPattern A r),
      (if IsSparse A k (r + 1) p = false then ∏ i : Fin A, weight A η r (p i) else 0) ≤ _
  have hpt : ∀ p : Fin A → FaultPattern A r,
      (if IsSparse A k (r + 1) p = false then ∏ i : Fin A, weight A η r (p i) else 0) ≤
        ∑ S ∈ powersetCard (k + 1) (univ : Finset (Fin A)), ∏ i, g S i (p i) := by
    intro p
    split_ifs with hp
    · have hp' : k < (univ.filter fun i : Fin A => IsSparse A k r (p i) = false).card := by
        have : IsSparse A k (r + 1) p =
            decide ((univ.filter fun i : Fin A => IsSparse A k r (p i) = false).card ≤ k) := rfl
        rw [this] at hp
        simpa using hp
      obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (s := univ.filter
        fun i : Fin A => IsSparse A k r (p i) = false) (n := k + 1) hp'
      have hSmem : S ∈ powersetCard (k + 1) (univ : Finset (Fin A)) := by
        rw [mem_powersetCard]; exact ⟨subset_univ _, hScard⟩
      have heq : ∏ i, g S i (p i) = ∏ i : Fin A, weight A η r (p i) := by
        apply Finset.prod_congr rfl
        intro i _
        simp only [hg]
        split_ifs with hi
        · have := hS hi
          simp only [mem_filter] at this
          simp [hbad, this.2]
        · ring
      rw [← heq]
      exact Finset.single_le_sum (f := fun S => ∏ i, g S i (p i))
        (fun S _ => Finset.prod_nonneg fun i _ => hg_nn S i (p i)) hSmem
    · exact Finset.sum_nonneg fun S _ => Finset.prod_nonneg fun i _ => hg_nn S i (p i)
  calc _ ≤ ∑ p : (Fin A → FaultPattern A r),
        ∑ S ∈ powersetCard (k + 1) (univ : Finset (Fin A)), ∏ i, g S i (p i) :=
          Finset.sum_le_sum fun p _ => hpt p
    _ = ∑ S ∈ powersetCard (k + 1) (univ : Finset (Fin A)),
          ∑ p : (Fin A → FaultPattern A r), ∏ i, g S i (p i) := Finset.sum_comm
    _ = ∑ S ∈ powersetCard (k + 1) (univ : Finset (Fin A)), b ^ (k + 1) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [mem_powersetCard] at hS
        rw [← Fintype.prod_sum]
        have : ∀ i, ∑ q, g S i q = if i ∈ S then b else 1 := by
          intro i
          by_cases hi : i ∈ S
          · simp [hg, hi, hbsum]
          · simp [hg, hi, weight_total]
        simp only [this]
        rw [Fintype.prod_ite_mem, Finset.prod_const, hS.2]
    _ = _ := by
        rw [Finset.sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem gen (x D δ : ℝ) (k : ℕ) (hx0 : 0 < x) (hx1 : x ≤ 1) (hδk : δ ≤ k) (hD : 0 ≤ D)
    (hthr : D * x ^ (k + 1) < x ^ (1 + δ)) (s : ℝ) (hs : 1 ≤ s) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c ≤ x ^ s) : D * c ^ (k + 1) ≤ x ^ (s * (1 + δ)) := by
  have h1 : c ^ (k + 1) ≤ (x ^ s) ^ (k + 1) := pow_le_pow_left₀ hc0 hc _
  have h2 : (x ^ s) ^ (k + 1) = x ^ ((k + 1 : ℕ) : ℝ) * x ^ ((s - 1) * ((k : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1; push_cast; ring
  rw [Real.rpow_natCast] at h2
  have hpos : 0 < x ^ ((s - 1) * ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hx0 _
  calc D * c ^ (k + 1) ≤ D * (x ^ s) ^ (k + 1) := mul_le_mul_of_nonneg_left h1 hD
    _ = (D * x ^ (k + 1)) * x ^ ((s - 1) * ((k : ℝ) + 1)) := by rw [h2]; ring
    _ ≤ x ^ (1 + δ) * x ^ ((s - 1) * ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hthr.le hpos.le
    _ = x ^ (1 + δ + (s - 1) * ((k : ℝ) + 1)) := (Real.rpow_add hx0 _ _).symm
    _ ≤ x ^ (s * (1 + δ)) := by
        apply Real.rpow_le_rpow_of_exponent_ge hx0 hx1
        nlinarith

end Ag2Aux_ABOSparseGe

open Ag2Aux_ABOSparseGe

theorem solution (A k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hlt : η < thresholdProb A k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 - η ^ ((1 + δ) ^ r) ≤ sparseProb A k η r := by
  obtain ⟨δ0, hδ0, hc⟩ := edc A k η hη hη1 (tlc A k hk η hη hlt)
  set δ := min δ0 1 with hδ
  have hδpos : 0 < δ := lt_min hδ0 one_pos
  have hδk : δ ≤ k := (min_le_right _ _).trans (by exact_mod_cast hk)
  have hc' : (A.choose (k + 1) : ℝ) * η ^ (k + 1) < η ^ (1 + δ) :=
    lt_of_lt_of_le hc (Real.rpow_le_rpow_of_exponent_ge hη hη1.le (by linarith [min_le_left δ0 1]))
  refine ⟨δ, hδpos, fun r => ?_⟩
  suffices h : badProb A k η r ≤ η ^ ((1 + δ) ^ r) by
    unfold badProb at h; linarith
  induction r with
  | zero =>
    unfold badProb; rw [sz]; simp
  | succ r ih =>
    have hs1 : (1 : ℝ) ≤ (1 + δ) ^ r := one_le_pow₀ (by linarith)
    have hg := gen η _ δ k hη hη1.le hδk (Nat.cast_nonneg _) hc' _ hs1 _
      (badProb_nonneg A k η hη.le hη1.le r) ih
    calc badProb A k η (r + 1) ≤ (A.choose (k + 1) : ℝ) * badProb A k η r ^ (k + 1) :=
          bsl A k η hη.le hη1.le r
      _ ≤ _ := hg
      _ = η ^ ((1 + δ) ^ (r + 1)) := by rw [pow_succ]
