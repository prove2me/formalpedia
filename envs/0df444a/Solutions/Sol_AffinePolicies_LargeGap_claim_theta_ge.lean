-- Prove2me | solution 1 for AffinePolicies.LargeGap.claim_theta_ge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:53:38.160654+00:00
-- url     : https://prove2.me/submissions/f6c5d692-739d-461f-a8e0-dc42d6c80b59

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting



namespace AffinePolicies.LargeGap

open AffinePolicies.Simplex Matrix

lemma g35_sym_apply {m : ℕ} (θ μ lam : ℝ) (b : Fin m → ℝ) (i : Fin m) :
    affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam) b i
      = (θ - μ) * b i + μ * ∑ k, b k + lam := by
  simp only [affinePolicy, Matrix.mulVec, dotProduct, Pi.add_apply]
  have : ∀ k, (if i = k then θ else μ) * b k
      = (θ - μ) * (if i = k then b k else 0) + μ * b k := by
    intro k; split_ifs <;> ring
  simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq]
  simp

lemma g35_B_apply {m : ℕ} (δ : ℝ) (y : Fin m → ℝ) (i : Fin m) :
    (B19 m δ *ᵥ y) i = y i + theta0 m δ * (∑ k, y k - y i) := by
  rw [show ∑ k, y k - y i = ∑ k ∈ Finset.univ.erase i, y k by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring]
  simp only [B19, Matrix.mulVec, dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [if_true, one_mul]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hk))]

lemma g35_cost {m : ℕ} (x y : Fin m → ℝ) :
    c19 m ⬝ᵥ x + d19 m ⬝ᵥ y = ∑ i, y i := by
  simp [c19, d19, dotProduct]

lemma g35_mem_zero (m : ℕ) (δ : ℝ) : (0 : Fin m → ℝ) ∈ U19 m δ :=
  subset_convexHull ℝ _ (Or.inl (Or.inl (Or.inl rfl)))

lemma g35_mem_single (m : ℕ) (δ : ℝ) (j : Fin m) :
    (Pi.single j (1:ℝ) : Fin m → ℝ) ∈ U19 m δ :=
  subset_convexHull ℝ _ (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))

lemma g35_mem_const (m : ℕ) (δ : ℝ) :
    (fun _ => 1 / Real.sqrt m : Fin m → ℝ) ∈ U19 m δ :=
  subset_convexHull ℝ _ (Or.inl (Or.inr rfl))

lemma g35_mem_block (m : ℕ) (δ : ℝ) (S : Finset (Fin m)) (hS : S.card = rr m δ) :
    blockPt m δ S ∈ U19 m δ :=
  subset_convexHull ℝ _ (Or.inr ⟨S, hS, rfl⟩)

/-- the power facts -/
lemma g35_pow (δ : ℝ) (m : ℕ) (hm0 : 0 < (m:ℝ)) :
    (m:ℝ) ^ ((1:ℝ)/2 - δ) = (m:ℝ) ^ ((1:ℝ)/2) / ((m:ℝ) ^ (δ/2)) ^ 2 ∧
    theta0 m δ = (m:ℝ) ^ (δ/2) / (m:ℝ) ^ ((1:ℝ)/2) ∧
    (m:ℝ) ^ (1 - δ) = ((m:ℝ) ^ ((1:ℝ)/2)) ^ 2 / ((m:ℝ) ^ (δ/2)) ^ 2 ∧
    (m:ℝ) ^ (1 + δ/2) = ((m:ℝ) ^ ((1:ℝ)/2)) ^ 2 * (m:ℝ) ^ (δ/2) ∧
    (m:ℝ) ^ δ = ((m:ℝ) ^ (δ/2)) ^ 2 ∧
    ((m:ℝ) ^ ((1:ℝ)/2)) ^ 2 = m ∧
    Real.sqrt m = (m:ℝ) ^ ((1:ℝ)/2) := by
  have sq : ∀ u : ℝ, ((m:ℝ) ^ u) ^ 2 = (m:ℝ) ^ (2 * u) := by
    intro u
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; ring_nf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sq, ← Real.rpow_sub hm0]; ring_nf
  · rw [theta0, ← Real.rpow_sub hm0, one_div, ← Real.rpow_neg hm0.le]; ring_nf
  · rw [sq, sq, ← Real.rpow_sub hm0]; ring_nf
  · rw [sq, ← Real.rpow_add hm0]; ring_nf
  · rw [sq]; ring_nf
  · rw [sq]; simp
  · rw [Real.sqrt_eq_rpow]

lemma g35_m_ge (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m
  all_goals (simp [Real.zero_rpow hδ.ne'] at hm <;> linarith)

/-- core of the claim on θ: θ ≥ 1/2 -/
lemma g35_theta_core (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ)
    (x : Fin m → ℝ) (μ θ lam : ℝ)
    (hfeas : Feasible (A19 m) (B19 m δ) (U19 m δ) x
      (affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam)))
    (hcost : CostLE (c19 m) (d19 m) (U19 m δ) x
      (affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam))
      ((m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4)) :
    0 ≤ lam ∧ lam * m ≤ (m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4 ∧ 1 / 2 ≤ θ := by
  have hm2 := g35_m_ge δ hδ m hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := g35_pow δ m hm0
  set a := (m:ℝ) ^ ((1:ℝ)/2) with ha
  set e := (m:ℝ) ^ (δ/2) with he
  have ha0 : 0 < a := Real.rpow_pos_of_pos hm0 _
  have he0 : 0 < e := Real.rpow_pos_of_pos hm0 _
  have ha1 : 1 ≤ a := by nlinarith
  have he1 : 1 ≤ e := by nlinarith
  set T := (m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4 with hT
  set y := affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam) with hy
  let j : Fin m := ⟨0, by omega⟩
  -- b = 0
  have f0 := (hfeas.2 0 (g35_mem_zero m δ)).1 j
  have c0 := hcost 0 (g35_mem_zero m δ)
  rw [g35_cost] at c0
  simp only [hy, g35_sym_apply, Pi.zero_apply, Finset.sum_const_zero] at f0 c0
  simp only [mul_zero, zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at f0 c0
  refine ⟨f0, by linarith, ?_⟩
  -- b = e_j
  have hb := g35_mem_single m δ j
  have fj := hfeas.2 _ hb
  have cj := hcost _ hb
  rw [g35_cost] at cj
  have hle := fj.2 j
  simp only [A19, Matrix.zero_mulVec, zero_add, g35_B_apply, Pi.single_eq_same] at hle
  have hnn : 0 ≤ ∑ k, y (Pi.single j 1) k - y (Pi.single j 1) j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [add_sub_cancel_left]
    exact Finset.sum_nonneg (fun k _ => fj.1 k)
  have hyj : y (Pi.single j 1) j = θ + lam := by
    rw [hy, g35_sym_apply]; simp
  have hyj0 : 0 ≤ y (Pi.single j 1) j := fj.1 j
  have hθ0 : 0 < theta0 m δ := by rw [h2]; positivity
  have hTpos : T = a / e ^ 2 / 4 := by rw [hT, h1]
  -- θ0 * (S - yj) ≤ θ0 * T ≤ 1/4
  have k1 : theta0 m δ * (∑ k, y (Pi.single j 1) k - y (Pi.single j 1) j) ≤ theta0 m δ * T :=
    mul_le_mul_of_nonneg_left (by linarith) hθ0.le
  have k2 : theta0 m δ * T ≤ 1 / 4 := by
    rw [h2, hTpos]
    have : e / a * (a / e ^ 2 / 4) = 1 / (4 * e) := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have k3 : lam ≤ 1 / 4 := by
    have : lam * m ≤ m / 4 := by
      calc lam * m ≤ T := by linarith
        _ = a / e ^ 2 / 4 := hTpos
        _ ≤ m / 4 := by
          rw [← h6]
          have : a / e ^ 2 ≤ a := div_le_self ha0.le (by nlinarith)
          nlinarith
    nlinarith
  linarith

theorem g35_theta_ge_core (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ)
    (x : Fin m → ℝ) (μ θ lam : ℝ)
    (hfeas : Feasible (A19 m) (B19 m δ) (U19 m δ) x
      (affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam)))
    (hcost : CostLE (c19 m) (d19 m) (U19 m δ) x
      (affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam))
      ((m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4)) :
    1 / 3 ≤ θ := by
  have := (g35_theta_core δ hδ m hm x μ θ lam hfeas hcost).2.2
  linarith

theorem g35_mu_bounds_core (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ)
    (x : Fin m → ℝ) (μ θ lam : ℝ)
    (hfeas : Feasible (A19 m) (B19 m δ) (U19 m δ) x
      (affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam)))
    (hcost : CostLE (c19 m) (d19 m) (U19 m δ) x
      (affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam))
      ((m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4)) :
    -(1 / (m : ℝ) ^ (1 + δ / 2)) ≤ μ ∧ μ < 0 := by
  obtain ⟨hl0, hlm, hθ⟩ := g35_theta_core δ hδ m hm x μ θ lam hfeas hcost
  have hm2 := g35_m_ge δ hδ m hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm2r : (2:ℝ) ≤ m := by exact_mod_cast hm2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := g35_pow δ m hm0
  set a := (m:ℝ) ^ ((1:ℝ)/2) with ha
  set e := (m:ℝ) ^ (δ/2) with he
  have ha0 : 0 < a := Real.rpow_pos_of_pos hm0 _
  have he0 : 0 < e := Real.rpow_pos_of_pos hm0 _
  have ha1 : 1 ≤ a := by nlinarith
  have he1 : 1 ≤ e := by nlinarith
  rw [h1] at hlm hcost
  rw [h4]
  set y := affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam) with hy
  let j : Fin m := ⟨0, by omega⟩
  have hμ : μ < 0 := by
    by_contra hcon
    push_neg at hcon
    have c1 := hcost _ (g35_mem_const m δ)
    rw [g35_cost] at c1
    simp only [hy, g35_sym_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, h7] at c1
    -- c1 : m * ((θ - μ) * (1/a) + μ * (m * (1/a)) + lam) ≤ a / e^2 / 4
    have hk : (m:ℝ) * ((θ - μ) * (1 / a) + μ * (m * (1 / a)) + lam) ≥ a * θ := by
      have e1 : (m:ℝ) * ((θ - μ) * (1 / a) + μ * (m * (1 / a)) + lam)
          = a * θ + a * μ * (m - 1) + m * lam := by
        rw [← h6]; field_simp; ring
      rw [e1]
      have : 0 ≤ a * μ * (m - 1) := by
        apply mul_nonneg (mul_nonneg ha0.le hcon); linarith
      nlinarith
    have : a / e ^ 2 / 4 ≤ a / 4 := by
      have : a / e ^ 2 ≤ a := div_le_self ha0.le (by nlinarith)
      linarith
    nlinarith
  refine ⟨?_, hμ⟩
  -- block point
  have hr : rr m δ ≤ m - 1 := by
    unfold rr
    rw [Nat.ceil_le, h3]
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hm1, ← h6, div_le_iff₀ (by positivity)]
    nlinarith
  have hcard : rr m δ ≤ (Finset.univ.erase j).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    exact hr
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
  have hjS : j ∉ S := fun h => by simpa using hSsub h
  have fb := (hfeas.2 _ (g35_mem_block m δ S hScard)).1 j
  simp only [hy, g35_sym_apply, blockPt, if_neg hjS, mul_zero, zero_add] at fb
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hScard, Pi.zero_apply] at fb
  -- fb : 0 ≤ μ * (rr * θ0) + lam
  have hrge : ((m:ℝ) ^ (1 - δ)) ≤ (rr m δ : ℝ) := Nat.le_ceil _
  rw [h3] at hrge
  rw [h2] at fb
  -- rr * θ0 ≥ a^2/e^2 * e/a = a/e
  have hprod : a / e ≤ (rr m δ : ℝ) * (e / a) := by
    calc a / e = a ^ 2 / e ^ 2 * (e / a) := by field_simp
      _ ≤ (rr m δ : ℝ) * (e / a) := mul_le_mul_of_nonneg_right hrge (by positivity)
  have hμ2 : μ * (a / e) ≥ - lam := by
    have : μ * ((rr m δ : ℝ) * (e / a)) ≤ μ * (a / e) :=
      mul_le_mul_of_nonpos_left hprod hμ.le
    linarith
  -- lam ≤ a/(4 e^2 m)
  have hl : lam ≤ a / e ^ 2 / 4 / a ^ 2 := by
    rw [le_div_iff₀ (by positivity), h6]; exact hlm
  have : -(a / e ^ 2 / 4 / a ^ 2) / (a / e) ≤ μ := by
    rw [div_le_iff₀ (by positivity)]; linarith
  calc -(1 / (a ^ 2 * e)) ≤ -(a / e ^ 2 / 4 / a ^ 2) / (a / e) := by
        rw [neg_div, neg_le_neg_iff]
        have : a / e ^ 2 / 4 / a ^ 2 / (a / e) = 1 / (4 * (a ^ 2 * e)) := by
          field_simp
        rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos (pow_pos ha0 2) he0]
    _ ≤ μ := this

end AffinePolicies.LargeGap

open AffinePolicies.LargeGap


theorem solution (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ)
    (x : Fin m → ℝ) (μ θ lam : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A19 m) (B19 m δ) (U19 m δ) x
      (AffinePolicies.Simplex.affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam)))
    (hcost : AffinePolicies.Simplex.CostLE (c19 m) (d19 m) (U19 m δ) x
      (AffinePolicies.Simplex.affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam))
      ((m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4)) :
    1 / 3 ≤ θ := by
  exact g35_theta_ge_core δ hδ m hm x μ θ lam hfeas hcost
