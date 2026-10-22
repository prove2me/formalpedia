-- Prove2me | solution 1 for AffinePolicies.LargeGap.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:31:54.857718+00:00
-- url     : https://prove2.me/submissions/24702c8f-d5cd-4d8d-8e44-7528ed067172

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

set_option autoImplicit false
open AffinePolicies.LargeGap Matrix

theorem apl_Bmul (m : ℕ) (ρ : ℝ) (y : Fin m → ℝ) (i : Fin m) :
    ((fun i j : Fin m => if i = j then (1 : ℝ) else ρ : Matrix (Fin m) (Fin m) ℝ) *ᵥ y) i
      = (1 - ρ) * y i + ρ * ∑ j, y j := by
  simp only [Matrix.mulVec, dotProduct]
  have : ∀ j, (if i = j then (1 : ℝ) else ρ) * y j =
      ρ * y j + (if i = j then (1 - ρ) * y j else 0) := by
    intro j
    by_cases h : i = j
    · simp [h]; ring
    · simp [h]
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [Finset.sum_ite_eq]
  ring

theorem apl_B19 (m : ℕ) (δ : ℝ) (y : Fin m → ℝ) (i : Fin m) :
    (B19 m δ *ᵥ y) i = (1 - theta0 m δ) * y i + theta0 m δ * ∑ j, y j :=
  apl_Bmul m (theta0 m δ) y i

/-- the set of right-hand sides that can be covered at cost at most 1 -/
def aplW (m : ℕ) (δ : ℝ) : Set (Fin m → ℝ) :=
  {b | ∃ y : Fin m → ℝ, 0 ≤ y ∧ b ≤ B19 m δ *ᵥ y ∧ ∑ i, y i ≤ 1}

theorem apl_W_convex (m : ℕ) (δ : ℝ) : Convex ℝ (aplW m δ) := by
  intro b₁ ⟨y₁, h0₁, hb₁, hs₁⟩ b₂ ⟨y₂, h0₂, hb₂, hs₂⟩ a c ha hc hac
  refine ⟨a • y₁ + c • y₂, ?_, ?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := h0₁ i; have := h0₂ i
    simp only [Pi.zero_apply] at *
    positivity
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hb₁ i; have h2 := hb₂ i
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith

theorem apl_theta_nonneg (m : ℕ) (δ : ℝ) : 0 ≤ theta0 m δ := by
  unfold theta0
  positivity

theorem apl_two_le (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m
  · simp [Real.zero_rpow hδ.ne'] at hm
    linarith
  · simp at hm

theorem apl_inv_sqrt_le (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 2 ≤ m) :
    1 / Real.sqrt m ≤ theta0 m δ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hm0 : (0 : ℝ) < m := by linarith
  unfold theta0
  rw [Real.sqrt_eq_rpow]
  apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hm0 _)
  exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)

theorem apl_theta_le_one_of_univ (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 2 ≤ m)
    (hr : rr m δ = m) : theta0 m δ ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hm0 : (0 : ℝ) < m := by linarith
  have h1 : 0 < 1 - δ := by
    by_contra h
    push_neg at h
    have h2 : (m : ℝ) ^ (1 - δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 h
    have h3 : rr m δ ≤ 1 := by
      unfold rr
      exact Nat.ceil_le.mpr (by simpa using h2)
    omega
  unfold theta0
  rw [div_le_one (Real.rpow_pos_of_pos hm0 _)]
  exact Real.one_le_rpow hm1 (by linarith)

theorem apl_gen_mem (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 2 ≤ m) (b : Fin m → ℝ)
    (hb : b ∈ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
      {fun _ => 1 / Real.sqrt m} ∪
      {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S} : Set (Fin m → ℝ))) :
    b ∈ aplW m δ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hρ0 : 0 ≤ theta0 m δ := apl_theta_nonneg m δ
  have hsq : (1 : ℝ) ≤ Real.sqrt m := by
    rw [Real.one_le_sqrt]; exact hm1
  have hs1 : 1 / Real.sqrt m ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hsq
  have hs_ρ := apl_inv_sqrt_le δ hδ m hm
  -- y = e_k covers every b with b_k ≤ 1 and b_i ≤ θ₀ otherwise
  have hek : ∀ (k : Fin m) (b : Fin m → ℝ), b k ≤ 1 → (∀ i, i ≠ k → b i ≤ theta0 m δ) →
      b ∈ aplW m δ := by
    intro k b hbk hbi
    refine ⟨Pi.single k 1, ?_, ?_, by simp⟩
    · intro i; by_cases h : i = k <;> simp [h]
    · intro i
      rw [apl_B19]
      have hs : ∑ j, (Pi.single k (1 : ℝ) : Fin m → ℝ) j = 1 := by simp
      rw [hs]
      by_cases h : i = k
      · subst h; simp; exact hbk
      · simp [h]; exact hbi i h
  have hk0 : 0 < m := by omega
  rcases hb with ((hb | hb) | hb) | hb
  · have : b = 0 := hb
    subst this
    exact ⟨0, le_rfl, by simp, by simp⟩
  · obtain ⟨j, rfl⟩ := hb
    apply hek j
    · simp
    · intro i hij; simp [hij, hρ0]
  · have : b = fun _ => 1 / Real.sqrt m := hb
    subst this
    apply hek ⟨0, hk0⟩
    · exact hs1
    · intro i _; exact hs_ρ
  · obtain ⟨S, hS, rfl⟩ := hb
    by_cases hex : ∃ k, k ∉ S
    · obtain ⟨k, hk⟩ := hex
      apply hek k
      · simp [blockPt, hk]
      · intro i _
        unfold blockPt
        split_ifs <;> simp [hρ0]
    · push_neg at hex
      have hSu : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hex
      have hr : rr m δ = m := by rw [← hS, hSu]; simp
      have hθ1 := apl_theta_le_one_of_univ δ hδ m hm hr
      refine ⟨fun _ => 1 / (m : ℝ), fun i => by positivity, ?_, ?_⟩
      · intro i
        rw [apl_B19]
        have hs : ∑ _j : Fin m, 1 / (m : ℝ) = 1 := by
          simp; field_simp
        rw [hs]
        have : 0 ≤ (1 - theta0 m δ) * (1 / (m : ℝ)) := by
          apply mul_nonneg <;> [linarith; positivity]
        unfold blockPt
        rw [hSu]
        simp only [one_div] at this
        simp
        linarith
      · simp; field_simp; exact le_rfl

theorem solution (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) :
    (∃ (x : Fin m → ℝ) (y : (Fin m → ℝ) → Fin m → ℝ),
        AffinePolicies.Simplex.Feasible (A19 m) (B19 m δ) (U19 m δ) x y ∧
          AffinePolicies.Simplex.CostLE (c19 m) (d19 m) (U19 m δ) x y 1) ∧
      AffinePolicies.Simplex.zAdapt (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) ≤ 1 := by
  classical
  have hm2 := apl_two_le δ hδ m hm
  have hU : U19 m δ ⊆ aplW m δ := by
    unfold U19
    exact convexHull_min (fun b hb => apl_gen_mem δ hδ m hm2 b hb) (apl_W_convex m δ)
  let y : (Fin m → ℝ) → Fin m → ℝ := fun b => if h : b ∈ aplW m δ then Classical.choose h else 0
  have hy : ∀ b ∈ U19 m δ, 0 ≤ y b ∧ b ≤ B19 m δ *ᵥ y b ∧ ∑ i, y b i ≤ 1 := by
    intro b hb
    have h : b ∈ aplW m δ := hU hb
    simp only [y, dif_pos h]
    exact Classical.choose_spec h
  have hfeas : AffinePolicies.Simplex.Feasible (A19 m) (B19 m δ) (U19 m δ) 0 y := by
    refine ⟨le_rfl, fun b hb => ⟨(hy b hb).1, ?_⟩⟩
    have := (hy b hb).2.1
    simpa [A19] using this
  have hcost : AffinePolicies.Simplex.CostLE (c19 m) (d19 m) (U19 m δ) 0 y 1 := by
    intro b hb
    have := (hy b hb).2.2
    simpa [c19, d19, dotProduct] using this
  refine ⟨⟨0, y, hfeas, hcost⟩, ?_⟩
  unfold AffinePolicies.Simplex.zAdapt
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨x', y', ⟨hx', hy'⟩, hc⟩
    have h0 : (0 : Fin m → ℝ) ∈ U19 m δ := by
      unfold U19
      exact subset_convexHull ℝ _ (Or.inl (Or.inl (Or.inl rfl)))
    have := hc 0 h0
    have h2 : 0 ≤ c19 m ⬝ᵥ x' + d19 m ⬝ᵥ y' 0 := by
      simp only [c19, d19, dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, one_mul, zero_add]
      exact Finset.sum_nonneg fun i _ => (hy' 0 h0).1 i
    linarith
  · exact ⟨0, y, hfeas, hcost⟩
