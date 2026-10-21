-- Prove2me | solution 1 for AffinePolicies.TwoGap.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:50:26.035859+00:00
-- url     : https://prove2.me/submissions/b829f8ee-421d-420e-9641-0f2393fc07f4

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

set_option autoImplicit false
open AffinePolicies.TwoGap Matrix

theorem apt_Bmul (m : ℕ) (y : Fin m → ℝ) (i : Fin m) :
    (B6 m *ᵥ y) i = (1 - 1 / Real.sqrt m) * y i + (1 / Real.sqrt m) * ∑ j, y j := by
  simp only [Matrix.mulVec, dotProduct, B6]
  have : ∀ j, (if i = j then (1 : ℝ) else 1 / Real.sqrt m) * y j =
      (1 / Real.sqrt m) * y j + (if i = j then (1 - 1 / Real.sqrt m) * y j else 0) := by
    intro j
    by_cases h : i = j
    · simp [h]; ring
    · simp [h]
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [Finset.sum_ite_eq]
  ring

/-- the set of right-hand sides that can be covered at cost at most 1 -/
def aptW (m : ℕ) : Set (Fin m → ℝ) :=
  {b | ∃ y : Fin m → ℝ, 0 ≤ y ∧ b ≤ B6 m *ᵥ y ∧ ∑ i, y i ≤ 1}

theorem apt_W_convex (m : ℕ) : Convex ℝ (aptW m) := by
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

theorem apt_gen_mem (m : ℕ) (b : Fin m → ℝ)
    (hb : b ∈ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
      {bLow m, bHigh m} : Set (Fin m → ℝ))) : b ∈ aptW m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨0, le_rfl, fun i => i.elim0, by simp⟩
  have hsq : (1 : ℝ) ≤ Real.sqrt m := by
    rw [Real.one_le_sqrt]; exact_mod_cast hm
  have hρ0 : 0 < 1 / Real.sqrt m := by positivity
  have hρ1 : 1 / Real.sqrt m ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hsq
  have hcommon : ∀ b : Fin m → ℝ, (∀ i, b i ≤ 1 / Real.sqrt m) → b ∈ aptW m := by
    intro b hb
    refine ⟨fun _ => 1 / (m : ℝ), fun i => by positivity, ?_, ?_⟩
    · intro i
      rw [apt_Bmul]
      have hs : ∑ _j : Fin m, 1 / (m : ℝ) = 1 := by
        simp; field_simp
      rw [hs]
      have : 0 ≤ (1 - 1 / Real.sqrt m) * (1 / (m : ℝ)) := by
        apply mul_nonneg <;> [linarith; positivity]
      linarith [hb i]
    · simp; field_simp; exact le_rfl
  rcases hb with (hb | hb) | hb
  · have : b = 0 := hb
    subst this
    exact ⟨0, le_rfl, by simp, by simp⟩
  · obtain ⟨j, rfl⟩ := hb
    refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
    · intro i; by_cases h : i = j <;> simp [h]
    · intro i
      rw [apt_Bmul]
      have hs : ∑ k, (Pi.single j (1 : ℝ) : Fin m → ℝ) k = 1 := by simp
      rw [hs]
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    · simp
  · rcases hb with hb | hb
    · subst hb
      apply hcommon
      intro i; unfold bLow; split_ifs <;> simp [hρ0.le]
    · have : b = bHigh m := hb
      subst this
      apply hcommon
      intro i; unfold bHigh; split_ifs <;> simp [hρ0.le]

theorem solution (m : ℕ) (hm_even : Even m) :
    (∃ (x : Fin m → ℝ) (y : (Fin m → ℝ) → Fin m → ℝ),
      AffinePolicies.Simplex.Feasible (A6 m) (B6 m) (U6 m) x y ∧ AffinePolicies.Simplex.CostLE (c6 m) (d6 m) (U6 m) x y 1) ∧
    AffinePolicies.Simplex.zAdapt (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) ≤ 1 := by
  classical
  have hU : U6 m ⊆ aptW m := by
    unfold U6
    exact convexHull_min (fun b hb => apt_gen_mem m b hb) (apt_W_convex m)
  let y : (Fin m → ℝ) → Fin m → ℝ := fun b => if h : b ∈ aptW m then Classical.choose h else 0
  have hy : ∀ b ∈ U6 m, 0 ≤ y b ∧ b ≤ B6 m *ᵥ y b ∧ ∑ i, y b i ≤ 1 := by
    intro b hb
    have h : b ∈ aptW m := hU hb
    simp only [y, dif_pos h]
    exact Classical.choose_spec h
  have hfeas : AffinePolicies.Simplex.Feasible (A6 m) (B6 m) (U6 m) 0 y := by
    refine ⟨le_rfl, fun b hb => ⟨(hy b hb).1, ?_⟩⟩
    have := (hy b hb).2.1
    simpa [A6] using this
  have hcost : AffinePolicies.Simplex.CostLE (c6 m) (d6 m) (U6 m) 0 y 1 := by
    intro b hb
    have := (hy b hb).2.2
    simpa [c6, d6, dotProduct] using this
  refine ⟨⟨0, y, hfeas, hcost⟩, ?_⟩
  unfold AffinePolicies.Simplex.zAdapt
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨x', y', ⟨hx', hy'⟩, hc⟩
    have h0 : (0 : Fin m → ℝ) ∈ U6 m := by
      unfold U6
      exact subset_convexHull ℝ _ (Or.inl (Or.inl rfl))
    have := hc 0 h0
    have h2 : 0 ≤ c6 m ⬝ᵥ x' + d6 m ⬝ᵥ y' 0 := by
      simp only [c6, d6, dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, one_mul, zero_add]
      exact Finset.sum_nonneg fun i _ => (hy' 0 h0).1 i
    linarith
  · exact ⟨0, y, hfeas, hcost⟩
