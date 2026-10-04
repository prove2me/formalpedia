-- Prove2me | solution 1 for AppliedComb.ManyFaces.local_lemma_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:19:06.79105+00:00
-- url     : https://prove2.me/submissions/3949fc61-0550-4d18-b1be-a55cc053ffd6

import Mathlib
import Definitions.Def_AppliedComb_ManyFaces_IndepOutside

open MeasureTheory

namespace LLLAux

open AppliedComb.ManyFaces

set_option linter.unusedSectionVars false

variable {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]

lemma allFail_insert [DecidableEq ι] (A : ι → Set Ω) (a : ι) (S : Finset ι) :
    allFail A (insert a S) = allFail A S \ A a := by
  ext ω
  simp only [allFail, Finset.mem_insert, Set.mem_iInter, Set.mem_compl_iff, Set.mem_sdiff]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Or.inr hj), h a (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩ j (rfl | hj)
    · exact h2
    · exact h1 j hj

lemma allFail_empty (A : ι → Set Ω) : allFail A ∅ = Set.univ := by
  simp [allFail]

lemma allFail_anti (A : ι → Set Ω) {S T : Finset ι} (h : S ⊆ T) :
    allFail A T ⊆ allFail A S := by
  intro ω hω
  simp only [allFail, Set.mem_iInter] at hω ⊢
  exact fun j hj => hω j (h hj)

/-- Removing one failing event: `P(Ā_a ∩ F) = P(F) - P(A_a ∩ F)`. -/
lemma real_allFail_insert [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (a : ι) (S : Finset ι) :
    μ.real (allFail A (insert a S)) = μ.real (allFail A S) - μ.real (A a ∩ allFail A S) := by
  rw [allFail_insert, Set.inter_comm]
  have h := measureReal_inter_add_sdiff (μ := μ) (s := allFail A S) (t := A a)
    (MeasurableSet.of_discrete)
  linarith

lemma prod_le_prod_of_subset_of_le_one' {ι : Type*} [DecidableEq ι] {s t : Finset ι} (h : s ⊆ t)
    (f : ι → ℝ) (h0 : ∀ j, 0 ≤ f j) (h1 : ∀ j, f j ≤ 1) :
    ∏ j ∈ t, f j ≤ ∏ j ∈ s, f j := by
  rw [← Finset.prod_sdiff h]
  have : ∏ j ∈ t \ s, f j ≤ 1 := Finset.prod_le_one (fun j _ => h0 j) (fun j _ => h1 j)
  have hp : 0 ≤ ∏ j ∈ s, f j := Finset.prod_nonneg (fun j _ => h0 j)
  nlinarith

/-- The core of the Local Lemma, proved by induction on the size of the subfamily. -/
theorem core [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (N : ι → Finset ι)
    (hind : ∀ i, IndepOutside μ A N i) (x : ι → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∀ n : ℕ, ∀ S : Finset ι, S.card < n →
      (∏ j ∈ S, (1 - x j) ≤ μ.real (allFail A S)) ∧
      ∀ i, i ∉ S → μ.real (A i ∩ allFail A S) ≤ x i * μ.real (allFail A S) := by
  intro n
  induction n with
  | zero => intro S hS; exact absurd hS (Nat.not_lt_zero _)
  | succ n ih =>
    intro S hSn
    have hSle : S.card ≤ n := Nat.lt_succ_iff.mp hSn
    have h0 : ∀ j, 0 ≤ 1 - x j := fun j => by linarith [(hx j).2]
    have h1 : ∀ j, 1 - x j ≤ 1 := fun j => by linarith [(hx j).1]
    -- the second claim
    have hR : ∀ i, i ∉ S → μ.real (A i ∩ allFail A S) ≤ x i * μ.real (allFail A S) := by
      intro i hi
      set S₂ : Finset ι := S \ N i with hS₂
      set S₁ : Finset ι := S ∩ N i with hS₁
      have hS₂S : S₂ ⊆ S := Finset.sdiff_subset
      have hS₁S : S₁ ⊆ S := Finset.inter_subset_left
      have hS₁N : S₁ ⊆ N i := Finset.inter_subset_right
      have hdisj : Disjoint S₂ (N i) := Finset.sdiff_disjoint
      have hiS₂ : i ∉ S₂ := fun h => hi (hS₂S h)
      -- chain: peel off the elements of `S₁` one at a time
      have chain : ∀ T : Finset ι, T ⊆ S₁ →
          (∏ j ∈ T, (1 - x j)) * μ.real (allFail A S₂) ≤ μ.real (allFail A (S₂ ∪ T)) := by
        intro T
        induction T using Finset.induction_on with
        | empty => intro _; simp
        | insert a T haT ihT =>
          intro hT
          have hTS₁ : T ⊆ S₁ := fun y hy => hT (Finset.mem_insert_of_mem hy)
          have haS₁ : a ∈ S₁ := hT (Finset.mem_insert_self a T)
          have haS : a ∈ S := hS₁S haS₁
          have haN : a ∈ N i := hS₁N haS₁
          set U : Finset ι := S₂ ∪ T with hU
          have haU : a ∉ U := by
            intro h
            rcases Finset.mem_union.mp h with h | h
            · exact (Finset.mem_sdiff.mp h).2 haN
            · exact haT h
          have hUS : U ⊆ S := Finset.union_subset hS₂S (hTS₁.trans hS₁S)
          have hUcard : U.card < n := by
            have : U.card < S.card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
                ⟨hUS, fun h => haU (h ▸ haS)⟩)
            omega
          have hRU := (ih U hUcard).2 a haU
          have hQU := ihT hTS₁
          have heq : S₂ ∪ insert a T = insert a U := by
            rw [hU, Finset.union_insert]
          rw [heq, real_allFail_insert, Finset.prod_insert haT]
          have hnn : 0 ≤ 1 - x a := h0 a
          have hP0 : 0 ≤ μ.real (allFail A S₂) := measureReal_nonneg
          calc (1 - x a) * (∏ j ∈ T, (1 - x j)) * μ.real (allFail A S₂)
              = (1 - x a) * ((∏ j ∈ T, (1 - x j)) * μ.real (allFail A S₂)) := by ring
            _ ≤ (1 - x a) * μ.real (allFail A U) := mul_le_mul_of_nonneg_left hQU hnn
            _ ≤ μ.real (allFail A U) - μ.real (A a ∩ allFail A U) := by nlinarith
      have hchain := chain S₁ le_rfl
      have hSU : S₂ ∪ S₁ = S := Finset.sdiff_union_inter S (N i)
      rw [hSU] at hchain
      -- independence of `A i` from the failures outside `N i`
      have hind' := hind i S₂ hiS₂ hdisj
      have hmono : μ.real (A i ∩ allFail A S) ≤ μ.real (A i ∩ allFail A S₂) :=
        measureReal_mono (Set.inter_subset_inter_right _ (allFail_anti A hS₂S))
      have hprod : ∏ j ∈ N i, (1 - x j) ≤ ∏ j ∈ S₁, (1 - x j) :=
        prod_le_prod_of_subset_of_le_one' hS₁N _ h0 h1
      have hP2 : 0 ≤ μ.real (allFail A S₂) := measureReal_nonneg
      have hxi : 0 < x i := (hx i).1
      calc μ.real (A i ∩ allFail A S) ≤ μ.real (A i ∩ allFail A S₂) := hmono
        _ = μ.real (A i) * μ.real (allFail A S₂) := hind'
        _ ≤ (x i * ∏ j ∈ N i, (1 - x j)) * μ.real (allFail A S₂) :=
            mul_le_mul_of_nonneg_right (hP i) hP2
        _ ≤ (x i * ∏ j ∈ S₁, (1 - x j)) * μ.real (allFail A S₂) := by
            apply mul_le_mul_of_nonneg_right _ hP2
            exact mul_le_mul_of_nonneg_left hprod hxi.le
        _ = x i * ((∏ j ∈ S₁, (1 - x j)) * μ.real (allFail A S₂)) := by ring
        _ ≤ x i * μ.real (allFail A S) := mul_le_mul_of_nonneg_left hchain hxi.le
    -- the first claim
    refine ⟨?_, hR⟩
    rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
    · simp [allFail_empty]
    · set S' : Finset ι := S.erase k with hS'
      have hS'card : S'.card < n := by
        have : S'.card < S.card := Finset.card_erase_lt_of_mem hk
        omega
      obtain ⟨hQ', hR'⟩ := ih S' hS'card
      have hkS' : k ∉ S' := Finset.notMem_erase k S
      have hS : S = insert k S' := (Finset.insert_erase hk).symm
      rw [hS, real_allFail_insert, Finset.prod_insert hkS']
      have hnn : 0 ≤ 1 - x k := h0 k
      have := hR' k hkS'
      calc (1 - x k) * ∏ j ∈ S', (1 - x j) ≤ (1 - x k) * μ.real (allFail A S') :=
            mul_le_mul_of_nonneg_left hQ' hnn
        _ ≤ μ.real (allFail A S') - μ.real (A k ∩ allFail A S') := by nlinarith


/-- `(1 - 1/(d+1))^m ≥ 1/e` whenever `m ≤ d` and `1 ≤ d`. -/
lemma pow_ge_inv_exp {d : ℝ} (hd : 1 ≤ d) {m : ℕ} (hm : (m : ℝ) ≤ d) :
    Real.exp (-1) ≤ (1 - 1 / (d + 1)) ^ m := by
  have hd0 : 0 < d := by linarith
  have hq : (1 - 1 / (d + 1)) * (1 + 1 / d) = 1 := by field_simp; ring
  have hq0 : 0 ≤ 1 - 1 / (d + 1) := by
    have : 1 / (d + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have h1 : (1 + 1 / d) ^ m ≤ Real.exp 1 := by
    calc (1 + 1 / d) ^ m ≤ (Real.exp (1 / d)) ^ m := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [Real.add_one_le_exp (1 / d)]
      _ = Real.exp (m * (1 / d)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 1 := by
          apply Real.exp_le_exp.mpr
          rw [mul_one_div, div_le_one hd0]; exact hm
  have h2 : (1 - 1 / (d + 1)) ^ m * (1 + 1 / d) ^ m = 1 := by
    rw [← mul_pow, hq, one_pow]
  have h3 : 0 ≤ (1 - 1 / (d + 1)) ^ m := pow_nonneg hq0 m
  have h4 : 1 ≤ (1 - 1 / (d + 1)) ^ m * Real.exp 1 := by
    calc (1 : ℝ) = (1 - 1 / (d + 1)) ^ m * (1 + 1 / d) ^ m := h2.symm
      _ ≤ (1 - 1 / (d + 1)) ^ m * Real.exp 1 := mul_le_mul_of_nonneg_left h1 h3
  rw [Real.exp_neg]
  rw [inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
  linarith [mul_comm ((1 - 1 / (d + 1)) ^ m) (Real.exp 1)]

end LLLAux

open LLLAux AppliedComb.ManyFaces in
/-- The Lovász Local Lemma, symmetric form. -/
theorem solution {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p d : ℝ) (hp : 0 < p ∧ p < 1) (hd : 1 ≤ d)
    (A : ι → Set Ω) (N : ι → Finset ι) (hN : ∀ i, i ∉ N i)
    (hind : ∀ i, IndepOutside μ A N i)
    (hPp : ∀ i, μ.real (A i) ≤ p) (hNd : ∀ i, ((N i).card : ℝ) ≤ d)
    (he : Real.exp 1 * p * (d + 1) < 1) :
    (1 - 1 / (d + 1)) ^ Fintype.card ι ≤ μ.real (allFail A Finset.univ) ∧
      0 < μ.real (allFail A Finset.univ) := by
  classical
  have hd1 : 0 < d + 1 := by linarith
  have hx0 : 0 < 1 / (d + 1) := one_div_pos.mpr hd1
  have hx1 : 1 / (d + 1) < 1 := by rw [div_lt_one hd1]; linarith
  have hq0 : 0 < 1 - 1 / (d + 1) := by linarith
  have hx : ∀ _ : ι, 0 < (1 : ℝ) / (d + 1) ∧ (1 : ℝ) / (d + 1) < 1 := fun _ => ⟨hx0, hx1⟩
  have hP : ∀ i, μ.real (A i) ≤ (fun _ : ι => (1 : ℝ) / (d + 1)) i *
      ∏ j ∈ N i, (1 - (fun _ : ι => (1 : ℝ) / (d + 1)) j) := by
    intro i
    simp only [Finset.prod_const]
    have h1 := pow_ge_inv_exp hd (hNd i)
    have h2 : p ≤ 1 / (d + 1) * Real.exp (-1) := by
      rw [Real.exp_neg, show 1 / (d + 1) * (Real.exp 1)⁻¹ = 1 / ((d + 1) * Real.exp 1) by
        field_simp]
      rw [le_div_iff₀ (mul_pos hd1 (Real.exp_pos 1))]
      calc p * ((d + 1) * Real.exp 1) = Real.exp 1 * p * (d + 1) := by ring
        _ ≤ 1 := he.le
    calc μ.real (A i) ≤ p := hPp i
      _ ≤ 1 / (d + 1) * Real.exp (-1) := h2
      _ ≤ 1 / (d + 1) * (1 - 1 / (d + 1)) ^ (N i).card :=
          mul_le_mul_of_nonneg_left h1 hx0.le
  have key : (1 - 1 / (d + 1)) ^ Fintype.card ι ≤ μ.real (allFail A Finset.univ) := by
    have := (LLLAux.core μ A N hind (fun _ => (1 : ℝ) / (d + 1)) hx hP
      (Finset.univ.card + 1) Finset.univ (Nat.lt_succ_self _)).1
    simpa [Finset.prod_const] using this
  exact ⟨key, lt_of_lt_of_le (pow_pos hq0 _) key⟩
