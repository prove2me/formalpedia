-- Prove2me | solution 1 for AdaptSubCover.Rounds.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:21:03.444984+00:00
-- url     : https://prove2.me/submissions/d0889472-d83e-4547-91df-99c20ac2e748

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis
import Theorems.Thm_AdaptSubCover_Rounds_lemma_4_2

open AdaptSubCover.Rounds

namespace ASCL43

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem prob_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (ω : Fin m → U) :
    0 ≤ I.prob ω := Finset.prod_nonneg fun i _ => hp0 i (ω i)

theorem E_mono (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (F G : (Fin m → U) → ℝ)
    (h : ∀ ω, 0 < I.prob ω → F ω ≤ G ω) : I.E F ≤ I.E G := by
  unfold Instance.E
  apply Finset.sum_le_sum
  intro ω _
  rcases (prob_nonneg I hp0 ω).lt_or_eq with hp | hp
  · exact mul_le_mul_of_nonneg_left (h ω hp) hp.le
  · rw [← hp]; simp

theorem E_sum {ι : Type} (I : Instance U m) (s : Finset ι) (F : ι → (Fin m → U) → ℝ) :
    I.E (fun ω => ∑ j ∈ s, F j ω) = ∑ j ∈ s, I.E (F j) := by
  unfold Instance.E
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem E_smul (I : Instance U m) (a : ℝ) (F : (Fin m → U) → ℝ) :
    I.E (fun ω => a * F ω) = a * I.E F := by
  unfold Instance.E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ω _; ring

theorem E_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (F : (Fin m → U) → ℝ)
    (h : ∀ ω, 0 ≤ F ω) : 0 ≤ I.E F :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (prob_nonneg I hp0 ω) (h ω)

theorem ind_nonneg (p : Prop) {inst : Decidable p} : (0 : ℝ) ≤ if p then 1 else 0 := by
  split <;> norm_num

theorem P_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (A : (Fin m → U) → Prop) :
    0 ≤ I.P A := by
  unfold Instance.P
  exact E_nonneg I hp0 _ fun ω => ind_nonneg _

theorem scale_unique (x : ℝ) (j j' : ℕ)
    (h1 : (2⁻¹ : ℝ) ^ j / 2 < x) (h2 : x ≤ (2⁻¹ : ℝ) ^ j)
    (h1' : (2⁻¹ : ℝ) ^ j' / 2 < x) (h2' : x ≤ (2⁻¹ : ℝ) ^ j') : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (2⁻¹ : ℝ) ^ j' ≤ (2⁻¹ : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ] at this
    linarith
  · have : (2⁻¹ : ℝ) ^ j ≤ (2⁻¹ : ℝ) ^ (j' + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ] at this
    linarith

theorem sum_biUnion_le' {ι κ : Type} [DecidableEq κ] (G : Finset ι) (T : ι → Finset κ)
    (c : κ → ℕ) : ∑ e ∈ G.biUnion T, c e ≤ ∑ j ∈ G, ∑ e ∈ T j, c e := by
  classical
  induction G using Finset.induction_on with
  | empty => simp
  | insert a G ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := Finset.sum_union_inter (s₁ := T a) (s₂ := G.biUnion T) (f := c)
    omega

theorem geom_two (N : ℕ) : ∑ i ∈ Finset.range N, (2 : ℝ) ^ i = 2 ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

end ASCL43

open ASCL43 in
theorem solution {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (z : ℕ) (π : AdaptivePolicy m U) (i : ℕ) (S : Finset (Fin m)) :
    ∃ T ⊆ Finset.univ \ S, ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ 144 / delta z * 2 ^ i ∧
      I.gExp (I.tau z) S T ≥ 1 / 6 * I.goodSum π i z S := by
  classical
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, -⟩ := hI'
  have hQr : (0 : ℝ) < I.Q := by exact_mod_cast hQ
  have hfQ : ∀ A : Finset U, (I.f A : ℝ) ≤ I.Q := by
    intro A; unfold Instance.Q; exact_mod_cast hmon (Finset.subset_univ A)
  have hfmono : ∀ A B : Finset U, A ⊆ B → (I.f A : ℝ) ≤ I.f B := by
    intro A B h; exact_mod_cast hmon h
  -- the sets of Lemma 4.2, one per good scale
  have hex : ∀ j : ℕ, ∃ T : Finset (Fin m), T ⊆ Finset.univ \ S ∧ (I.Good π i j S →
      ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ 144 / (2⁻¹ : ℝ) ^ j * 2 ^ i ∧
      I.condE (I.InScale j S)
          (fun ω => (I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) ≥
        (2⁻¹ : ℝ) ^ j * I.Q / 6 * (I.rStar π i j S / I.P (I.InScale j S))) := by
    intro j
    by_cases hg : I.Good π i j S
    · obtain ⟨T, hT, h1, h2⟩ := AdaptSubCover.Rounds.lemma_4_2 I hI hQ π i j S hg
      exact ⟨T, hT, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hg⟩
  choose Tj hTsub hTj using hex
  set G := (Finset.range z).filter (fun j => I.Good π i j S) with hG
  set T := G.biUnion Tj with hT
  have hTS : T ⊆ Finset.univ \ S := by
    intro e he
    rw [hT, Finset.mem_biUnion] at he
    obtain ⟨j, _, hj⟩ := he
    exact hTsub j hj
  refine ⟨T, hTS, ?_, ?_⟩
  · -- cost
    have h1 := sum_biUnion_le' G Tj I.c
    have h1r : ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ ∑ j ∈ G, ((∑ e ∈ Tj j, I.c e : ℕ) : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast h1
    refine h1r.trans ?_
    have h2 : ∑ j ∈ G, ((∑ e ∈ Tj j, I.c e : ℕ) : ℝ) ≤ ∑ j ∈ G, 144 * 2 ^ i * (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have := (hTj j (Finset.mem_filter.mp hj).2).1
      rw [inv_pow, div_inv_eq_mul] at this
      linarith
    refine h2.trans ?_
    have h3 : ∑ j ∈ G, 144 * 2 ^ i * (2 : ℝ) ^ j ≤ ∑ j ∈ Finset.range z, 144 * 2 ^ i * (2 : ℝ) ^ j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    refine h3.trans ?_
    rw [← Finset.mul_sum]
    have hgeom : ∑ j ∈ Finset.range z, (2 : ℝ) ^ j ≤ 2 ^ z := by
      rw [geom_two]; linarith
    have hδ : 144 / delta z * 2 ^ i = 144 * 2 ^ i * (2 : ℝ) ^ z := by
      unfold delta; rw [inv_pow, div_inv_eq_mul]; ring
    rw [hδ]
    exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  · -- value
    set ratio : (Fin m → U) → ℝ := fun ω =>
      ((I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) / ((I.Q : ℝ) - I.f (S.image ω))
      with hratio
    have hratio0 : ∀ ω, 0 ≤ ratio ω := by
      intro ω
      apply div_nonneg
      · linarith [hfmono _ _ (Finset.subset_union_left (s₁ := S.image ω) (s₂ := T.image ω))]
      · linarith [hfQ (S.image ω)]
    -- scales below threshold have f(S) < τ
    have hlt : ∀ j < z, ∀ ω, I.InScale j S ω → (I.f (S.image ω) : ℝ) < I.tau z := by
      intro j hj ω hE
      obtain ⟨-, h1, -⟩ := hE
      have hpow : (2⁻¹ : ℝ) ^ z ≤ (2⁻¹ : ℝ) ^ j / 2 := by
        have : (2⁻¹ : ℝ) ^ z ≤ (2⁻¹ : ℝ) ^ (j + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        rw [pow_succ] at this; linarith
      have : (2⁻¹ : ℝ) ^ z < ((I.Q : ℝ) - I.f (S.image ω)) / I.Q := lt_of_le_of_lt hpow h1
      rw [lt_div_iff₀ hQr] at this
      unfold Instance.tau delta
      linarith
    -- Step A: gExp dominates the sum over good scales
    have hA : ∑ j ∈ G, I.E (fun ω => @ite ℝ (I.InScale j S ω) (Classical.propDecidable _)
        (ratio ω) 0) ≤ I.gExp (I.tau z) S T := by
      rw [← E_sum]
      unfold Instance.gExp
      apply E_mono I hp0
      intro ω _
      by_cases hex : ∃ j ∈ G, I.InScale j S ω
      · obtain ⟨j0, hj0, hE0⟩ := hex
        rw [Finset.sum_eq_single_of_mem j0 hj0 (fun j hj hne => by
          rw [if_neg]
          intro hE
          apply hne
          exact scale_unique _ j j0 hE.2.1 hE.2.2 hE0.2.1 hE0.2.2)]
        rw [if_pos hE0]
        have hjz : j0 < z := Finset.mem_range.mp (Finset.mem_filter.mp hj0).1
        rw [if_pos (hlt j0 hjz ω hE0)]
      · push Not at hex
        rw [Finset.sum_eq_zero (fun j hj => if_neg (hex j hj))]
        split
        · exact hratio0 ω
        · exact le_refl _
    -- Step B: each good scale contributes at least r*/6
    have hB : ∀ j ∈ G, 1 / 6 * I.rStar π i j S ≤
        I.E (fun ω => @ite ℝ (I.InScale j S ω) (Classical.propDecidable _) (ratio ω) 0) := by
      intro j hj
      have hg := (Finset.mem_filter.mp hj).2
      obtain ⟨-, hcond⟩ := hTj j hg
      have hθ : (0 : ℝ) < (2⁻¹ : ℝ) ^ j := by positivity
      -- lower bound on the ratio on the scale
      set D : (Fin m → U) → ℝ := fun ω =>
        (I.f (S.image ω ∪ (Tj j).image ω) : ℝ) - I.f (S.image ω) with hD
      have hpt : ∀ ω, @ite ℝ (I.InScale j S ω) (Classical.propDecidable _) (D ω) 0 /
          ((2⁻¹ : ℝ) ^ j * I.Q) ≤
          @ite ℝ (I.InScale j S ω) (Classical.propDecidable _) (ratio ω) 0 := by
        intro ω
        by_cases hE : I.InScale j S ω
        · rw [if_pos hE, if_pos hE]
          obtain ⟨-, h1, h2⟩ := hE
          have hden : 0 < (I.Q : ℝ) - I.f (S.image ω) := by
            have : 0 < ((I.Q : ℝ) - I.f (S.image ω)) / I.Q := lt_of_le_of_lt (by positivity) h1
            rwa [div_pos_iff_of_pos_right hQr] at this
          have hden2 : (I.Q : ℝ) - I.f (S.image ω) ≤ (2⁻¹ : ℝ) ^ j * I.Q := by
            rwa [div_le_iff₀ hQr] at h2
          have hDmono : D ω ≤ (I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω) := by
            simp only [hD]
            have : (Tj j).image ω ⊆ T.image ω := by
              apply Finset.image_subset_image
              intro e he; rw [hT, Finset.mem_biUnion]; exact ⟨j, hj, he⟩
            linarith [hfmono _ _ (Finset.union_subset_union (le_refl (S.image ω)) this)]
          have hD0 : 0 ≤ D ω := by
            simp only [hD]
            linarith [hfmono _ _ (Finset.subset_union_left (s₁ := S.image ω) (s₂ := (Tj j).image ω))]
          simp only [hratio]
          calc D ω / ((2⁻¹ : ℝ) ^ j * I.Q) ≤ D ω / ((I.Q : ℝ) - I.f (S.image ω)) :=
                div_le_div_of_nonneg_left hD0 hden hden2
            _ ≤ _ := div_le_div_of_nonneg_right hDmono hden.le
        · rw [if_neg hE, if_neg hE, zero_div]
      have hEle : I.E (fun ω => @ite ℝ (I.InScale j S ω) (Classical.propDecidable _) (D ω) 0) /
          ((2⁻¹ : ℝ) ^ j * I.Q) ≤
          I.E (fun ω => @ite ℝ (I.InScale j S ω) (Classical.propDecidable _) (ratio ω) 0) := by
        rw [div_eq_mul_inv, mul_comm, ← E_smul]
        apply E_mono I hp0
        intro ω _
        rw [mul_comm, ← div_eq_mul_inv]
        exact hpt ω
      refine le_trans ?_ hEle
      -- relate to the conditional expectation
      have hr0 : 0 ≤ I.rStar π i j S := P_nonneg I hp0 _
      have hrE : I.rStar π i j S ≤ I.P (I.InScale j S) := by
        unfold Instance.rStar Instance.P
        apply E_mono I hp0
        intro ω _
        by_cases h : I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ I.InScale j S ω
        · rw [if_pos h, if_pos h.2.2]
        · rw [if_neg h]; exact ind_nonneg _
      have hED0 : 0 ≤ I.E (fun ω => @ite ℝ (I.InScale j S ω) (Classical.propDecidable _) (D ω) 0) := by
        apply E_nonneg I hp0
        intro ω
        split
        · simp only [hD]
          linarith [hfmono _ _ (Finset.subset_union_left (s₁ := S.image ω) (s₂ := (Tj j).image ω))]
        · exact le_refl _
      rcases (P_nonneg I hp0 (I.InScale j S)).lt_or_eq with hpos | hzero
      · have hc : I.condE (I.InScale j S) D * I.P (I.InScale j S) =
            I.E (fun ω => @ite ℝ (I.InScale j S ω) (Classical.propDecidable _) (D ω) 0) := by
          unfold Instance.condE
          field_simp
        have h1 : (2⁻¹ : ℝ) ^ j * I.Q / 6 * I.rStar π i j S ≤
            I.E (fun ω => @ite ℝ (I.InScale j S ω) (Classical.propDecidable _) (D ω) 0) := by
          rw [← hc]
          have := mul_le_mul_of_nonneg_right hcond hpos.le
          have e : (2⁻¹ : ℝ) ^ j * I.Q / 6 * (I.rStar π i j S / I.P (I.InScale j S)) *
              I.P (I.InScale j S) = (2⁻¹ : ℝ) ^ j * I.Q / 6 * I.rStar π i j S := by
            field_simp
          rw [e] at this
          exact this
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      · rw [← hzero] at hrE
        have : I.rStar π i j S = 0 := le_antisymm hrE hr0
        rw [this, mul_zero]
        exact div_nonneg hED0 (by positivity)
    -- combine
    unfold Instance.goodSum
    rw [← hG, Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum hB) hA
