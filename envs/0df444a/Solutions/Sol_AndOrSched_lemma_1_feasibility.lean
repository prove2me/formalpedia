-- Prove2me | solution 1 for AndOrSched.lemma_1_feasibility
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:23:04.124601+00:00
-- url     : https://prove2.me/submissions/9994a5ba-665e-4314-899c-454cdf53927c

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_nonRedPred
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_key
open scoped Classical NNReal

namespace Aux_AOS_feas

open AndOrSched

theorem sigma_of_injective {N : Type} [Fintype N] (f : N → ℕ) (hf : Function.Injective f) :
    ∃ σ : N ≃ Fin (Fintype.card N), ∀ i j, σ i < σ j ↔ f i < f j := by
  let g : N → ℕ := fun j => (Finset.univ.filter (fun i => f i < f j)).card
  have hg_lt : ∀ j, g j < Fintype.card N := by
    intro j
    have hss : (Finset.univ.filter (fun i => f i < f j)) ⊂ Finset.univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have : j ∈ Finset.univ.filter (fun i => f i < f j) := by rw [h]; exact Finset.mem_univ j
      simp at this
    have := Finset.card_lt_card hss
    simpa using this
  have hg_mono : ∀ i j, f i < f j → g i < g j := by
    intro i j hij
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun h => ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact lt_trans hk hij
    · have : i ∈ Finset.univ.filter (fun k => f k < f j) := by simp [hij]
      rw [← h] at this
      simp at this
  have hinj : Function.Injective (fun j => (⟨g j, hg_lt j⟩ : Fin (Fintype.card N))) := by
    intro i j hij
    simp only [Fin.mk.injEq] at hij
    by_contra hne
    rcases lt_trichotomy (f i) (f j) with h | h | h
    · exact absurd hij (ne_of_lt (hg_mono i j h))
    · exact hne (hf h)
    · exact absurd hij (ne_of_gt (hg_mono j i h))
  have hbij : Function.Bijective (fun j => (⟨g j, hg_lt j⟩ : Fin (Fintype.card N))) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  refine ⟨Equiv.ofBijective _ hbij, fun i j => ?_⟩
  simp only [Equiv.ofBijective_apply, Fin.mk_lt_mk]
  constructor
  · intro h
    rcases lt_trichotomy (f i) (f j) with h' | h' | h'
    · exact h'
    · rw [hf h'] at h; exact absurd h (lt_irrefl _)
    · exact absurd h (not_lt.mpr (hg_mono j i h').le)
  · exact hg_mono i j

theorem lex_lt (a b x y M : ℕ) (hx : x < M) (hab : a < b) : a * M + x < b * M + y := by
  have h1 : (a + 1) * M ≤ b * M := Nat.mul_le_mul_right M hab
  have h2 : (a + 1) * M = a * M + M := by ring
  omega

def kind (I : Instance) : I.N → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

noncomputable def ht (I : Instance) : I.N → ℕ
  | Sum.inl a => (Finset.univ.filter (fun a' => Relation.TransGen I.andA a' a)).card
  | Sum.inr b => (Finset.univ.filter (fun b' => Relation.TransGen I.andB b' b)).card

theorem ht_lt (I : Instance) (j : I.N) : ht I j < Fintype.card I.N + 1 := by
  rw [Fintype.card_sum]
  cases j with
  | inl a =>
    show (Finset.univ.filter (fun a' => Relation.TransGen I.andA a' a)).card < _
    have := Finset.card_filter_le (Finset.univ : Finset I.A) (fun a' => Relation.TransGen I.andA a' a)
    rw [Finset.card_univ] at this
    omega
  | inr b =>
    show (Finset.univ.filter (fun b' => Relation.TransGen I.andB b' b)).card < _
    have := Finset.card_filter_le (Finset.univ : Finset I.B) (fun b' => Relation.TransGen I.andB b' b)
    rw [Finset.card_univ] at this
    omega

theorem ht_A (I : Instance) (hI : Acyclic I) (a a' : I.A) (h : I.andA a a') :
    ht I (Sum.inl a) < ht I (Sum.inl a') := by
  show (Finset.univ.filter (fun c => Relation.TransGen I.andA c a)).card <
    (Finset.univ.filter (fun c => Relation.TransGen I.andA c a')).card
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun he => ?_⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact Relation.TransGen.tail hc h
  · have : a ∈ Finset.univ.filter (fun c => Relation.TransGen I.andA c a') := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single h
    rw [← he] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hI.1 a this

theorem ht_B (I : Instance) (hI : Acyclic I) (b b' : I.B) (h : I.andB b b') :
    ht I (Sum.inr b) < ht I (Sum.inr b') := by
  show (Finset.univ.filter (fun c => Relation.TransGen I.andB c b)).card <
    (Finset.univ.filter (fun c => Relation.TransGen I.andB c b')).card
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun he => ?_⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact Relation.TransGen.tail hc h
  · have : b ∈ Finset.univ.filter (fun c => Relation.TransGen I.andB c b') := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single h
    rw [← he] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hI.2 b this

theorem andRel_irrefl (I : Instance) (hI : Acyclic I) (i : I.N) : ¬ andRel I i i := by
  cases i with
  | inl a => exact fun h => hI.1 a (Relation.TransGen.single h)
  | inr b => exact fun h => hI.2 b (Relation.TransGen.single h)

end Aux_AOS_feas

open AndOrSched Aux_AOS_feas in
theorem solution (I : AndOrSched.Instance) (hI : AndOrSched.Acyclic I)
    (hint : ∀ j, ∃ n : ℕ, I.p j = n)
    (hp : ∀ j, I.p j ≤ 1) (hred : ∀ b, AndOrSched.nonRedPred I b = AndOrSched.orPred I b)
    (x : I.N → ℕ → ℝ) (hx : AndOrSched.LP1Feasible I x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (∃ σ, AndOrSched.Compat I (AndOrSched.key I x β) σ) ∧
    ∀ σ, AndOrSched.Compat I (AndOrSched.key I x β) σ →
      AndOrSched.IsFeasible I (AndOrSched.listC I σ) := by
  set K := key I x β with hK
  -- the score
  set n := Fintype.card I.N with hn
  let e : I.N → ℕ := fun j => (Fintype.equivFin I.N j).val
  have he : ∀ j, e j < n := fun j => (Fintype.equivFin I.N j).isLt
  let prim : I.N → ℕ := fun j => (K j * 2 + kind I j) * (n + 1) + ht I j
  let code : I.N → ℕ := fun j => prim j * n + e j
  have hkind : ∀ j, kind I j ≤ 1 := by intro j; cases j <;> simp [kind]
  have F1 : ∀ i j, K i < K j → prim i < prim j := by
    intro i j h
    show (K i * 2 + kind I i) * (n + 1) + ht I i < (K j * 2 + kind I j) * (n + 1) + ht I j
    have := hkind i
    exact lex_lt _ _ _ _ _ (ht_lt I i) (by omega)
  have F2 : ∀ i j, K i = K j → kind I i < kind I j → prim i < prim j := by
    intro i j h1 h2
    show (K i * 2 + kind I i) * (n + 1) + ht I i < (K j * 2 + kind I j) * (n + 1) + ht I j
    exact lex_lt _ _ _ _ _ (ht_lt I i) (by omega)
  have F3 : ∀ i j, K i = K j → kind I i = kind I j → ht I i < ht I j → prim i < prim j := by
    intro i j h1 h2 h3
    show (K i * 2 + kind I i) * (n + 1) + ht I i < (K j * 2 + kind I j) * (n + 1) + ht I j
    rw [h1, h2]
    omega
  have F4 : ∀ i j, prim i < prim j → code i < code j := by
    intro i j h
    show prim i * n + e i < prim j * n + e j
    exact lex_lt _ _ _ _ _ (he i) h
  have hcode_inj : Function.Injective code := by
    intro i j h
    have h1 : code i % n = e i := by
      show (prim i * n + e i) % n = e i
      exact Nat.mul_add_mod_of_lt (he i)
    have h2 : code j % n = e j := by
      show (prim j * n + e j) % n = e j
      exact Nat.mul_add_mod_of_lt (he j)
    have : e i = e j := by rw [← h1, ← h2, h]
    exact (Fintype.equivFin I.N).injective (Fin.ext this)
  have hcode_lt : ∀ i j, code i < code j → K i ≤ K j := by
    intro i j h
    by_contra hc
    push_neg at hc
    exact absurd (F4 _ _ (F1 _ _ hc)) (not_lt.mpr h.le)
  -- compatibility facts shared by both parts
  have hcompat_lt : ∀ σ : I.N ≃ Fin (Fintype.card I.N), Compat I K σ → ∀ i j, i ≠ j →
      K i ≤ K j → (K i = K j → σ i < σ j) → σ i < σ j := by
    intro σ hσ i j hij hle htie
    have hσ' := hσ
    unfold Compat at hσ'
    rcases lt_trichotomy (σ i) (σ j) with h | h | h
    · exact h
    · exact absurd (σ.injective h) hij
    · have := hσ'.1 j i h
      exact htie (le_antisymm hle this)
  refine ⟨?_, ?_⟩
  · -- existence of a compatible order
    obtain ⟨σ, hσ⟩ := sigma_of_injective code hcode_inj
    refine ⟨σ, ?_⟩
    unfold Compat
    refine ⟨?_, ?_, ?_⟩
    · intro i j h
      exact hcode_lt i j ((hσ i j).mp h)
    · intro b a _ hab
      rw [hσ]
      exact F4 _ _ (F2 _ _ hab (by simp [kind]))
    · intro i j hij hk
      rw [hσ]
      apply F4
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact F3 _ _ hk rfl (ht_A I hI a a' hij)
        | inr b' => exact absurd hij (by simp [andRel])
      | inr b =>
        cases j with
        | inl a' => exact absurd hij (by simp [andRel])
        | inr b' => exact F3 _ _ hk rfl (ht_B I hI b b' hij)
  · -- every compatible order gives a feasible schedule
    intro σ hσ
    have hσ' := hσ
    unfold Compat at hσ'
    set T := horizon I with hT
    have hx' := hx
    unfold LP1Feasible at hx'
    obtain ⟨hcumT, hcap, hor, hand, hnn⟩ := hx'
    have hcum0 : ∀ j, cum x j 0 = 0 := by intro j; simp [cum]
    have hmono : ∀ j t t', t ≤ t' → t' ≤ T → cum x j t ≤ cum x j t' := by
      intro j t t' h1 h2
      unfold cum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro s hs
        rw [Finset.mem_Icc] at hs ⊢
        omega
      · intro s hs _
        rw [Finset.mem_Icc] at hs
        exact hnn j s (Finset.mem_Icc.mpr ⟨hs.1, by omega⟩)
    have hpN : ∀ j, pN I j ≤ 1 := by
      intro j
      unfold pN
      calc ⌊I.p j⌋₊ ≤ ⌊(1 : ℚ≥0)⌋₊ := Nat.floor_le_floor (hp j)
        _ = 1 := Nat.floor_one
    -- alpha points
    have ap_le : ∀ (θ : ℝ) j t, θ ≤ cum x j t → alphaPoint x j θ ≤ t := by
      intro θ j t h
      exact Nat.sInf_le h
    have ap_mem : ∀ (θ : ℝ), θ ≤ 1 → ∀ j, θ ≤ cum x j (alphaPoint x j θ) := by
      intro θ hθ j
      have hne : ({t : ℕ | θ ≤ cum x j t} : Set ℕ).Nonempty := ⟨T, by
        show θ ≤ cum x j T
        rw [hcumT j]; exact hθ⟩
      exact Nat.sInf_mem hne
    have ap_T : ∀ (θ : ℝ), θ ≤ 1 → ∀ j, alphaPoint x j θ ≤ T := by
      intro θ hθ j
      apply ap_le
      rw [hcumT j]; exact hθ
    have ap_pos : ∀ (θ : ℝ), 0 < θ → θ ≤ 1 → ∀ j, 1 ≤ alphaPoint x j θ := by
      intro θ hθ0 hθ1 j
      by_contra h
      push_neg at h
      have h0 : alphaPoint x j θ = 0 := by omega
      have := ap_mem θ hθ1 j
      rw [h0, hcum0] at this
      linarith
    -- the threshold for A-jobs
    have hδ1 : (1 : ℝ) ≤ (delta I : ℝ) := by
      have : 1 ≤ delta I := le_max_left _ _
      exact_mod_cast this
    have hδpos : (0 : ℝ) < (delta I : ℝ) := by linarith
    have hθA0 : 0 < β / (delta I : ℝ) := div_pos hβ0 hδpos
    have hθA1 : β / (delta I : ℝ) ≤ 1 := by
      rw [div_le_one hδpos]; linarith
    have hKA : ∀ a, K (Sum.inl a) = alphaPoint x (Sum.inl a) (β / (delta I : ℝ)) := fun a => rfl
    have hKB : ∀ b, K (Sum.inr b) = alphaPoint x (Sum.inr b) β := fun b => rfl
    -- a reusable step: if cum of j reaches θ at k, find t ≤ k usable in constraints
    have step : ∀ (θ : ℝ) (j : I.N), 0 < θ → θ ≤ 1 →
        (T ≤ 1 ∨ ∃ t, 1 ≤ t ∧ t ≤ T - pN I j ∧ t ≤ alphaPoint x j θ ∧
          θ ≤ cum x j (t + pN I j)) := by
      intro θ j hθ0 hθ1
      have hk1 := ap_pos θ hθ0 hθ1 j
      have hkT := ap_T θ hθ1 j
      have hkm := ap_mem θ hθ1 j
      have hp1 := hpN j
      by_cases hc : 1 ≤ alphaPoint x j θ - pN I j
      · right
        refine ⟨alphaPoint x j θ - pN I j, hc, by omega, by omega, ?_⟩
        rw [show alphaPoint x j θ - pN I j + pN I j = alphaPoint x j θ by omega]
        exact hkm
      · by_cases hT2 : 2 ≤ T
        · right
          have hk : alphaPoint x j θ = 1 := by omega
          have hpj : pN I j = 1 := by omega
          refine ⟨1, le_rfl, by omega, by omega, ?_⟩
          rw [hpj]
          show θ ≤ cum x j 2
          have := hmono j (alphaPoint x j θ) 2 (by omega) hT2
          linarith
        · left; omega
    -- AND precedence gives key order
    have hand_key : ∀ i j, andRel I i j → K i ≤ K j := by
      intro i j hij
      cases i with
      | inl a =>
        cases j with
        | inr b' => exact absurd hij (by simp [andRel])
        | inl a' =>
          rw [hKA, hKA]
          rcases step _ (Sum.inl a') hθA0 hθA1 with hT1 | ⟨t, ht1, ht2, ht3, ht4⟩
          · have := ap_T _ hθA1 (Sum.inl a)
            have := ap_pos _ hθA0 hθA1 (Sum.inl a')
            omega
          · have h1 := hand (Sum.inl a) (Sum.inl a') hij t (Finset.mem_Icc.mpr ⟨ht1, ht2⟩)
            have h2 : β / (delta I : ℝ) ≤ cum x (Sum.inl a) t := by linarith
            exact le_trans (ap_le _ _ _ h2) ht3
      | inr b =>
        cases j with
        | inl a' => exact absurd hij (by simp [andRel])
        | inr b' =>
          rw [hKB, hKB]
          rcases step _ (Sum.inr b') hβ0 hβ1 with hT1 | ⟨t, ht1, ht2, ht3, ht4⟩
          · have := ap_T _ hβ1 (Sum.inr b)
            have := ap_pos _ hβ0 hβ1 (Sum.inr b')
            omega
          · have h1 := hand (Sum.inr b) (Sum.inr b') hij t (Finset.mem_Icc.mpr ⟨ht1, ht2⟩)
            have h2 : β ≤ cum x (Sum.inr b) t := by linarith
            exact le_trans (ap_le _ _ _ h2) ht3
    -- OR precedence gives a predecessor with smaller key
    have hor_key : ∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, K (Sum.inl a) ≤ K (Sum.inr b) := by
      intro b hne
      rw [hKB]
      have hcardP : ((orPred I b).card : ℝ) ≤ (delta I : ℝ) := by
        have h1 : (orPred I b).card ≤ delta I := by
          rw [← hred b]
          exact le_trans (Finset.le_sup (f := fun b => (nonRedPred I b).card) (Finset.mem_univ b))
            (le_max_right _ _)
        exact_mod_cast h1
      have hcpos : (0 : ℝ) < (orPred I b).card := by
        have := Finset.card_pos.mpr hne
        exact_mod_cast this
      rcases step _ (Sum.inr b) hβ0 hβ1 with hT1 | ⟨t, ht1, ht2, ht3, ht4⟩
      · obtain ⟨a, ha⟩ := hne
        refine ⟨a, ha, ?_⟩
        rw [hKA]
        have := ap_T _ hθA1 (Sum.inl a)
        have := ap_pos _ hβ0 hβ1 (Sum.inr b)
        omega
      · have h1 := hor b hne t (Finset.mem_Icc.mpr ⟨ht1, ht2⟩)
        have h2 : β ≤ ∑ a ∈ orPred I b, cum x (Sum.inl a) t := by linarith
        by_contra hno
        push_neg at hno
        have hlt : ∀ a ∈ orPred I b, cum x (Sum.inl a) t < β / (orPred I b).card := by
          intro a ha
          by_contra hge
          push_neg at hge
          have h3 : β / (delta I : ℝ) ≤ β / (orPred I b).card :=
            div_le_div_of_nonneg_left hβ0.le hcpos hcardP
          have := ap_le _ _ _ (le_trans h3 hge)
          have := hno a ha
          rw [hKA] at this
          omega
        have h4 : ∑ a ∈ orPred I b, cum x (Sum.inl a) t <
            ∑ a ∈ orPred I b, β / (orPred I b).card := Finset.sum_lt_sum_of_nonempty hne hlt
        have e : ((orPred I b).card : ℝ) * (β / (orPred I b).card) = β := by field_simp
        rw [Finset.sum_const, nsmul_eq_mul, e] at h4
        linarith
    -- the list schedule
    have hC : ∀ i j, σ i < σ j → listC I σ i + (I.p j : ℝ) ≤ listC I σ j := by
      intro i j hij
      unfold listC
      have hsub : insert j (Finset.univ.filter (fun k => σ k ≤ σ i)) ⊆
          Finset.univ.filter (fun k => σ k ≤ σ j) := by
        intro k hk
        rw [Finset.mem_insert] at hk
        rw [Finset.mem_filter]
        rcases hk with rfl | hk
        · exact ⟨Finset.mem_univ _, le_rfl⟩
        · rw [Finset.mem_filter] at hk
          exact ⟨Finset.mem_univ _, le_trans hk.2 hij.le⟩
      have hnot : j ∉ Finset.univ.filter (fun k => σ k ≤ σ i) := by
        rw [Finset.mem_filter]; intro h; exact absurd h.2 (not_le.mpr hij)
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => ((I.p k : ℚ≥0) : ℝ)) hsub
        (fun k _ _ => by positivity)
      rw [Finset.sum_insert hnot] at this
      linarith
    unfold IsFeasible
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      unfold listC
      exact Finset.single_le_sum (f := fun i => ((I.p i : ℚ≥0) : ℝ)) (fun i _ => by positivity)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_rfl⟩)
    · intro i j hij
      rcases lt_or_gt_of_ne (fun h => hij (σ.injective h)) with h | h
      · left; have := hC i j h; linarith
      · right; have := hC j i h; linarith
    · intro i j hij
      have hne : i ≠ j := by
        intro h; subst h; exact andRel_irrefl I hI i hij
      have := hcompat_lt σ hσ i j hne (hand_key i j hij) (hσ'.2.2 i j hij)
      exact hC i j this
    · intro b hne
      obtain ⟨a, ha, hle⟩ := hor_key b hne
      refine ⟨a, ha, hC _ _ ?_⟩
      exact hcompat_lt σ hσ _ _ (by simp) hle (hσ'.2.1 b a ha)
