-- Prove2me | solution 1 for AssortOpt.HMF.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:24:35.833622+00:00
-- url     : https://prove2.me/submissions/2d598084-9bbf-4387-86c0-4315c62ba001

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

open AssortOpt.HMF

namespace HMFCore

variable {n : ℕ}

lemma take_succ_eq (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    ℓ.take (k + 1) = ℓ.take k ++ [ℓ[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  rfl

lemma mem_prefixes {D : ListDist n} {ρ : List (Fin n)} :
    ρ ∈ prefixes D ↔ ρ ≠ [] ∧ ∃ ℓ ∈ D.supp, ρ <+: ℓ := by
  unfold prefixes
  simp only [Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
  tauto

lemma prefixes_filter_eq (D : ListDist n) (ℓ : List (Fin n)) (hℓ : ℓ ∈ D.supp) :
    (prefixes D).filter (fun ρ => ρ <+: ℓ) =
      (Finset.range ℓ.length).image (fun k => ℓ.take (k + 1)) := by
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, mem_prefixes]
  constructor
  · rintro ⟨⟨hne, -⟩, hpre⟩
    have hlen : ρ.length ≤ ℓ.length := hpre.length_le
    have hpos : 0 < ρ.length := List.length_pos_iff.mpr hne
    refine ⟨ρ.length - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hpos]
    exact (List.prefix_iff_eq_take.mp hpre).symm
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨?_, ℓ, hℓ, List.take_prefix _ _⟩, List.take_prefix _ _⟩
    rw [take_succ_eq ℓ k hk]
    simp
    intro h; subst h; simp at hk

/-- Exchange of the sum over realizable prefixes with the sum over lists and positions. -/
lemma prefix_exchange (D : ListDist n) (G : List (Fin n) → ℝ) :
    ∑ ρ ∈ prefixes D, prefProb D ρ * G ρ =
      ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range ℓ.length, G (ℓ.take (k + 1)) := by
  classical
  unfold prefProb
  have h1 : ∀ ρ, (∑ ℓ ∈ D.supp with ρ <+: ℓ, D.p ℓ) * G ρ =
      ∑ ℓ ∈ D.supp, if ρ <+: ℓ then D.p ℓ * G ρ else 0 := by
    intro ρ
    rw [Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ℓ _
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [← Finset.sum_filter, ← Finset.mul_sum, prefixes_filter_eq D ℓ hℓ]
  congr 1
  rw [Finset.sum_image]
  intro a ha b hb hab
  have := congrArg List.length hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp [List.length_take] at this
  omega

/-- The stopping indicator at position `i` of `ℓ` (0 if out of range). -/
noncomputable def sv (φ : Policy n) (ℓ : List (Fin n)) (i : ℕ) : ℝ :=
  (ℓ[i]?.map (fun a => ind (φ a (ℓ.take i).toFinset))).getD 0

lemma sv_eq (φ : Policy n) (ℓ : List (Fin n)) (i : ℕ) (hi : i < ℓ.length) :
    sv φ ℓ i = ind (φ ℓ[i] (ℓ.take i).toFinset) := by
  unfold sv
  rw [List.getElem?_eq_getElem hi]
  rfl

lemma endPrice_take (r : Fin n → ℝ) (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    endPrice r (ℓ.take (k + 1)) = r ℓ[k] := by
  unfold endPrice
  rw [take_succ_eq ℓ k hk, List.getLast?_concat]
  rfl

lemma getLast?_take (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    (ℓ.take (k + 1)).getLast? = some ℓ[k] := by
  rw [take_succ_eq ℓ k hk, List.getLast?_concat]

lemma dropLast_take (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    (ℓ.take (k + 1)).dropLast = ℓ.take k := by
  rw [take_succ_eq ℓ k hk, List.dropLast_concat]

lemma stopInd_take (φ : Policy n) (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    stopInd φ (ℓ.take (k + 1)) = sv φ ℓ k * ∏ i ∈ Finset.range k, (1 - sv φ ℓ i) := by
  unfold stopInd
  rw [getLast?_take ℓ k hk]
  simp only
  rw [dropLast_take ℓ k hk, sv_eq φ ℓ k hk]
  congr 1
  have hlen : (ℓ.take k).length = k := by simp [List.length_take]; omega
  have e1 : ∀ k' : Fin (ℓ.take k).length,
      (1 - ind (φ ((ℓ.take k).get k') ((ℓ.take (k + 1)).take k').toFinset)) =
        (fun i => 1 - sv φ ℓ i) k'.1 := by
    intro k'
    have hk' : k'.1 < k := by have := k'.2; omega
    simp only
    rw [sv_eq φ ℓ k' (by omega), List.take_take, min_eq_left (by omega)]
    simp [List.getElem_take]
  rw [Finset.prod_congr rfl (fun k' _ => e1 k'), Finset.prod_range (fun i => 1 - sv φ ℓ i), hlen]

end HMFCore

namespace HMFCore

variable {n : ℕ}

lemma toFinset_take_mono (ℓ : List (Fin n)) {i j : ℕ} (hij : i ≤ j) :
    (ℓ.take i).toFinset ⊆ (ℓ.take j).toFinset := by
  intro a ha
  rw [List.mem_toFinset] at ha ⊢
  exact (List.take_prefix_take_left hij).subset ha

lemma insert_take (ℓ : List (Fin n)) (i : ℕ) (hi : i < ℓ.length) :
    insert ℓ[i] (ℓ.take i).toFinset = (ℓ.take (i + 1)).toFinset := by
  rw [take_succ_eq ℓ i hi, List.toFinset_append]
  ext a
  simp [or_comm]

lemma revPolicy_eq_lists (D : ListDist n) (r : Fin n → ℝ) (φ : Policy n) :
    revPolicy D r φ = ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k : Fin ℓ.length,
      r ℓ[k.1] * (sv φ ℓ k * ∏ i ∈ Finset.range k, (1 - sv φ ℓ i)) := by
  unfold revPolicy
  have h1 : ∀ ρ ∈ prefixes D, endPrice r ρ * prefProb D ρ * stopInd φ ρ =
      prefProb D ρ * (endPrice r ρ * stopInd φ ρ) := fun ρ _ => by ring
  rw [Finset.sum_congr rfl h1, prefix_exchange]
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 1
  rw [Finset.sum_range (fun k => endPrice r (ℓ.take (k + 1)) * stopInd φ (ℓ.take (k + 1)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [endPrice_take r ℓ k k.2, stopInd_take φ ℓ k k.2]

end HMFCore


open AssortOpt.HMF

namespace HMFCore

variable {n : ℕ}

lemma chooses_iff (S : Finset (Fin n)) (ℓ : List (Fin n)) (j : Fin n) :
    Chooses S ℓ j ↔ j ∈ S ∧ ∃ (i : ℕ) (h : i < ℓ.length), ℓ[i] = j ∧
      ∀ i' (h' : i' < i), ℓ[i']'(by omega) ∉ S := by
  unfold Chooses
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hj, i, h, he, hlt⟩
    refine ⟨by simpa using hj, i, h, he, fun i' h' => ?_⟩
    simpa using hlt i' h'
  · rintro ⟨hj, i, h, he, hlt⟩
    refine ⟨by simpa using hj, i, h, he, fun i' h' => ?_⟩
    simpa using hlt i' h'

lemma chooses_mem {S : Finset (Fin n)} {ℓ : List (Fin n)} {j : Fin n} (h : Chooses S ℓ j) :
    j ∈ S ∧ j ∈ ℓ := by
  refine ⟨?_, List.mem_of_find?_eq_some h⟩
  have := List.find?_some h
  simpa using this

lemma chooses_unique {S : Finset (Fin n)} {ℓ : List (Fin n)} {j j' : Fin n}
    (h : Chooses S ℓ j) (h' : Chooses S ℓ j') : j = j' := by
  unfold Chooses at h h'
  rw [h] at h'
  exact Option.some.inj h'

/-- index of the first item of `S` on `ℓ` (0-based; `ℓ.length` if none). -/
def kap (S : Finset (Fin n)) (ℓ : List (Fin n)) : ℕ := ℓ.findIdx (fun i => decide (i ∈ S))

lemma kap_le (S : Finset (Fin n)) (ℓ : List (Fin n)) : kap S ℓ ≤ ℓ.length :=
  List.findIdx_le_length

lemma lt_kap_iff (S : Finset (Fin n)) (ℓ : List (Fin n)) (k : ℕ) :
    k < kap S ℓ ↔ ∃ h : k < ℓ.length, ∀ j (hj : j ≤ k), ℓ[j] ∉ S := by
  unfold kap
  rw [List.lt_findIdx_iff]
  simp

lemma disj_take_iff (S : Finset (Fin n)) (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    Disjoint (ℓ.take (k + 1)).toFinset S ↔ k < kap S ℓ := by
  rw [lt_kap_iff, Finset.disjoint_left]
  constructor
  · intro h
    refine ⟨hk, fun j hj => h ?_⟩
    rw [List.mem_toFinset, List.mem_take_iff_getElem]
    exact ⟨j, by simp; omega, rfl⟩
  · rintro ⟨_, h⟩ a ha
    rw [List.mem_toFinset, List.mem_take_iff_getElem] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hj' : j ≤ k := by simp at hj; omega
    simpa using h j hj'

lemma kap_mem (S : Finset (Fin n)) (ℓ : List (Fin n)) (h : kap S ℓ < ℓ.length) :
    ℓ[kap S ℓ] ∈ S := by
  have := List.findIdx_getElem (p := fun i => decide (i ∈ S)) (xs := ℓ) (w := h)
  unfold kap
  simpa using this

lemma chooses_kap (S : Finset (Fin n)) (ℓ : List (Fin n)) (h : kap S ℓ < ℓ.length) :
    Chooses S ℓ ℓ[kap S ℓ] := by
  rw [chooses_iff]
  refine ⟨kap_mem S ℓ h, kap S ℓ, h, rfl, fun i' h' => ?_⟩
  have := (lt_kap_iff S ℓ i').mp h'
  obtain ⟨_, hh⟩ := this
  exact hh i' le_rfl

lemma not_chooses_of_kap (S : Finset (Fin n)) (ℓ : List (Fin n)) (h : kap S ℓ = ℓ.length)
    (j : Fin n) : ¬ Chooses S ℓ j := by
  intro hc
  obtain ⟨hjS, hjℓ⟩ := chooses_mem hc
  have := (List.findIdx_eq_length (p := fun i => decide (i ∈ S)) (xs := ℓ)).mp h j hjℓ
  simp [hjS] at this

/-- exchange of sums, with a summand that may also depend on the list -/
lemma prefix_exchange2 (D : ListDist n) (G : List (Fin n) → List (Fin n) → ℝ) :
    ∑ ρ ∈ prefixes D, ∑ ℓ ∈ D.supp with ρ <+: ℓ, D.p ℓ * G ρ ℓ =
      ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range ℓ.length, G (ℓ.take (k + 1)) ℓ := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [← Finset.sum_filter, ← Finset.mul_sum, prefixes_filter_eq D ℓ hℓ]
  congr 1
  rw [Finset.sum_image]
  intro a ha b hb hab
  have := congrArg List.length hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp [List.length_take] at this
  omega

lemma one_sub_prod (s : ℕ → ℝ) (K : ℕ) :
    ∏ i ∈ Finset.range K, (1 - s i) = 1 - ∑ k ∈ Finset.range K, s k * ∏ i ∈ Finset.range k, (1 - s i) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
    ring

lemma prefProb_pos (D : ListDist n) (ρ : List (Fin n)) (hρ : ρ ∈ prefixes D) :
    0 < prefProb D ρ := by
  obtain ⟨-, ℓ, hℓ, hpre⟩ := mem_prefixes.mp hρ
  unfold prefProb
  apply Finset.sum_pos'
  · intro i hi
    exact le_of_lt (D.pos i (Finset.mem_filter.mp hi).1)
  · exact ⟨ℓ, Finset.mem_filter.mpr ⟨hℓ, hpre⟩, D.pos ℓ hℓ⟩

/-- revenue of the assortment on list `ℓ` -/
noncomputable def rch (r : Fin n → ℝ) (S : Finset (Fin n)) (ℓ : List (Fin n)) : ℝ :=
  ∑ j' ∈ S, r j' * (if Chooses S ℓ j' then 1 else 0)

lemma revAssort_eq_lists (D : ListDist n) (r : Fin n → ℝ) (S : Finset (Fin n)) :
    revAssort D r S = ∑ ℓ ∈ D.supp, D.p ℓ * rch r S ℓ := by
  unfold revAssort choiceProb rch
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ℓ _
  split_ifs <;> ring

lemma rch_kap (r : Fin n → ℝ) (S : Finset (Fin n)) (ℓ : List (Fin n)) (h : kap S ℓ < ℓ.length) :
    rch r S ℓ = r ℓ[kap S ℓ] := by
  unfold rch
  rw [Finset.sum_eq_single_of_mem _ (kap_mem S ℓ h)]
  · rw [if_pos (chooses_kap S ℓ h)]; ring
  · intro b _ hb
    rw [if_neg, mul_zero]
    intro hc
    exact hb (chooses_unique hc (chooses_kap S ℓ h))

lemma rch_none (r : Fin n → ℝ) (S : Finset (Fin n)) (ℓ : List (Fin n)) (h : kap S ℓ = ℓ.length) :
    rch r S ℓ = 0 := by
  unfold rch
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (not_chooses_of_kap S ℓ h j), mul_zero]

/-- price at position `k` -/
noncomputable def pr (r : Fin n → ℝ) (ℓ : List (Fin n)) (k : ℕ) : ℝ := (ℓ[k]?.map r).getD 0

lemma pr_eq (r : Fin n → ℝ) (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    pr r ℓ k = r ℓ[k] := by
  unfold pr; rw [List.getElem?_eq_getElem hk]; rfl

/-- `W φ ℓ k`: the policy stops exactly at position `k` of `ℓ`. -/
noncomputable def W (φ : Policy n) (ℓ : List (Fin n)) (k : ℕ) : ℝ :=
  sv φ ℓ k * ∏ i ∈ Finset.range k, (1 - sv φ ℓ i)

lemma revPolicy_eq_lists' (D : ListDist n) (r : Fin n → ℝ) (φ : Policy n) :
    revPolicy D r φ = ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range ℓ.length, pr r ℓ k * W φ ℓ k := by
  rw [revPolicy_eq_lists]
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 1
  rw [Finset.sum_range (fun k => pr r ℓ k * W φ ℓ k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [pr_eq r ℓ k k.2]
  rfl

lemma sv_allones (φ : Policy n) (S : Finset (Fin n))
    (hS : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → φ j H = true) (ℓ : List (Fin n))
    (hnd : ℓ.Nodup) (h : kap S ℓ < ℓ.length) : sv φ ℓ (kap S ℓ) = 1 := by
  rw [sv_eq φ ℓ _ h, hS _ (kap_mem S ℓ h)]
  · rfl
  · rw [List.mem_toFinset, List.mem_take_iff_getElem]
    rintro ⟨i, hi, hie⟩
    have hil : i < ℓ.length := by simp at hi; omega
    have := (List.Nodup.getElem_inj_iff hnd).mp hie
    simp at hi; omega

lemma W_zero_after (φ : Policy n) (ℓ : List (Fin n)) (K k : ℕ) (hK : sv φ ℓ K = 1) (hk : K < k) :
    W φ ℓ k = 0 := by
  unfold W
  rw [Finset.prod_eq_zero (Finset.mem_range.mpr hk) (by rw [hK]; ring), mul_zero]

/-- the per-list form of Lemma 1 -/
lemma per_list (r : Fin n → ℝ) (φ : Policy n) (S : Finset (Fin n))
    (hS : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → φ j H = true) (ℓ : List (Fin n))
    (hnd : ℓ.Nodup) :
    ∑ k ∈ Finset.range ℓ.length, pr r ℓ k * W φ ℓ k - rch r S ℓ =
      ∑ k ∈ Finset.range (kap S ℓ), (pr r ℓ k - rch r S ℓ) * W φ ℓ k := by
  rcases lt_or_eq_of_le (kap_le S ℓ) with h | h
  · have h1 := sv_allones φ S hS ℓ hnd h
    have hsplit : ∑ k ∈ Finset.range ℓ.length, pr r ℓ k * W φ ℓ k =
        ∑ k ∈ Finset.range (kap S ℓ + 1), pr r ℓ k * W φ ℓ k := by
      symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      intro k hk hk'
      simp only [Finset.mem_range] at hk hk'
      rw [W_zero_after φ ℓ (kap S ℓ) k h1 (by omega), mul_zero]
    rw [hsplit, Finset.sum_range_succ, rch_kap r S ℓ h]
    have hW : W φ ℓ (kap S ℓ) = 1 - ∑ k ∈ Finset.range (kap S ℓ), W φ ℓ k := by
      unfold W
      rw [h1, one_mul, one_sub_prod]
    rw [hW, pr_eq r ℓ _ h]
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  · rw [rch_none r S ℓ h, h]
    simp

lemma lemma1 (D : ListDist n) (r : Fin n → ℝ)
    (φ : Policy n) (S : Finset (Fin n))
    (hS : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → φ j H = true) :
    revPolicy D r φ - revAssort D r S =
      ∑ ρ ∈ (prefixes D).filter (fun ρ => Disjoint ρ.toFinset S),
        adjPrice D r S ρ * prefProb D ρ * stopInd φ ρ ∧
    revPolicy D r φ - revAssort D r S =
      ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (kap S ℓ),
        adjPrice D r S (ℓ.take (k + 1)) * stopInd φ (ℓ.take (k + 1)) := by
  classical
  -- list form of the left side
  have hL : revPolicy D r φ - revAssort D r S =
      ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (kap S ℓ), (pr r ℓ k - rch r S ℓ) * W φ ℓ k := by
    rw [revPolicy_eq_lists', revAssort_eq_lists, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [← mul_sub, per_list r φ S hS ℓ (D.nodup ℓ hℓ)]
  -- the prefix sum, rewritten with conditional probabilities cleared
  have hR : ∑ ρ ∈ (prefixes D).filter (fun ρ => Disjoint ρ.toFinset S),
        adjPrice D r S ρ * prefProb D ρ * stopInd φ ρ =
      ∑ ρ ∈ prefixes D, ∑ ℓ ∈ D.supp with ρ <+: ℓ, D.p ℓ *
        (if Disjoint ρ.toFinset S then (endPrice r ρ - rch r S ℓ) * stopInd φ ρ else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hpos := prefProb_pos D ρ hρ
    split_ifs with hd
    · have e1 : adjPrice D r S ρ * prefProb D ρ =
          ∑ ℓ ∈ D.supp with ρ <+: ℓ, D.p ℓ * (endPrice r ρ - rch r S ℓ) := by
        unfold adjPrice condChoiceProb rch
        rw [sub_mul, Finset.sum_mul]
        have e2 : ∀ j' ∈ S, r j' * ((∑ ℓ ∈ D.supp with ρ <+: ℓ ∧ Chooses S ℓ j', D.p ℓ) /
            prefProb D ρ) * prefProb D ρ =
            ∑ ℓ ∈ D.supp with ρ <+: ℓ, D.p ℓ * (r j' * if Chooses S ℓ j' then 1 else 0) := by
          intro j' _
          rw [mul_assoc, div_mul_cancel₀ _ hpos.ne', ← Finset.filter_filter, Finset.sum_filter,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ℓ _
          split_ifs <;> ring
        rw [Finset.sum_congr rfl e2, Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        unfold prefProb
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ℓ _
        ring
      rw [e1, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ℓ _
      ring
    · simp
  have hR2 : ∑ ρ ∈ prefixes D, ∑ ℓ ∈ D.supp with ρ <+: ℓ, D.p ℓ *
        (if Disjoint ρ.toFinset S then (endPrice r ρ - rch r S ℓ) * stopInd φ ρ else 0) =
      ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (kap S ℓ), (pr r ℓ k - rch r S ℓ) * W φ ℓ k := by
    rw [prefix_exchange2 D (fun ρ ℓ =>
      if Disjoint ρ.toFinset S then (endPrice r ρ - rch r S ℓ) * stopInd φ ρ else 0)]
    apply Finset.sum_congr rfl
    intro ℓ _
    congr 1
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (kap_le S ℓ))]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hkl : k < ℓ.length := lt_of_lt_of_le hk (kap_le S ℓ)
      rw [if_pos ((disj_take_iff S ℓ k hkl).mpr hk), endPrice_take r ℓ k hkl,
        stopInd_take φ ℓ k hkl, pr_eq r ℓ k hkl]
      rfl
    · intro k hk hk'
      rw [Finset.mem_range] at hk hk'
      rw [if_neg]
      rw [disj_take_iff S ℓ k hk]
      exact hk'
  have hR3 : ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (kap S ℓ),
        adjPrice D r S (ℓ.take (k + 1)) * stopInd φ (ℓ.take (k + 1)) =
      ∑ ρ ∈ (prefixes D).filter (fun ρ => Disjoint ρ.toFinset S),
        adjPrice D r S ρ * prefProb D ρ * stopInd φ ρ := by
    rw [Finset.sum_filter]
    have := prefix_exchange D (fun ρ => if Disjoint ρ.toFinset S then
      adjPrice D r S ρ * stopInd φ ρ else 0)
    rw [show (∑ ρ ∈ prefixes D, if Disjoint ρ.toFinset S then
        adjPrice D r S ρ * prefProb D ρ * stopInd φ ρ else 0) =
        ∑ ρ ∈ prefixes D, prefProb D ρ * (if Disjoint ρ.toFinset S then
        adjPrice D r S ρ * stopInd φ ρ else 0) from
        Finset.sum_congr rfl (fun ρ _ => by split_ifs <;> ring), this]
    apply Finset.sum_congr rfl
    intro ℓ _
    congr 1
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (kap_le S ℓ))]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hkl : k < ℓ.length := lt_of_lt_of_le hk (kap_le S ℓ)
      rw [if_pos ((disj_take_iff S ℓ k hkl).mpr hk)]
    · intro k hk hk'
      rw [Finset.mem_range] at hk hk'
      rw [if_neg]
      rw [disj_take_iff S ℓ k hk]
      exact hk'
  refine ⟨by rw [hR, hR2, hL], by rw [hR3, hR, hR2, hL]⟩

end HMFCore


open AssortOpt.HMF

theorem solution {n : ℕ} (D : ListDist n) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (φ : Policy n) (hφ : IsMonotonePolicy φ) (S : Finset (Fin n))
    (hS : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → φ j H = true) :
    revPolicy D r φ - revAssort D r S =
      ∑ ρ ∈ (prefixes D).filter (fun ρ => Disjoint ρ.toFinset S),
        adjPrice D r S ρ * prefProb D ρ * stopInd φ ρ :=
  (HMFCore.lemma1 D r φ S hS).1
