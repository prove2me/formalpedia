-- Prove2me | solution 1 for AssortOpt.HMF.opt_policy_assortment
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:31:34.70965+00:00
-- url     : https://prove2.me/submissions/c81ad565-4d6a-4883-9e01-9498ef8cd6bc

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

namespace HMFCore

variable {n : ℕ}

lemma ind_cases (b : Bool) : ind b = 0 ∨ ind b = 1 := by cases b <;> simp [ind]

lemma sv_cases (φ : Policy n) (ℓ : List (Fin n)) (i : ℕ) : sv φ ℓ i = 0 ∨ sv φ ℓ i = 1 := by
  unfold sv
  cases ℓ[i]? with
  | none => simp
  | some a => simpa using ind_cases (φ a (ℓ.take i).toFinset)

lemma W_eq_stopInd (φ : Policy n) (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    stopInd φ (ℓ.take (k + 1)) = W φ ℓ k := stopInd_take φ ℓ k hk

lemma W_congr (φ ψ : Policy n) (ℓ : List (Fin n)) (k : ℕ)
    (h : ∀ i ≤ k, sv ψ ℓ i = sv φ ℓ i) : W ψ ℓ k = W φ ℓ k := by
  unfold W
  rw [h k le_rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [h i hi.le]

lemma prod_cases (s : ℕ → ℝ) (hs : ∀ i, s i = 0 ∨ s i = 1) (K : ℕ) :
    ∏ i ∈ Finset.range K, (1 - s i) = 0 ∨ ∏ i ∈ Finset.range K, (1 - s i) = 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_range_succ]
    rcases ih with h | h <;> rcases hs K with h' | h' <;> simp [h, h']

lemma prod_nonneg01 (s : ℕ → ℝ) (hs : ∀ i, s i = 0 ∨ s i = 1) (K : ℕ) :
    0 ≤ ∏ i ∈ Finset.range K, (1 - s i) := by
  rcases prod_cases s hs K with h | h <;> rw [h] <;> norm_num

lemma Wf_nonneg (s : ℕ → ℝ) (hs : ∀ i, s i = 0 ∨ s i = 1) (k : ℕ) :
    0 ≤ s k * ∏ i ∈ Finset.range k, (1 - s i) := by
  apply mul_nonneg
  · rcases hs k with h | h <;> rw [h] <;> norm_num
  · exact prod_nonneg01 s hs k

lemma split3 (F : ℕ → ℝ) (m L : ℕ) :
    ∑ k ∈ Finset.range (m + 1 + L), F k =
      ∑ k ∈ Finset.range m, F k + F m + ∑ t ∈ Finset.range L, F (m + 1 + t) := by
  rw [Finset.sum_range_add F (m + 1) L, Finset.sum_range_succ F m]

/-- switching one stopping decision from 0 to 1 at a position whose value dominates all values
at which the original policy stops does not decrease the expected value. -/
lemma first_stop (s s' a : ℕ → ℝ) (K m : ℕ) (c : ℝ)
    (hs : ∀ i, s i = 0 ∨ s i = 1)
    (hm : m < K) (hsm : s m = 0) (hs'm : s' m = 1) (heq : ∀ i < K, i ≠ m → s' i = s i)
    (hc : 0 ≤ c) (ham : c ≤ a m) (hak : ∀ k < K, s k = 1 → a k ≤ c) :
    ∑ k ∈ Finset.range K, a k * (s k * ∏ i ∈ Finset.range k, (1 - s i)) ≤
      ∑ k ∈ Finset.range K, a k * (s' k * ∏ i ∈ Finset.range k, (1 - s' i)) := by
  obtain ⟨L, rfl⟩ : ∃ L, K = (m + 1) + L := ⟨K - (m + 1), by omega⟩
  have hpre : ∀ k ≤ m, ∏ i ∈ Finset.range k, (1 - s' i) = ∏ i ∈ Finset.range k, (1 - s i) := by
    intro k hk
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [heq i (by omega) (by omega)]
  rw [split3 (fun k => a k * (s k * ∏ i ∈ Finset.range k, (1 - s i))),
    split3 (fun k => a k * (s' k * ∏ i ∈ Finset.range k, (1 - s' i)))]
  have hA : ∑ k ∈ Finset.range m, a k * (s' k * ∏ i ∈ Finset.range k, (1 - s' i)) =
      ∑ k ∈ Finset.range m, a k * (s k * ∏ i ∈ Finset.range k, (1 - s i)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [heq k (by omega) (by omega), hpre k hk.le]
  have hB' : ∑ t ∈ Finset.range L, a (m + 1 + t) * (s' (m + 1 + t) *
      ∏ i ∈ Finset.range (m + 1 + t), (1 - s' i)) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    rw [Finset.prod_eq_zero (i := m) (Finset.mem_range.mpr (by omega)) (by rw [hs'm]; ring)]
    ring
  rw [hA, hB', hsm, hs'm, hpre m le_rfl]
  set P := ∏ i ∈ Finset.range m, (1 - s i) with hP
  -- bound the tail
  have htail : ∑ t ∈ Finset.range L, a (m + 1 + t) * (s (m + 1 + t) *
      ∏ i ∈ Finset.range (m + 1 + t), (1 - s i)) ≤
      c * ∑ t ∈ Finset.range L, s (m + 1 + t) * ∏ i ∈ Finset.range (m + 1 + t), (1 - s i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_range] at ht
    rcases hs (m + 1 + t) with h0 | h1
    · rw [h0]; ring_nf; rfl
    · exact mul_le_mul_of_nonneg_right (hak _ (by omega) h1) (Wf_nonneg s hs _)
  have hsumW : ∑ t ∈ Finset.range L, s (m + 1 + t) * ∏ i ∈ Finset.range (m + 1 + t), (1 - s i) ≤
      P := by
    have e1 := one_sub_prod s (m + 1 + L)
    have e2 := one_sub_prod s (m + 1)
    rw [Finset.sum_range_add _ (m + 1) L] at e1
    rw [Finset.prod_range_succ, hsm, ← hP] at e2
    have hQ := prod_nonneg01 s hs (m + 1 + L)
    linarith
  have hPnn : 0 ≤ P := prod_nonneg01 s hs m
  have : c * ∑ t ∈ Finset.range L, s (m + 1 + t) * ∏ i ∈ Finset.range (m + 1 + t), (1 - s i) ≤
      a m * P := by
    calc _ ≤ c * P := mul_le_mul_of_nonneg_left hsumW hc
      _ ≤ a m * P := mul_le_mul_of_nonneg_right ham hPnn
  linarith

lemma toFinset_of_getLast (ρ : List (Fin n)) (e : Fin n) (h : ρ.getLast? = some e) :
    ρ.toFinset = insert e ρ.dropLast.toFinset := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h
  rw [List.dropLast_concat, List.toFinset_append]
  ext a; simp

lemma assort_rev (D : ListDist n) (r : Fin n → ℝ) (S : Finset (Fin n)) :
    revPolicy D r (assortPolicy S) = revAssort D r S := by
  have h := (lemma1 D r (assortPolicy S) S (fun j hj H _ => by simp [assortPolicy, hj])).1
  have h0 : ∑ ρ ∈ (prefixes D).filter (fun ρ => Disjoint ρ.toFinset S),
      adjPrice D r S ρ * prefProb D ρ * stopInd (assortPolicy S) ρ = 0 := by
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hd := (Finset.mem_filter.mp hρ).2
    unfold stopInd
    cases he : ρ.getLast? with
    | none => simp
    | some e =>
      have heS : e ∉ S := by
        intro heS
        exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr (List.mem_of_getLast? he)) heS
      simp [assortPolicy, heS, ind]
  linarith

lemma list_form (D : ListDist n) (r : Fin n → ℝ) (ψ : Policy n) (S : Finset (Fin n))
    (hS : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → ψ j H = true) :
    revPolicy D r ψ - revAssort D r S =
      ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (kap S ℓ),
        adjPrice D r S (ℓ.take (k + 1)) * W ψ ℓ k := by
  rw [(lemma1 D r ψ S hS).2]
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [W_eq_stopInd ψ ℓ k (lt_of_lt_of_le hk (kap_le S ℓ))]

lemma take_mem_prefixes (D : ListDist n) (ℓ : List (Fin n)) (hℓ : ℓ ∈ D.supp) (k : ℕ)
    (hk : k < ℓ.length) : ℓ.take (k + 1) ∈ prefixes D := by
  rw [mem_prefixes]
  refine ⟨?_, ℓ, hℓ, List.take_prefix _ _⟩
  rw [take_succ_eq ℓ k hk]; simp
  intro h; subst h; simp at hk

/-- the flip of one entry -/
def flipP (φ : Policy n) (j0 : Fin n) (H0 : Finset (Fin n)) : Policy n :=
  fun a H => φ a H || decide (a = j0 ∧ H = H0)

lemma sv_flip (φ : Policy n) (j0 : Fin n) (H0 : Finset (Fin n)) (ℓ : List (Fin n)) (i : ℕ)
    (hi : i < ℓ.length) (h : ¬ (ℓ[i] = j0 ∧ (ℓ.take i).toFinset = H0)) :
    sv (flipP φ j0 H0) ℓ i = sv φ ℓ i := by
  rw [sv_eq _ ℓ i hi, sv_eq _ ℓ i hi]
  unfold flipP
  simp [h]

lemma sv_flip_at (φ : Policy n) (j0 : Fin n) (H0 : Finset (Fin n)) (ℓ : List (Fin n)) (i : ℕ)
    (hi : i < ℓ.length) (h : ℓ[i] = j0 ∧ (ℓ.take i).toFinset = H0) :
    sv (flipP φ j0 H0) ℓ i = 1 := by
  rw [sv_eq _ ℓ i hi]
  unfold flipP
  simp [h, ind]

end HMFCore


open AssortOpt.HMF HMFCore

theorem solution {n : ℕ} (D : ListDist n) (hD : HasHistoryMonotoneFutures D)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    ∃ S : Finset (Fin n),
      IsGreatest (revPolicy D r '' {φ | IsMonotonePolicy φ}) (revPolicy D r (assortPolicy S)) ∧
      revPolicy D r (assortPolicy S) = revAssort D r S := by
  classical
  -- an optimal monotone policy with the maximum number of 1-entries
  let P : Finset (Policy n) := Finset.univ.filter (fun φ => IsMonotonePolicy φ)
  have hPne : P.Nonempty := ⟨fun _ _ => false,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ _ _ _ => le_refl _⟩⟩
  obtain ⟨φ0, hφ0P, hφ0max⟩ := Finset.exists_max_image P (revPolicy D r) hPne
  let O : Finset (Policy n) := P.filter (fun φ => revPolicy D r φ = revPolicy D r φ0)
  have hOne : O.Nonempty := ⟨φ0, Finset.mem_filter.mpr ⟨hφ0P, rfl⟩⟩
  let ones : Policy n → ℕ := fun φ =>
    (Finset.univ.filter (fun p : Fin n × Finset (Fin n) => φ p.1 p.2 = true)).card
  obtain ⟨φ, hφO, hφmax⟩ := Finset.exists_max_image O ones hOne
  have hφmono : IsMonotonePolicy φ := (Finset.mem_filter.mp (Finset.mem_filter.mp hφO).1).2
  have hφval : revPolicy D r φ = revPolicy D r φ0 := (Finset.mem_filter.mp hφO).2
  have hφopt : ∀ ψ, IsMonotonePolicy ψ → revPolicy D r ψ ≤ revPolicy D r φ := by
    intro ψ hψ
    rw [hφval]
    exact hφ0max ψ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψ⟩)
  have improve : ∀ ψ : Policy n, IsMonotonePolicy ψ → (∀ j H, φ j H = true → ψ j H = true) →
      (∃ j H, φ j H = false ∧ ψ j H = true) → revPolicy D r φ ≤ revPolicy D r ψ → False := by
    rintro ψ hψ hle ⟨j, H, hf, ht⟩ hrev
    have hψP : ψ ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψ⟩
    have hψO : ψ ∈ O := Finset.mem_filter.mpr ⟨hψP,
      le_antisymm (hφ0max ψ hψP) (hφval ▸ hrev)⟩
    have h1 := hφmax ψ hψO
    have h2 : ones φ < ones ψ := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨(j, H), by simp [ht], by simp [hf]⟩
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hle _ _ hp
    omega
  -- S: the items on which φ is the all-1 function
  let S : Finset (Fin n) := Finset.univ.filter (fun j => ∀ H, j ∉ H → φ j H = true)
  have hS : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → φ j H = true :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hnotS : ∀ j, j ∉ S → ∃ H, j ∉ H ∧ φ j H = false := by
    intro j hj
    by_contra hcon
    push Not at hcon
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun H hH => by simpa using hcon H hH⟩)
  -- a policy above φ agreeing with φ on S-disjoint histories has the same revenue
  have agree : ∀ ψ : Policy n, (∀ j H, φ j H = true → ψ j H = true) →
      (∀ ℓ ∈ D.supp, ∀ i < kap S ℓ, sv ψ ℓ i = sv φ ℓ i) →
      revPolicy D r φ ≤ revPolicy D r ψ := by
    intro ψ hle hsv
    have hSψ : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → ψ j H = true :=
      fun j hj H hH => hle j H (hS j hj H hH)
    have e1 := list_form D r φ S hS
    have e2 := list_form D r ψ S hSψ
    have : ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (kap S ℓ),
        adjPrice D r S (ℓ.take (k + 1)) * W ψ ℓ k =
        ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (kap S ℓ),
        adjPrice D r S (ℓ.take (k + 1)) * W φ ℓ k := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [W_congr φ ψ ℓ k (fun i hi => hsv ℓ hℓ i (by omega))]
    linarith
  have hmain : revPolicy D r φ ≤ revAssort D r S := by
    by_contra hlt
    push Not at hlt
    -- (C1) WLOG: φ_j(H) = 1 whenever H meets S
    have hC1 : ∀ j H, j ∉ H → ¬ Disjoint H S → φ j H = true := by
      by_contra hcon
      push Not at hcon
      obtain ⟨j0, H0, -, hnd, hf⟩ := hcon
      have hf' : φ j0 H0 = false := by simpa using hf
      let ψ : Policy n := fun a H => φ a H || decide (¬ Disjoint H S)
      apply improve ψ
      · intro a H H' haH' hHH'
        have hm := hφmono a H H' haH' hHH'
        simp only [ψ]
        rw [Bool.le_iff_imp] at hm ⊢
        intro h
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h ⊢
        rcases h with h | h
        · exact Or.inl (hm h)
        · exact Or.inr (fun h' => h (h'.mono_left hHH'))
      · intro j H h; simp [ψ, h]
      · exact ⟨j0, H0, hf', by simp [ψ, hnd]⟩
      · apply agree ψ (fun j H h => by simp [ψ, h])
        intro ℓ hℓ i hi
        have hil : i < ℓ.length := lt_of_lt_of_le hi (kap_le S ℓ)
        rw [sv_eq ψ ℓ i hil, sv_eq φ ℓ i hil]
        have hdisj : Disjoint (ℓ.take i).toFinset S :=
          ((disj_take_iff S ℓ i hil).mpr hi).mono_left (toFinset_take_mono ℓ (by omega))
        simp [ψ, hdisj]
    -- (C2) maximal zero histories
    let F : Fin n → Finset (Finset (Fin n)) := fun j =>
      Finset.univ.filter (fun H => j ∉ H ∧ φ j H = false)
    have hFne : ∀ j, j ∉ S → (F j).Nonempty := by
      intro j hj
      obtain ⟨H, hH⟩ := hnotS j hj
      exact ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH⟩⟩
    let Hm : Fin n → Finset (Fin n) := fun j =>
      if h : j ∉ S then Classical.choose (Finset.exists_maximal (hFne j h)) else ∅
    have hHm : ∀ j, j ∉ S → Maximal (· ∈ F j) (Hm j) := by
      intro j hj
      simp only [Hm, dif_pos hj]
      exact Classical.choose_spec (Finset.exists_maximal (hFne j hj))
    have hHm_mem : ∀ j, j ∉ S → j ∉ Hm j ∧ φ j (Hm j) = false := by
      intro j hj
      have := (hHm j hj).1
      simpa [F] using this
    have hHm_max : ∀ j, j ∉ S → ∀ H', j ∉ H' → Hm j ⊆ H' → H' ≠ Hm j → φ j H' = true := by
      intro j hj H' hjH' hsub hne
      by_contra hcon
      have hmem : H' ∈ F j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjH', by simpa using hcon⟩
      exact hne (le_antisymm ((hHm j hj).2 hmem hsub) hsub)
    have hHm_disj : ∀ j, j ∉ S → Disjoint (Hm j) S := by
      intro j hj
      by_contra hcon
      have := hC1 j (Hm j) (hHm_mem j hj).1 hcon
      rw [(hHm_mem j hj).2] at this
      exact Bool.false_ne_true this
    -- the flipped policy is monotone, above φ, and differs from φ
    have flip_mono : ∀ j, j ∉ S → IsMonotonePolicy (flipP φ j (Hm j)) := by
      intro j hj a H H' haH' hHH'
      have hm := hφmono a H H' haH' hHH'
      unfold flipP
      rw [Bool.le_iff_imp] at hm ⊢
      intro h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | ⟨rfl, rfl⟩
      · exact Or.inl (hm h)
      · by_cases hH' : H' = Hm a
        · exact Or.inr ⟨rfl, hH'⟩
        · exact Or.inl (hHm_max a hj H' haH' hHH' hH')
    have flip_ge : ∀ j H0, ∀ a H, φ a H = true → flipP φ j H0 a H = true := by
      intro j H0 a H h; simp [flipP, h]
    have flip_ne : ∀ j, j ∉ S → ∃ a H, φ a H = false ∧ flipP φ j (Hm j) a H = true :=
      fun j hj => ⟨j, Hm j, (hHm_mem j hj).2, by simp [flipP]⟩
    -- Ω(j): realizable prefixes ending in j with history H_j
    let Ω : Fin n → Finset (List (Fin n)) := fun j =>
      (prefixes D).filter (fun ρ => ρ.getLast? = some j ∧ ρ.dropLast.toFinset = Hm j)
    have take_mem_Ω : ∀ j, ∀ ℓ ∈ D.supp, ∀ m (hm : m < ℓ.length), ℓ[m] = j →
        (ℓ.take m).toFinset = Hm j → ℓ.take (m + 1) ∈ Ω j := by
      intro j ℓ hℓ m hm hj hH
      refine Finset.mem_filter.mpr ⟨take_mem_prefixes D ℓ hℓ m hm, ?_, ?_⟩
      · rw [getLast?_take ℓ m hm, hj]
      · rw [dropLast_take ℓ m hm, hH]
    -- (C3) each Ω(j) is nonempty
    have hΩne : ∀ j, j ∉ S → (Ω j).Nonempty := by
      intro j hj
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      apply improve (flipP φ j (Hm j)) (flip_mono j hj) (flip_ge j (Hm j)) (flip_ne j hj)
      apply agree _ (flip_ge j (Hm j))
      intro ℓ hℓ i hi
      have hil : i < ℓ.length := lt_of_lt_of_le hi (kap_le S ℓ)
      apply sv_flip φ j (Hm j) ℓ i hil
      rintro ⟨h1, h2⟩
      have := take_mem_Ω j ℓ hℓ i hil h1 h2
      rw [hcon] at this
      exact Finset.notMem_empty _ this
    -- S ≠ N
    have hScne : (Finset.univ.filter (fun j => j ∉ S)).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hall : ∀ j, j ∈ S := by
        intro j
        by_contra hj
        have : j ∈ Finset.univ.filter (fun j => j ∉ S) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
        rw [hcon] at this
        exact Finset.notMem_empty _ this
      have h1 := (lemma1 D r φ S hS).1
      have h0 : (prefixes D).filter (fun ρ => Disjoint ρ.toFinset S) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro ρ hρ hd
        obtain ⟨hne, -⟩ := mem_prefixes.mp hρ
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil ρ hne
        exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr ha) (hall a)
      rw [h0, Finset.sum_empty] at h1
      linarith
    -- the maximin item j* and value r*
    let g : Fin n → ℝ := fun j => if h : (Ω j).Nonempty then (Ω j).inf' h (adjPrice D r S) else 0
    obtain ⟨js, hjsmem, hjsmax⟩ := Finset.exists_max_image _ g hScne
    have hjs : js ∉ S := (Finset.mem_filter.mp hjsmem).2
    set rs := g js with hrs
    have hg_le : ∀ j, j ∉ S → ∀ ρ ∈ Ω j, g j ≤ adjPrice D r S ρ := by
      intro j hj ρ hρ
      simp only [g, dif_pos (hΩne j hj)]
      exact Finset.inf'_le _ hρ
    have hg_att : ∀ j, j ∉ S → ∃ ρ ∈ Ω j, adjPrice D r S ρ = g j := by
      intro j hj
      simp only [g, dif_pos (hΩne j hj)]
      obtain ⟨ρ, hρ, he⟩ := Finset.exists_mem_eq_inf' (hΩne j hj) (adjPrice D r S)
      exact ⟨ρ, hρ, he.symm⟩
    -- (42)
    have h42 : ∀ ρ ∈ prefixes D, Disjoint ρ.toFinset S → ∀ e, ρ.getLast? = some e →
        φ e ρ.dropLast.toFinset = true → adjPrice D r S ρ ≤ rs := by
      intro ρ hρ hd e he hφe
      have heS : e ∉ S := fun h =>
        Finset.disjoint_left.mp hd (List.mem_toFinset.mpr (List.mem_of_getLast? he)) h
      obtain ⟨ρ', hρ'Ω, hρ'eq⟩ := hg_att e heS
      obtain ⟨hρ'pre, hρ'end, hρ'H⟩ := Finset.mem_filter.mp hρ'Ω
      have hge : g e ≤ rs := hjsmax e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heS⟩)
      have hnsub : ¬ ρ.dropLast.toFinset ⊆ ρ'.dropLast.toFinset := by
        intro hsub
        rw [hρ'H] at hsub
        have := hφmono e _ _ (hHm_mem e heS).1 hsub
        rw [hφe, (hHm_mem e heS).2] at this
        exact absurd this (by decide)
      have hdom := hD ρ hρ ρ' hρ'pre (by rw [he, hρ'end]) hnsub
      have hdisj : Disjoint S (ρ.toFinset ∪ ρ'.toFinset) := by
        rw [Finset.disjoint_union_right]
        refine ⟨hd.symm, ?_⟩
        rw [toFinset_of_getLast ρ' e hρ'end, hρ'H, Finset.disjoint_insert_right]
        exact ⟨heS, (hHm_disj e heS).symm⟩
      have hcmp := hdom S hdisj
      have : adjPrice D r S ρ ≤ adjPrice D r S ρ' := by
        unfold adjPrice endPrice
        rw [he, hρ'end]
        have : ∑ j' ∈ S, r j' * condChoiceProb D S j' ρ' ≤
            ∑ j' ∈ S, r j' * condChoiceProb D S j' ρ :=
          Finset.sum_le_sum (fun j' hj' => mul_le_mul_of_nonneg_left (hcmp j' hj') (hr j'))
        simp only [Option.map_some, Option.getD_some]
        linarith
      linarith
    -- r* ≥ 0
    have hrs0 : 0 ≤ rs := by
      by_contra hneg
      push Not at hneg
      have h1 := (lemma1 D r φ S hS).1
      have hle : ∑ ρ ∈ (prefixes D).filter (fun ρ => Disjoint ρ.toFinset S),
          adjPrice D r S ρ * prefProb D ρ * stopInd φ ρ ≤ 0 := by
        apply Finset.sum_nonpos
        intro ρ hρ
        obtain ⟨hρp, hd⟩ := Finset.mem_filter.mp hρ
        unfold stopInd
        cases he : ρ.getLast? with
        | none => simp
        | some e =>
          simp only
          have hprod : 0 ≤ ∏ k : Fin ρ.dropLast.length,
              (1 - ind (φ (ρ.dropLast.get k) (ρ.take k).toFinset)) := by
            apply Finset.prod_nonneg
            intro k _
            rcases ind_cases (φ (ρ.dropLast.get k) (ρ.take k).toFinset) with h | h <;>
              rw [h] <;> norm_num
          cases hφe : φ e ρ.dropLast.toFinset with
          | false => simp [ind]
          | true =>
            have := h42 ρ hρp hd e he hφe
            have hpp := prefProb_pos D ρ hρp
            simp only [ind, if_true, one_mul]
            have : adjPrice D r S ρ * prefProb D ρ ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (by linarith) hpp.le
            exact mul_nonpos_of_nonpos_of_nonneg this hprod
      linarith
    -- flip at (j*, H_{j*}) does not decrease revenue
    apply improve (flipP φ js (Hm js)) (flip_mono js hjs) (flip_ge js (Hm js)) (flip_ne js hjs)
    have hSψ : ∀ j ∈ S, ∀ H : Finset (Fin n), j ∉ H → flipP φ js (Hm js) j H = true :=
      fun j hj H hH => flip_ge js (Hm js) j H (hS j hj H hH)
    have e1 := list_form D r φ S hS
    have e2 := list_form D r _ S hSψ
    have : ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (kap S ℓ),
          adjPrice D r S (ℓ.take (k + 1)) * W φ ℓ k ≤
        ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range (kap S ℓ),
          adjPrice D r S (ℓ.take (k + 1)) * W (flipP φ js (Hm js)) ℓ k := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      apply mul_le_mul_of_nonneg_left _ (D.pos ℓ hℓ).le
      have hnd := D.nodup ℓ hℓ
      by_cases hex : ∃ m, ∃ hm : m < kap S ℓ,
          ℓ[m]'(lt_of_lt_of_le hm (kap_le S ℓ)) = js ∧ (ℓ.take m).toFinset = Hm js
      · obtain ⟨m, hm, hmj, hmH⟩ := hex
        have hml : m < ℓ.length := lt_of_lt_of_le hm (kap_le S ℓ)
        unfold W
        apply first_stop (sv φ ℓ) (sv (flipP φ js (Hm js)) ℓ)
          (fun k => adjPrice D r S (ℓ.take (k + 1))) (kap S ℓ) m rs (sv_cases φ ℓ) hm
        · rw [sv_eq φ ℓ m hml, hmj, hmH, (hHm_mem js hjs).2]; rfl
        · exact sv_flip_at φ js (Hm js) ℓ m hml ⟨hmj, hmH⟩
        · intro i hi him
          have hil : i < ℓ.length := lt_of_lt_of_le hi (kap_le S ℓ)
          apply sv_flip φ js (Hm js) ℓ i hil
          rintro ⟨h1, -⟩
          apply him
          have : ℓ[i] = ℓ[m] := by rw [h1, hmj]
          exact (List.Nodup.getElem_inj_iff hnd).mp this
        · exact hrs0
        · exact hg_le js hjs _ (take_mem_Ω js ℓ hℓ m hml hmj hmH)
        · intro k hk hsk
          have hkl : k < ℓ.length := lt_of_lt_of_le hk (kap_le S ℓ)
          apply h42 (ℓ.take (k + 1)) (take_mem_prefixes D ℓ hℓ k hkl)
            ((disj_take_iff S ℓ k hkl).mpr hk) ℓ[k] (getLast?_take ℓ k hkl)
          rw [dropLast_take ℓ k hkl]
          rw [sv_eq φ ℓ k hkl] at hsk
          revert hsk
          cases φ ℓ[k] (ℓ.take k).toFinset <;> simp [ind]
      · push Not at hex
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [W_congr φ (flipP φ js (Hm js)) ℓ k]
        intro i hi
        have hil : i < ℓ.length := lt_of_lt_of_le (lt_of_le_of_lt hi hk) (kap_le S ℓ)
        apply sv_flip φ js (Hm js) ℓ i hil
        rintro ⟨h1, h2⟩
        exact hex i (by omega) h1 h2
    linarith
  refine ⟨S, ⟨⟨assortPolicy S, fun _ _ _ _ _ => le_refl _, rfl⟩, ?_⟩, assort_rev D r S⟩
  rintro _ ⟨ψ, hψ, rfl⟩
  rw [assort_rev D r S]
  exact le_trans (hφopt ψ hψ) hmain
