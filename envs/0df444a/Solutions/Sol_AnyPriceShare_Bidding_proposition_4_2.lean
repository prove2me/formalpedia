-- Prove2me | solution 1 for AnyPriceShare.Bidding.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:52:02.833+00:00
-- url     : https://prove2.me/submissions/54b9b66f-7156-484c-a18e-e235cfb670e7

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

open AnyPriceShare.Bidding

namespace APSP42Sol

/-- Any feasible price vector bounds the AnyPrice share from above. -/
theorem anyPrice_le_of_prices {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ)
    (hβ : 0 ≤ β) (S : Finset (Fin m)) (X : ℝ) (p : Fin m → ℝ) (hp0 : ∀ j ∈ S, 0 ≤ p j)
    (hp1 : ∑ j ∈ S, p j = 1) (hX : ∀ T ⊆ S, ∑ j ∈ T, p j ≤ β → addVal u T ≤ X) :
    anyPrice β (addVal u) S ≤ X := by
  unfold anyPrice
  have hne : ∀ q : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1},
      Nonempty {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, q.1 j ≤ β} :=
    fun q => ⟨⟨∅, Finset.empty_subset _, by simpa using hβ⟩⟩
  have hbdd : ∀ q : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1},
      BddAbove (Set.range fun T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, q.1 j ≤ β} =>
        addVal u T.1) := fun q => (Set.finite_range _).bddAbove
  refine ciInf_le_of_le ⟨0, ?_⟩ ⟨p, hp0, hp1⟩ ?_
  · rintro _ ⟨q, rfl⟩
    refine le_ciSup_of_le (hbdd q) ⟨∅, Finset.empty_subset _, by simpa using hβ⟩ ?_
    simp [addVal]
  · haveI := hne ⟨p, hp0, hp1⟩
    exact ciSup_le fun T => hX T.1 T.2.1 T.2.2

theorem anyPrice_empty {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) :
    anyPrice β w ∅ = 0 := by
  unfold anyPrice
  haveI : IsEmpty {p : Fin m → ℝ // (∀ j ∈ (∅ : Finset (Fin m)), 0 ≤ p j) ∧
      ∑ j ∈ (∅ : Finset (Fin m)), p j = 1} := ⟨fun q => by simpa using q.2.2⟩
  exact Real.iInf_of_isEmpty _


/-- The set whose supremum is the TPS. -/
theorem tps_bdd {m : ℕ} (u : Fin m → ℝ) (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) :
    BddAbove {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} := by
  refine ⟨β * ∑ j ∈ S, u j, fun z hz => ?_⟩
  simp only [Set.mem_ofPred_eq] at hz
  rw [← hz]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => min_le_left _ _) hβ.le

theorem tps_zero_mem {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (S : Finset (Fin m)) :
    (0 : ℝ) ∈ {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} := by
  simp only [Set.mem_ofPred_eq]
  rw [Finset.sum_eq_zero fun j _ => min_eq_right (hu j)]; simp

theorem tps_cont {m : ℕ} (u : Fin m → ℝ) (β : ℝ) (S : Finset (Fin m)) :
    Continuous fun z : ℝ => β * ∑ j ∈ S, min (u j) z := by
  fun_prop

theorem tps_mem {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) : β * ∑ j ∈ S, min (u j) (tps β u S) = tps β u S := by
  have hc : IsClosed {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} :=
    isClosed_eq (tps_cont u β S) continuous_id
  exact hc.csSup_mem ⟨0, tps_zero_mem u hu β S⟩ (tps_bdd u β hβ S)

theorem tps_nonneg {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) : 0 ≤ tps β u S :=
  le_csSup (tps_bdd u β hβ S) (tps_zero_mem u hu β S)

/-- Above the TPS the capped proportional share is strictly below the cap (intermediate value
theorem). -/
theorem tps_lt {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) (z : ℝ) (hz : tps β u S < z) : β * ∑ j ∈ S, min (u j) z < z := by
  by_contra hcon
  push Not at hcon
  set g : ℝ → ℝ := fun t => β * ∑ j ∈ S, min (u j) t - t with hg
  have hgc : Continuous g := (tps_cont u β S).sub continuous_id
  set b' := max z (β * ∑ j ∈ S, u j)
  have hzb : z ≤ b' := le_max_left _ _
  have hgz : 0 ≤ g z := by simp only [hg]; linarith
  have hgb : g b' ≤ 0 := by
    have : β * ∑ j ∈ S, min (u j) b' ≤ β * ∑ j ∈ S, u j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => min_le_left _ _) hβ.le
    simp only [hg]; linarith [le_max_right z (β * ∑ j ∈ S, u j)]
  obtain ⟨t, ⟨ht1, -⟩, ht⟩ :=
    intermediate_value_Icc' hzb hgc.continuousOn ⟨hgb, hgz⟩
  have hmem : t ∈ {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} := by
    simp only [Set.mem_ofPred_eq]; simp only [hg] at ht; linarith
  have := le_csSup (tps_bdd u β hβ S) hmem
  unfold tps at hz
  linarith

end APSP42Sol

open APSP42Sol in
theorem solution {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j)
    (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) :
    anyPrice β (addVal u) S ≤ tps β u S := by
  classical
  set w := tps β u S with hw
  have hw0 : 0 ≤ w := tps_nonneg u hu β hβ S
  rcases S.eq_empty_or_nonempty with hS | hSne
  · subst hS; rw [anyPrice_empty]; exact hw0
  set K := S.filter (fun j => w < u j) with hK
  set k : ℕ := K.card with hk
  set U := ∑ j ∈ S.filter (fun j => ¬ w < u j), u j with hU
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun j _ => hu j
  -- the capped sum near the TPS
  have hsplit : ∀ z, w ≤ z → (∀ j ∈ K, z ≤ u j) → ∑ j ∈ S, min (u j) z = k * z + U := by
    intro z hwz hzK
    rw [← Finset.sum_filter_add_sum_filter_not S (fun j => w < u j)]
    congr 1
    · rw [Finset.sum_congr rfl (fun j hj => min_eq_right (hzK j hj))]
      simp [hk, hK]
    · refine Finset.sum_congr rfl fun j hj => min_eq_left ?_
      simp only [Finset.mem_filter, not_lt] at hj
      linarith [hj.2]
  have hwfix : β * (k * w + U) = w := by
    rw [← hsplit w le_rfl (fun j hj => (Finset.mem_filter.1 hj).2.le)]
    exact tps_mem u hu β hβ S
  -- `β k < 1`
  have hβk : β * k < 1 := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simp
    · have hKne : K.Nonempty := Finset.card_pos.1 hpos
      set l := (K.image u).min' (hKne.image u)
      have hl : w < l := by
        obtain ⟨j, hj, hjl⟩ := Finset.mem_image.1 ((K.image u).min'_mem (hKne.image u))
        have hlj : l = u j := hjl.symm
        rw [hlj]; exact (Finset.mem_filter.1 hj).2
      set z := (w + l) / 2
      have hwz : w < z := by simp only [z]; linarith
      have hzl : z < l := by simp only [z]; linarith
      have hlt := tps_lt u hu β hβ S z hwz
      rw [hsplit z hwz.le (fun j hj => le_trans hzl.le ((K.image u).min'_le _ (Finset.mem_image_of_mem u hj)))] at hlt
      by_contra hcon
      push Not at hcon
      have : 0 ≤ (β * k - 1) * (z - w) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  set c := 1 - β * k with hc
  have hc0 : 0 < c := by linarith
  have hwU : β * U = w * c := by rw [hc]; linarith [hwfix]
  -- bundles avoiding `K` are worth at most `U`
  have hnoK : ∀ T ⊆ S, (∀ j ∈ T, ¬ w < u j) → addVal u T ≤ U := by
    intro T hT hTK
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hu j
    intro j hj
    exact Finset.mem_filter.2 ⟨hT hj, hTK j hj⟩
  -- prices are nonnegative on `T ⊆ S`; an item priced above `β` is not affordable
  have hafford : ∀ (p : Fin m → ℝ), (∀ j ∈ S, 0 ≤ p j) → ∀ T ⊆ S, ∑ j ∈ T, p j ≤ β →
      ∀ j ∈ T, p j ≤ β := by
    intro p hp T hT hTp j hj
    exact le_trans (Finset.single_le_sum (fun i hi => hp i (hT hi)) hj) hTp
  rcases hU0.lt_or_eq with hUpos | hUz
  · -- main case: `v(M ∖ K) > 0`, argue by contradiction with prices `β + ε` on `K`
    by_contra hlt
    push Not at hlt
    set A := anyPrice β (addVal u) S
    have hA : 0 < A := lt_of_le_of_lt hw0 hlt
    set d := A - w
    have hd : 0 < d := by simp only [d]; linarith
    set ε := d * c / (2 * (k + 1) * A)
    have hε : 0 < ε := by positivity
    set q := β + ε
    have hkε : (k : ℝ) * ε * A = d * c * (k / (2 * (k + 1))) := by
      simp only [ε]; field_simp
    have hr0 : 0 ≤ (k : ℝ) / (2 * (k + 1)) := by positivity
    have hr1 : (k : ℝ) / (2 * (k + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    set r := (k : ℝ) / (2 * (k + 1))
    -- `1 - k q = c - k ε > 0` and `β U < A (1 - k q)`
    have hkq : 1 - k * q = c - k * ε := by simp only [q, c]; ring
    have hdr : d * r < d := by nlinarith
    have hdA : d ≤ A := by simp only [d]; linarith
    have hpos' : 0 < (c - k * ε) * A := by
      have : (c - k * ε) * A = c * (A - d * r) := by rw [sub_mul, hkε]; ring
      rw [this]; exact mul_pos hc0 (by linarith)
    have hm : 0 < c - k * ε := pos_of_mul_pos_left hpos' hA.le
    have hmain : β * U < A * (c - k * ε) := by
      have : A * (c - k * ε) - β * U = c * d * (1 - r) := by
        rw [hwU, mul_sub, mul_comm A (k * ε), hkε]; simp only [d]; ring
      have : 0 < c * d * (1 - r) := by
        apply mul_pos (mul_pos hc0 hd); linarith
      linarith
    -- the price vector
    let p : Fin m → ℝ := fun j => if w < u j then q else (c - k * ε) * u j / U
    have hp0 : ∀ j ∈ S, 0 ≤ p j := by
      intro j _
      simp only [p]
      split_ifs
      · positivity
      · exact div_nonneg (mul_nonneg hm.le (hu j)) hU0
    have hp1 : ∑ j ∈ S, p j = 1 := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun j => w < u j)]
      rw [Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_filter.1 hj).2),
        Finset.sum_congr rfl (fun j hj => if_neg (Finset.mem_filter.1 hj).2)]
      rw [Finset.sum_const, ← Finset.sum_div, ← Finset.mul_sum, ← hU, nsmul_eq_mul,
        mul_div_assoc, div_self hUpos.ne', ← hk]
      simp only [q]; rw [hc]; ring
    have hbound : A ≤ β * U / (c - k * ε) := by
      refine anyPrice_le_of_prices u hu β hβ.le S _ p hp0 hp1 ?_
      intro T hT hTp
      have hTK : ∀ j ∈ T, ¬ w < u j := by
        intro j hj hjK
        have := hafford p hp0 T hT hTp j hj
        simp only [p, if_pos hjK, q] at this
        linarith
      have hsum : ∑ j ∈ T, p j = (c - k * ε) / U * addVal u T := by
        rw [addVal, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [p, if_neg (hTK j hj)]; ring
      rw [hsum] at hTp
      rw [le_div_iff₀ hm]
      have := (div_mul_eq_mul_div (c - k * ε) U (addVal u T))
      rw [this, div_le_iff₀ hUpos] at hTp
      linarith
    rw [le_div_iff₀ hm] at hbound
    linarith
  · -- degenerate case: `v(M ∖ K) = 0`
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · obtain ⟨j0, hj0⟩ := hSne
      refine anyPrice_le_of_prices u hu β hβ.le S _ (fun j => if j = j0 then 1 else 0)
        (fun j _ => by split_ifs <;> norm_num) (by simp [hj0]) ?_
      intro T hT _
      have hTK : ∀ j ∈ T, ¬ w < u j := by
        intro j hj hjK
        have : j ∈ K := Finset.mem_filter.2 ⟨hT hj, hjK⟩
        have hc0' : K.card = 0 := by rw [← hk]; exact h0
        rw [Finset.card_eq_zero] at hc0'
        rw [hc0'] at this
        simp at this
      linarith [hnoK T hT hTK]
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast hpos
      refine anyPrice_le_of_prices u hu β hβ.le S _ (fun j => if w < u j then 1 / k else 0)
        (fun j _ => by split_ifs <;> positivity) ?_ ?_
      · rw [← Finset.sum_filter]; simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← hK, ← hk]; field_simp
      · intro T hT hTp
        have hTK : ∀ j ∈ T, ¬ w < u j := by
          intro j hj hjK
          have := hafford _ (fun j _ => by split_ifs <;> positivity) T hT hTp j hj
          simp only [if_pos hjK] at this
          rw [div_le_iff₀ hkpos] at this
          linarith
        linarith [hnoK T hT hTK]
