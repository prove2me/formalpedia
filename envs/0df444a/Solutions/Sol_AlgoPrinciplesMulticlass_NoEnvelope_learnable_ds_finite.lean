-- Prove2me | solution 1 for AlgoPrinciplesMulticlass.NoEnvelope.learnable_ds_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:10:11.060171+00:00
-- url     : https://prove2.me/submissions/7339e305-295d-4d2f-a896-9748a225f485

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC
universe u

section
namespace AlgoPrinciplesMulticlass
open NoEnvelope MeasureTheory Classical


namespace Dev.DsFinite

lemma bad_card {Y : Type*} {N : ℕ} (B : Finset (Fin N → Y))
    (hB : ∀ w ∈ B, ∀ i, ∃ g ∈ B, g i ≠ w i ∧ ∀ j, j ≠ i → g j = w j)
    (i : Fin N) (φ : (Fin N → Y) → Y)
    (hφ : ∀ w ∈ B, ∀ w' ∈ B, (∀ j, j ≠ i → w j = w' j) → φ w = φ w') :
    B.card ≤ 2 * (B.filter (fun w => φ w ≠ w i)).card := by
  classical
  let σ : (Fin N → Y) → (Fin N → Y) := fun w => if h : w ∈ B then (hB w h i).choose else w
  have hσ : ∀ w ∈ B, σ w ∈ B ∧ σ w i ≠ w i ∧ ∀ j, j ≠ i → σ w j = w j := by
    intro w hw
    simp only [σ, dif_pos hw]
    exact (hB w hw i).choose_spec
  have h1 : (B.filter (fun w => φ w = w i)).card ≤ (B.filter (fun w => φ w ≠ w i)).card := by
    apply Finset.card_le_card_of_injOn σ
    · intro w hw
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hw ⊢
      obtain ⟨hwB, hwφ⟩ := hw
      obtain ⟨h1, h2, h3⟩ := hσ w hwB
      refine ⟨h1, ?_⟩
      have : φ (σ w) = φ w := hφ _ h1 _ hwB (fun j hj => h3 j hj)
      rw [this, hwφ]
      exact fun h => h2 h.symm
    · intro w hw w' hw' heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hw hw'
      obtain ⟨_, _, h3⟩ := hσ w hw.1
      obtain ⟨_, _, h3'⟩ := hσ w' hw'.1
      funext j
      by_cases hj : j = i
      · subst hj; rw [← hw.2, ← hw'.2]
        exact hφ _ hw.1 _ hw'.1 (fun k hk => by rw [← h3 k hk, ← h3' k hk, heq])
      · rw [← h3 j hj, ← h3' j hj, heq]
  have := Finset.card_filter_add_card_filter_not (s := B) (fun w => φ w = w i)
  have e : (B.filter (fun w => ¬ φ w = w i)) = B.filter (fun w => φ w ≠ w i) := rfl
  rw [e] at this
  omega

lemma sum_bad {Y : Type*} {N m : ℕ} (B : Finset (Fin N → Y))
    (hB : ∀ w ∈ B, ∀ i, ∃ g ∈ B, g i ≠ w i ∧ ∀ j, j ≠ i → g j = w j)
    (a : Fin m → Fin N) (g : (Fin N → Y) → Fin N → Y)
    (hg : ∀ i, i ∉ Set.range a → ∀ w ∈ B, ∀ w' ∈ B, (∀ j, j ≠ i → w j = w' j) → g w i = g w' i) :
    (N - m) * B.card ≤ 2 * ∑ w ∈ B, (Finset.univ.filter (fun i => g w i ≠ w i)).card := by
  classical
  have hsw : ∑ w ∈ B, (Finset.univ.filter (fun i => g w i ≠ w i)).card
      = ∑ i : Fin N, (B.filter (fun w => g w i ≠ w i)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hsw]
  have hr : (Finset.univ.image a).card ≤ m := by
    calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
      _ = m := by simp
  have hun : N - m ≤ (Finset.univ.filter (fun i : Fin N => i ∉ Set.range a)).card := by
    have : (Finset.univ.filter (fun i : Fin N => i ∉ Set.range a)) = Finset.univ \ Finset.univ.image a := by
      ext i; simp
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  calc (N - m) * B.card ≤ (Finset.univ.filter (fun i : Fin N => i ∉ Set.range a)).card * B.card :=
        Nat.mul_le_mul_right _ hun
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin N => i ∉ Set.range a), B.card := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => i ∉ Set.range a),
          2 * (B.filter (fun w => g w i ≠ w i)).card := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact bad_card B hB i (fun w => g w i) (fun w hw w' hw' h => hg i hi w hw w' hw' h)
    _ ≤ 2 * ∑ i : Fin N, (B.filter (fun w => g w i ≠ w i)).card := by
        rw [← Finset.mul_sum]
        apply Nat.mul_le_mul_left
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

lemma many_big {Y : Type*} {N : ℕ} (hN : 0 < N) (B : Finset (Fin N → Y)) (c : (Fin N → Y) → ℕ)
    (hc : ∀ w ∈ B, c w ≤ N) (hs : 3 * N * B.card ≤ 8 * ∑ w ∈ B, c w) :
    B.card ≤ 4 * (B.filter (fun w => N < 8 * c w)).card := by
  classical
  have e := Finset.sum_filter_add_sum_filter_not B (fun w => N < 8 * c w) c
  have h1 : ∑ w ∈ B.filter (fun w => N < 8 * c w), c w ≤ (B.filter (fun w => N < 8 * c w)).card * N := by
    calc _ ≤ ∑ w ∈ B.filter (fun w => N < 8 * c w), N :=
          Finset.sum_le_sum (fun w hw => hc w (Finset.mem_filter.1 hw).1)
      _ = _ := by simp
  have h2 : 8 * ∑ w ∈ B.filter (fun w => ¬ N < 8 * c w), c w ≤ B.card * N := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ w ∈ B.filter (fun w => ¬ N < 8 * c w), N :=
          Finset.sum_le_sum (fun w hw => by have := (Finset.mem_filter.1 hw).2; omega)
      _ ≤ ∑ w ∈ B, N := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = _ := by simp
  have : 3 * N * B.card ≤ 8 * ((B.filter (fun w => N < 8 * c w)).card * N) + B.card * N := by
    nlinarith
  have h3 : N * B.card ≤ N * (4 * (B.filter (fun w => N < 8 * c w)).card) := by nlinarith
  exact Nat.le_of_mul_le_mul_left h3 hN


lemma avg {Y : Type*} {N m : ℕ} (B : Finset (Fin N → Y)) (hne : B.Nonempty)
    (E : (Fin m → Fin N) → (Fin N → Y) → Prop)
    (h : ∀ a, B.card ≤ 4 * (B.filter (E a)).card) :
    ∃ w ∈ B, N ^ m ≤ 4 * (Finset.univ.filter (fun a => E a w)).card := by
  by_contra hcon
  push_neg at hcon
  have h1 : ∑ w ∈ B, 4 * (Finset.univ.filter fun a => E a w).card < ∑ w ∈ B, N ^ m :=
    Finset.sum_lt_sum_of_nonempty hne hcon
  have h2 : ∑ w ∈ B, (Finset.univ.filter fun a => E a w).card
      = ∑ a : Fin m → Fin N, (B.filter (E a)).card := by
    simp only [Finset.card_filter]; exact Finset.sum_comm
  have h3 : ∑ a : Fin m → Fin N, B.card ≤ ∑ a : Fin m → Fin N, 4 * (B.filter (E a)).card :=
    Finset.sum_le_sum (fun a _ => h a)
  rw [← Finset.mul_sum, h2, Finset.sum_const, smul_eq_mul] at h1
  rw [Finset.sum_const, ← Finset.mul_sum, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    smul_eq_mul] at h3
  simp only [Fintype.card_fin] at h3
  nlinarith

lemma ennreal_lt1 {N c : ℕ} (hN : 0 < N) (h : N < 8 * c) :
    ENNReal.ofReal (1 / 8) < (N : ENNReal)⁻¹ * c := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ENNReal)⁻¹ * c = ENNReal.ofReal ((c : ℝ) / N) := by
    rw [ENNReal.ofReal_div_of_pos hNr, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      div_eq_mul_inv, mul_comm]
  rw [e]
  have hpos : (0 : ℝ) < (c : ℝ) / N := by
    apply div_pos _ hNr
    have : 0 < c := by omega
    exact_mod_cast this
  rw [ENNReal.ofReal_lt_ofReal_iff hpos, div_lt_div_iff₀ (by norm_num) hNr]
  have : (N : ℝ) < 8 * c := by exact_mod_cast h
  linarith

lemma ennreal_lt2 {N k n : ℕ} (hN : 0 < N) (h : N ^ n ≤ 4 * k) :
    ENNReal.ofReal (1 / 8) < (k : ENNReal) * ((N : ENNReal)⁻¹) ^ n := by
  have hNr : (0 : ℝ) < (N : ℝ) ^ n := by positivity
  have e : (k : ENNReal) * ((N : ENNReal)⁻¹) ^ n = ENNReal.ofReal ((k : ℝ) / (N : ℝ) ^ n) := by
    rw [ENNReal.ofReal_div_of_pos hNr, ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, div_eq_mul_inv]
    rw [ENNReal.inv_pow]
  rw [e]
  have hh : (N : ℝ) ^ n ≤ 4 * k := by exact_mod_cast h
  have hpos : (0 : ℝ) < (k : ℝ) / (N : ℝ) ^ n := by
    apply div_pos _ hNr
    have : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        have : 0 < N ^ n := by positivity
        omega
      · exact h0
    exact_mod_cast this
  rw [ENNReal.ofReal_lt_ofReal_iff hpos, div_lt_div_iff₀ (by norm_num) hNr]
  linarith

end Dev.DsFinite

open Dev.DsFinite in
theorem chk_learnable_ds_finite {X Y : Type*} (G : Set (X → Y)) (hG : PACLearnable G) :
    MulticlassDS.Compress.dsDim G < ⊤ := by
  by_contra hnot
  have htop : MulticlassDS.Compress.dsDim G = ⊤ := top_le_iff.1 (not_lt.1 hnot)
  obtain ⟨A, hA⟩ := hG
  obtain ⟨n, hn⟩ := hA (1/8) (1/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsh : ∃ (N : ℕ) (S : Fin N → X), 4 * n + 4 ≤ N ∧ MulticlassDS.Compress.DSShatters G S := by
    by_contra hcon
    push_neg at hcon
    have hle : MulticlassDS.Compress.dsDim G ≤ ((4 * n + 4 : ℕ) : ℕ∞) := by
      unfold MulticlassDS.Compress.dsDim
      refine iSup_le fun k => iSup_le fun S => iSup_le fun hS => ?_
      by_contra hk
      exact hcon k S (by exact_mod_cast (not_le.1 hk).le) hS
    rw [htop] at hle
    exact ENat.coe_ne_top _ (top_le_iff.1 hle)
  obtain ⟨N, S, hNge, B, hBsub, hne0, hfin, hnb⟩ := hsh
  have hN : 0 < N := by omega
  have hex : ∀ w ∈ B, ∃ h ∈ G, h ∘ S = w := fun w hw => hBsub hw
  obtain ⟨w0, hw0⟩ := hne0
  obtain ⟨h0, -, -⟩ := hex w0 hw0
  haveI : Nonempty (X → Y) := ⟨h0⟩
  choose! Hf hHG hHS using hex
  let Bf := hfin.toFinset
  have hmem : ∀ w, w ∈ Bf ↔ w ∈ B := fun w => hfin.mem_toFinset
  have hBne : Bf.Nonempty := ⟨w0, (hmem _).2 hw0⟩
  have hBf : ∀ w ∈ Bf, ∀ i, ∃ g ∈ Bf, g i ≠ w i ∧ ∀ j, j ≠ i → g j = w j := by
    intro w hw i
    obtain ⟨g, hg, h1, h2⟩ := hnb w ((hmem _).1 hw) i
    exact ⟨g, (hmem _).2 hg, h1, h2⟩
  letI : MeasurableSpace X := ⊤
  let U : Measure (Fin N) := (N : ENNReal)⁻¹ • Measure.count
  have hUsing : ∀ j : Fin N, U {j} = (N : ENNReal)⁻¹ := by
    intro j; simp [U]
  have hUfin : ∀ s : Finset (Fin N), U ↑s = (N : ENNReal)⁻¹ * s.card := by
    intro s; simp [U, Measure.count_apply_finset]
  haveI : IsProbabilityMeasure U := by
    constructor
    have := hUfin Finset.univ
    simp only [Finset.coe_univ, Finset.card_univ, Fintype.card_fin] at this
    rw [this]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)
  have hSm : Measurable S := Measurable.of_discrete
  let D : @Measure X ⊤ := U.map S
  haveI hDp : @IsProbabilityMeasure X ⊤ D := Measure.isProbabilityMeasure_map hSm.aemeasurable
  -- the learner's output
  let f : (Fin n → Fin N) → (Fin N → Y) → X → Y := fun a w => A n (fun k => (S (a k), w (a k)))
  let c : (Fin n → Fin N) → (Fin N → Y) → ℕ := fun a w =>
    (Finset.univ.filter (fun i => f a w (S i) ≠ w i)).card
  have hlab : ∀ w ∈ Bf, ∀ a : Fin n → Fin N,
      labelSample (Hf w) (S ∘ a) = fun k => (S (a k), w (a k)) := by
    intro w hw a
    funext k
    have := congrFun (hHS w ((hmem _).1 hw)) (a k)
    simp only [labelSample, Function.comp] at this ⊢
    rw [this]
  have hloss : ∀ w ∈ Bf, ∀ a : Fin n → Fin N,
      popLoss D (f a w) (Hf w) = (N : ENNReal)⁻¹ * (c a w) := by
    intro w hw a
    have hS' : ∀ i, Hf w (S i) = w i := fun i => congrFun (hHS w ((hmem _).1 hw)) i
    unfold popLoss
    rw [Measure.map_apply hSm (MeasurableSet.of_discrete)]
    have : S ⁻¹' {x | f a w x ≠ Hf w x} = ↑(Finset.univ.filter (fun i => f a w (S i) ≠ w i)) := by
      ext i; simp [hS']
    rw [this, hUfin]
  let E : (Fin n → Fin N) → (Fin N → Y) → Prop := fun a w => N < 8 * c a w
  have hbig : ∀ a, Bf.card ≤ 4 * (Bf.filter (E a)).card := by
    intro a
    have hsb := sum_bad (m := n) Bf hBf a (fun w i => f a w (S i)) (by
      intro i hi w hw w' hw' hagree
      have : f a w = f a w' := by
        simp only [f]
        congr 1
        funext k
        have hk : a k ≠ i := fun h => hi ⟨k, h⟩
        rw [hagree _ hk]
      simp only [this])
    apply many_big hN Bf (c a)
    · intro w _
      calc c a w ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_filter_le _ _
        _ = N := by simp
    · have h4 : 3 * N ≤ 4 * (N - n) := by omega
      calc 3 * N * Bf.card ≤ 4 * (N - n) * Bf.card := Nat.mul_le_mul_right _ h4
        _ = 4 * ((N - n) * Bf.card) := by ring
        _ ≤ 4 * (2 * ∑ w ∈ Bf, c a w) := Nat.mul_le_mul_left _ hsb
        _ = 8 * ∑ w ∈ Bf, c a w := by ring
  obtain ⟨w, hwB, hcnt⟩ := avg Bf hBne E (fun a => by convert hbig a)
  have hlow := hn n le_rfl (Hf w) (hHG w ((hmem _).1 hwB)) D hDp
  unfold failProb at hlow
  let F : (Fin n → Fin N) → Fin n → X := fun a k => S (a k)
  have hF : Measurable F := Measurable.of_discrete
  have hmap : Measure.pi (fun _ : Fin n => D) = (Measure.pi (fun _ : Fin n => U)).map F := by
    rw [Measure.pi_map_pi (fun _ => hSm.aemeasurable)]
  rw [hmap] at hlow
  have h1 := Measure.le_map_apply hF.aemeasurable
    {xs : Fin n → X | ENNReal.ofReal (1 / 8) < popLoss D (A n (labelSample (Hf w) xs)) (Hf w)}
    (μ := Measure.pi (fun _ : Fin n => U))
  set Ef := Finset.univ.filter (fun a : Fin n → Fin N => E a w) with hEf
  have hsub : (↑Ef : Set (Fin n → Fin N)) ⊆ F ⁻¹'
      {xs : Fin n → X | ENNReal.ofReal (1 / 8) < popLoss D (A n (labelSample (Hf w) xs)) (Hf w)} := by
    intro a ha
    simp only [hEf, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have e1 : labelSample (Hf w) (F a) = fun k => (S (a k), w (a k)) := hlab w hwB a
    rw [e1]
    have := hloss w hwB a
    simp only [f] at this
    rw [this]
    exact ennreal_lt1 hN ha
  have h2 : Measure.pi (fun _ : Fin n => U) ↑Ef = (Ef.card : ENNReal) * ((N : ENNReal)⁻¹) ^ n := by
    rw [← sum_measure_singleton]
    have : ∀ a ∈ Ef, Measure.pi (fun _ : Fin n => U) {a} = ((N : ENNReal)⁻¹) ^ n := by
      intro a _
      rw [Measure.pi_singleton]
      simp [hUsing]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hcnt' : N ^ n ≤ 4 * Ef.card := by convert hcnt
  have h3 := ennreal_lt2 (k := Ef.card) hN hcnt'
  rw [← h2] at h3
  exact absurd (lt_of_lt_of_le h3 ((measure_mono hsub).trans (h1.trans hlow))) (lt_irrefl _)
end AlgoPrinciplesMulticlass
end

theorem solution : type_of% @AlgoPrinciplesMulticlass.chk_learnable_ds_finite := @AlgoPrinciplesMulticlass.chk_learnable_ds_finite
