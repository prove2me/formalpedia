-- Prove2me | solution 1 for AffinePolicies.TwoGap.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:56:00.490907+00:00
-- url     : https://prove2.me/submissions/f2459015-f57a-4f8b-9066-03271fc12392

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

set_option autoImplicit false

namespace Pb100bbd9

open Finset AffinePolicies.TwoGap AffinePolicies.Simplex Matrix

theorem Bmul (m : ℕ) (v : Fin m → ℝ) (i : Fin m) :
    (B6 m *ᵥ v) i = 1 / Real.sqrt m * ∑ k, v k + (1 - 1 / Real.sqrt m) * v i := by
  simp only [B6, mulVec, dotProduct]
  have : ∀ k, (if i = k then (1 : ℝ) else 1 / Real.sqrt m) * v k
      = 1 / Real.sqrt m * v k + (if i = k then (1 - 1 / Real.sqrt m) * v i else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib, Finset.sum_ite_eq,
    ← Finset.mul_sum]
  simp

theorem cost_eq (m : ℕ) (x : Fin m → ℝ) (v : Fin m → ℝ) :
    c6 m ⬝ᵥ x + d6 m ⬝ᵥ v = ∑ i, v i := by
  simp [c6, d6, dotProduct]

theorem mem0 (m : ℕ) : (0 : Fin m → ℝ) ∈ U6 m :=
  subset_convexHull ℝ _ (by simp)

theorem memE (m : ℕ) (j : Fin m) : (Pi.single j (1 : ℝ) : Fin m → ℝ) ∈ U6 m :=
  subset_convexHull ℝ _ (by simp)

theorem memLow (m : ℕ) : bLow m ∈ U6 m :=
  subset_convexHull ℝ _ (by simp)

theorem memHigh (m : ℕ) : bHigh m ∈ U6 m :=
  subset_convexHull ℝ _ (by simp)

theorem yE (m : ℕ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (j : Fin m) :
    affinePolicy P q (Pi.single j 1) = fun i => P i j + q i := by
  funext i
  simp [affinePolicy]

theorem sfacts (m : ℕ) (hm1 : 1 ≤ m) :
    0 < 1 / Real.sqrt m ∧ 1 / Real.sqrt m ≤ 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hsq1 : 1 ≤ Real.sqrt m := by
    rw [Real.one_le_sqrt]; exact_mod_cast hm1
  exact ⟨by positivity, by rw [div_le_one hsq]; exact hsq1⟩

/-- At a unit vector: the diagonal entry of the policy is large, and every cost bound is ≥ 1. -/
theorem diag (m : ℕ) (hm1 : 1 ≤ m) (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ)
    (q : Fin m → ℝ) (t : ℝ)
    (hf : Feasible (A6 m) (B6 m) (U6 m) x (affinePolicy P q))
    (hc : CostLE (c6 m) (d6 m) (U6 m) x (affinePolicy P q) t) (j : Fin m) :
    1 - 1 / Real.sqrt m * t ≤ P j j + q j ∧ 1 ≤ t := by
  obtain ⟨hs0, hs1⟩ := sfacts m hm1
  set s := 1 / Real.sqrt m with hs
  have hF := hf.2 _ (memE m j)
  have hC := hc _ (memE m j)
  rw [yE, cost_eq] at hC
  rw [yE] at hF
  obtain ⟨hnn, hrow⟩ := hF
  have hr := hrow j
  simp only [A6, zero_mulVec, zero_add, Pi.single_eq_same] at hr
  rw [Bmul] at hr
  have hyj : 0 ≤ P j j + q j := hnn j
  have hle : P j j + q j ≤ ∑ i, (P i j + q i) :=
    Finset.single_le_sum (f := fun i => P i j + q i) (fun i _ => hnn i) (Finset.mem_univ j)
  constructor
  · nlinarith [mul_nonneg hs0.le hyj, mul_le_mul_of_nonneg_left hC hs0.le]
  · nlinarith [mul_le_mul_of_nonneg_left hle (by linarith : (0:ℝ) ≤ 1 - s)]

/-- The block point `b = s · 1_S`: a lower bound on any cost bound. -/
theorem block (m : ℕ) (hm1 : 1 ≤ m) (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ)
    (q : Fin m → ℝ) (t : ℝ)
    (hf : Feasible (A6 m) (B6 m) (U6 m) x (affinePolicy P q))
    (hc : CostLE (c6 m) (d6 m) (U6 m) x (affinePolicy P q) t)
    (p : Fin m → Prop) [DecidablePred p]
    (hb : (fun i => if p i then 1 / Real.sqrt m else 0) ∈ U6 m) :
    ((univ.filter p).card : ℝ) * (1 / Real.sqrt m) * (1 - 1 / Real.sqrt m * t)
      - ((1 / Real.sqrt m) * (univ.filter p).card - 1) * ∑ i ∈ univ.filter p, q i ≤ t := by
  obtain ⟨hs0, hs1⟩ := sfacts m hm1
  set s := 1 / Real.sqrt m with hs
  set S := univ.filter p with hS
  set b : Fin m → ℝ := fun i => if p i then s else 0 with hbdef
  have hyb : ∀ i, affinePolicy P q b i = s * ∑ j ∈ S, P i j + q i := by
    intro i
    simp only [affinePolicy, Pi.add_apply, mulVec, dotProduct, hbdef, mul_ite, mul_zero]
    rw [← Finset.sum_filter, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hq0 : 0 ≤ q := by
    have := (hf.2 0 (mem0 m)).1
    simpa [affinePolicy] using this
  -- per-row lower bound for i ∈ S
  have hrow : ∀ i ∈ S, s * (1 - s * t) - (s * S.card - 1) * q i ≤ affinePolicy P q b i := by
    intro i hi
    rw [hyb]
    have hPij : ∀ j, P i j = (P i j + q i) - q i := fun j => by ring
    have hsum : ∑ j ∈ S, P i j = ∑ j ∈ S, (P i j + q i) - S.card * q i := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
    have hnn : ∀ j, 0 ≤ P i j + q i := by
      intro j
      have := (hf.2 _ (memE m j)).1 i
      rw [yE] at this; exact this
    have hge : P i i + q i ≤ ∑ j ∈ S, (P i j + q i) :=
      Finset.single_le_sum (f := fun j => P i j + q i) (fun j _ => hnn j) hi
    have hd := (diag m hm1 x P q t hf hc i).1
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_left hge hs0.le, mul_le_mul_of_nonneg_left hd hs0.le]
  have hnnb : ∀ i, 0 ≤ affinePolicy P q b i := fun i => (hf.2 b hb).1 i
  have hcb := hc b hb
  rw [cost_eq] at hcb
  have hsub : ∑ i ∈ S, affinePolicy P q b i ≤ ∑ i, affinePolicy P q b i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hnnb i)
  have hlow : ∑ i ∈ S, (s * (1 - s * t) - (s * S.card - 1) * q i)
      ≤ ∑ i ∈ S, affinePolicy P q b i := Finset.sum_le_sum hrow
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hlow
  linarith

theorem card_low (m : ℕ) : ((univ.filter fun i : Fin m => (i : ℕ) < m / 2).card) = m / 2 := by
  rw [Fin.card_filter_val_lt]; omega

theorem card_high (m : ℕ) (hm : Even m) :
    ((univ.filter fun i : Fin m => m / 2 ≤ (i : ℕ)).card) = m / 2 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m))) (fun i : Fin m => (i : ℕ) < m / 2)
  rw [card_low, card_univ, Fintype.card_fin] at h
  have he : (univ.filter fun i : Fin m => ¬ (i : ℕ) < m / 2)
      = univ.filter fun i : Fin m => m / 2 ≤ (i : ℕ) :=
    Finset.filter_congr (fun i _ => not_lt)
  rw [he] at h
  obtain ⟨k, hk⟩ := hm
  omega

/-- Main lower bound: every affine cost bound `t` satisfies `√m ≤ t (2 + √m/2)`. -/
theorem lower (m : ℕ) (hm4 : 4 ≤ m) (hm_even : Even m) (x : Fin m → ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (t : ℝ)
    (hf : Feasible (A6 m) (B6 m) (U6 m) x (affinePolicy P q))
    (hc : CostLE (c6 m) (d6 m) (U6 m) x (affinePolicy P q) t) :
    Real.sqrt m ≤ t * (2 + Real.sqrt m / 2) := by
  have hm1 : 1 ≤ m := by omega
  have b1 := block m hm1 x P q t hf hc (fun i : Fin m => (i : ℕ) < m / 2) (memLow m)
  have b2 := block m hm1 x P q t hf hc (fun i : Fin m => m / 2 ≤ (i : ℕ)) (memHigh m)
  rw [card_low] at b1
  rw [card_high m hm_even] at b2
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin m))
    (fun i : Fin m => (i : ℕ) < m / 2) q
  have he : (univ.filter fun i : Fin m => ¬ (i : ℕ) < m / 2)
      = univ.filter fun i : Fin m => m / 2 ≤ (i : ℕ) :=
    Finset.filter_congr (fun i _ => not_lt)
  rw [he] at hsplit
  have hq0 : 0 ≤ q := by
    have := (hf.2 0 (mem0 m)).1
    simpa [affinePolicy] using this
  have hqs : ∑ i, q i ≤ t := by
    have := hc 0 (mem0 m)
    rw [cost_eq] at this
    simpa [affinePolicy] using this
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hmpos.le
  have hsq2 : 2 ≤ Real.sqrt m := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm4)
  obtain ⟨k, hk⟩ := hm_even
  have hk2 : m / 2 = k := by omega
  rw [hk2] at b1 b2 hsplit
  have hkR : (m : ℝ) = 2 * k := by rw [hk]; push_cast; ring
  set r := Real.sqrt m with hr
  set s := 1 / r with hs
  have hks : (k : ℝ) * s = r / 2 := by
    rw [hs]; field_simp; nlinarith
  have hkss : (k : ℝ) * s * s = 1 / 2 := by
    rw [hks, hs]; field_simp
  have hA : 0 ≤ s * k - 1 := by nlinarith
  have e1 : (k : ℝ) * s * (1 - s * t) = r / 2 - t / 2 := by
    rw [show (k : ℝ) * s * (1 - s * t) = k * s - (k * s * s) * t by ring, hkss, hks]; ring
  rw [e1] at b1 b2
  have hsum := congrArg (fun z => (s * k - 1) * z) hsplit
  simp only [mul_add] at hsum
  have := mul_le_mul_of_nonneg_left hqs hA
  have hsk : s * k = r / 2 := by rw [mul_comm]; exact hks
  rw [hsk] at this hsum b1 b2
  nlinarith

theorem zAdapt_le_one (m : ℕ) (hm1 : 1 ≤ m) :
    zAdapt (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) ≤ 1 := by
  obtain ⟨hs0, hs1⟩ := sfacts m hm1
  set s := 1 / Real.sqrt m with hs
  set K : Set (Fin m → ℝ) := {b | ∃ v : Fin m → ℝ, 0 ≤ v ∧ b ≤ B6 m *ᵥ v ∧ ∑ k, v k ≤ 1}
    with hK
  have hKc : Convex ℝ K := by
    intro b1 hb1 b2 hb2 a c ha hc hac
    obtain ⟨v1, h1, h1', h1''⟩ := hb1
    obtain ⟨v2, h2, h2', h2''⟩ := hb2
    refine ⟨a • v1 + c • v2, ?_, ?_, ?_⟩
    · intro k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact add_nonneg (mul_nonneg ha (h1 k)) (mul_nonneg hc (h2 k))
    · intro k
      rw [mulVec_add, mulVec_smul, mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left (h1' k) ha, mul_le_mul_of_nonneg_left (h2' k) hc]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left h1'' ha, mul_le_mul_of_nonneg_left h2'' hc]
  -- any point bounded by `s` componentwise lies in `K`, via a unit vector
  have i0 : Fin m := ⟨0, by omega⟩
  have hsmall : ∀ b : Fin m → ℝ, (∀ i, b i ≤ s) → b ∈ K := by
    intro b hb
    refine ⟨Pi.single i0 1, ?_, ?_, by simp⟩
    · intro k; by_cases h : k = i0 <;> simp [h]
    · intro i
      rw [Bmul]
      have h1 : ∑ k, (Pi.single i0 (1 : ℝ) : Fin m → ℝ) k = 1 := by simp
      rw [h1]
      have h2 : (0 : ℝ) ≤ (Pi.single i0 (1 : ℝ) : Fin m → ℝ) i := by
        by_cases h : i = i0 <;> simp [h]
      have := hb i
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) h2]
  have hsub : U6 m ⊆ K := by
    unfold U6
    apply convexHull_min _ hKc
    rintro b ((hb | ⟨j, rfl⟩) | hb)
    · rw [Set.mem_singleton_iff] at hb; subst hb
      exact ⟨0, le_refl _, by simp, by simp⟩
    · refine ⟨Pi.single j 1, ?_, ?_, by simp⟩
      · intro k; by_cases h : k = j <;> simp [h]
      · intro i
        rw [Bmul]
        by_cases h : i = j
        · subst h; simp
        · simp [h, hs0.le]
    · rcases hb with hb | hb <;> rw [hb] <;> apply hsmall <;> intro i
      · simp only [bLow]; split_ifs <;> linarith
      · simp only [bHigh]; split_ifs <;> linarith
  classical
  let y : (Fin m → ℝ) → Fin m → ℝ := fun b => if h : b ∈ K then h.choose else 0
  have hyK : ∀ b ∈ U6 m, 0 ≤ y b ∧ b ≤ B6 m *ᵥ y b ∧ ∑ k, y b k ≤ 1 := by
    intro b hb
    have hbK := hsub hb
    simp only [y, dif_pos hbK]
    exact hbK.choose_spec
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨x, y', hf, hc⟩
    have h1 := hc 0 (mem0 m)
    rw [cost_eq] at h1
    have h2 := (hf.2 0 (mem0 m)).1
    have : 0 ≤ ∑ i, y' 0 i := Finset.sum_nonneg (fun i _ => h2 i)
    linarith
  · refine ⟨0, y, ⟨le_refl _, fun b hb => ⟨(hyK b hb).1, ?_⟩⟩, fun b hb => ?_⟩
    · simp only [A6, zero_mulVec, zero_add]; exact (hyK b hb).2.1
    · rw [cost_eq]; exact (hyK b hb).2.2

theorem zAdapt_nonneg (m : ℕ) : 0 ≤ zAdapt (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) := by
  apply Real.sInf_nonneg
  rintro t ⟨x, y', hf, hc⟩
  have h1 := hc 0 (mem0 m)
  rw [cost_eq] at h1
  have h2 := (hf.2 0 (mem0 m)).1
  have : 0 ≤ ∑ i, y' 0 i := Finset.sum_nonneg (fun i _ => h2 i)
  linarith

theorem zAff_ne (m : ℕ) (hm1 : 1 ≤ m) :
    {t | ∃ (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ),
      Feasible (A6 m) (B6 m) (U6 m) x (affinePolicy P q) ∧
      CostLE (c6 m) (d6 m) (U6 m) x (affinePolicy P q) t}.Nonempty := by
  obtain ⟨hs0, hs1⟩ := sfacts m hm1
  set s := 1 / Real.sqrt m with hs
  have hbd : ∀ b ∈ U6 m, ∀ i, b i ≤ 1 := by
    have hconv : Convex ℝ {b : Fin m → ℝ | ∀ i, b i ≤ 1} := by
      intro b1 hb1 b2 hb2 a c ha hc hac i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hb1 i) ha, mul_le_mul_of_nonneg_left (hb2 i) hc]
    intro b hb
    unfold U6 at hb
    refine convexHull_min ?_ hconv hb
    rintro b ((hb | ⟨j, rfl⟩) | hb)
    · rw [Set.mem_singleton_iff] at hb; subst hb; intro i; simp
    · intro i; by_cases h : i = j
      · subst h; simp
      · simp [h]
    · rcases hb with hb | hb <;> rw [hb] <;> intro i
      · simp only [bLow]; split_ifs <;> linarith
      · simp only [bHigh]; split_ifs <;> linarith
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  refine ⟨(m : ℝ), 0, 0, fun _ => 1, ⟨le_refl _, fun b hb => ⟨?_, ?_⟩⟩, fun b hb => ?_⟩
  · intro i; simp [affinePolicy]
  · intro i
    simp only [A6, zero_mulVec, zero_add, affinePolicy, Pi.add_apply, Pi.zero_apply]
    rw [Bmul]
    simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have := hbd b hb i
    nlinarith [mul_nonneg hs0.le (by linarith : (0:ℝ) ≤ (m : ℝ) - 1)]
  · rw [cost_eq]
    simp [affinePolicy]

theorem main (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm_even : Even m) (hm : 200 / δ ^ 2 < (m : ℝ)) :
    (2 - δ) * zAdapt (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) <
      zAff (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) := by
  have hd2 : 0 < δ ^ 2 := by positivity
  have hmδ : 200 < (m : ℝ) * δ ^ 2 := by rwa [div_lt_iff₀ hd2] at hm
  have hmpos : (0 : ℝ) < m := by
    by_contra h; push Not at h; nlinarith
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hmpos
    · exact h
  have hA0 := zAdapt_nonneg m
  have hA1 := zAdapt_le_one m hm1
  have hAff1 : 1 ≤ zAff (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) := by
    apply le_csInf (zAff_ne m hm1)
    rintro t ⟨x, P, q, hf, hc⟩
    exact (diag m hm1 x P q t hf hc ⟨0, by omega⟩).2
  by_cases hδ2 : 2 ≤ δ
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ δ - 2) hA0]
  · push Not at hδ2
    have h50 : (50 : ℝ) < m := by nlinarith
    have hm4 : 4 ≤ m := by
      by_contra h; push Not at h
      have : (m : ℝ) ≤ 3 := by exact_mod_cast (by omega : m ≤ 3)
      linarith
    set r := Real.sqrt m with hr
    have hsq : 0 < r := Real.sqrt_pos.mpr hmpos
    have hss : r * r = m := Real.mul_self_sqrt hmpos.le
    have hδr : 8 < δ * r := by
      have h0 : 0 < δ * r := by positivity
      nlinarith
    have hlow : r / (2 + r / 2) ≤ zAff (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) := by
      apply le_csInf (zAff_ne m hm1)
      rintro t ⟨x, P, q, hf, hc⟩
      rw [div_le_iff₀ (by positivity)]
      exact lower m hm4 hm_even x P q t hf hc
    have hkey : 2 - δ < r / (2 + r / 2) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hA1 (by linarith : (0:ℝ) ≤ 2 - δ)]

end Pb100bbd9

open AffinePolicies.TwoGap in
theorem solution (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm_even : Even m) (hm : 200 / δ ^ 2 < (m : ℝ)) :
    (2 - δ) * AffinePolicies.Simplex.zAdapt (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) <
      AffinePolicies.Simplex.zAff (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) := by
  exact Pb100bbd9.main δ hδ m hm_even hm
