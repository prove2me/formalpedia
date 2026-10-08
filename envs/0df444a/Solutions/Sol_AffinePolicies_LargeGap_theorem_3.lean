-- Prove2me | solution 1 for AffinePolicies.LargeGap.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T00:56:07.049572+00:00
-- url     : https://prove2.me/submissions/5984a656-acb8-4c64-a3b4-972e0244ee44

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

set_option autoImplicit false

namespace P5aaa8fc0

open Finset

/-- Double counting over all `n`-subsets: a lower bound `c` on every `n`-subset sum gives
`c * #t ≤ n * (sum over t)`. -/
theorem avg_le {α : Type*} [DecidableEq α] (t : Finset α) (n : ℕ) (hn1 : 1 ≤ n)
    (hnt : n ≤ t.card) (f : α → ℝ) (c : ℝ) (h : ∀ S ∈ t.powersetCard n, c ≤ ∑ j ∈ S, f j) :
    c * t.card ≤ n * ∑ j ∈ t, f j := by
  set P := t.powersetCard n with hP
  set M : ℕ := Nat.choose (t.card - 1) (n - 1) with hM
  have hcount : ∀ j ∈ t, (P.filter (fun S => j ∈ S)).card = M := by
    intro j hj
    have := card_filter_powersetCard_subset {j} t n (by simpa using hj) (by simpa using hn1)
    simpa [hP, Finset.singleton_subset_iff] using this
  have hdc : ∑ S ∈ P, ∑ j ∈ S, f j = (M : ℝ) * ∑ j ∈ t, f j := by
    have h1 : ∀ S ∈ P, ∑ j ∈ S, f j = ∑ j ∈ t, if j ∈ S then f j else 0 := by
      intro S hS
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [mem_filter]
      constructor
      · intro hj; exact ⟨(mem_powersetCard.1 hS).1 hj, hj⟩
      · intro hj; exact hj.2
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcount j hj]
  have hlow : (P.card : ℝ) * c ≤ ∑ S ∈ P, ∑ j ∈ S, f j := by
    have := Finset.sum_le_sum h
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  obtain ⟨a, ha⟩ : ∃ a, t.card = a + 1 := ⟨t.card - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hid : (t.card : ℝ) * (M : ℝ) = (P.card : ℝ) * n := by
    rw [hP, card_powersetCard, hM, ha, hk]
    simp only [Nat.add_sub_cancel]
    exact_mod_cast Nat.add_one_mul_choose_eq a k
  have hMpos : (0 : ℝ) < M := by
    rw [hM]; exact_mod_cast Nat.choose_pos (by omega)
  have key : (M : ℝ) * (c * t.card) ≤ (M : ℝ) * (n * ∑ j ∈ t, f j) := by
    calc (M : ℝ) * (c * t.card) = c * ((t.card : ℝ) * M) := by ring
      _ = n * ((P.card : ℝ) * c) := by rw [hid]; ring
      _ ≤ n * ∑ S ∈ P, ∑ j ∈ S, f j := mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = (M : ℝ) * (n * ∑ j ∈ t, f j) := by rw [hdc]; ring
  exact le_of_mul_le_mul_left key hMpos

open AffinePolicies.LargeGap AffinePolicies.Simplex Matrix

theorem Bmul (m : ℕ) (δ : ℝ) (v : Fin m → ℝ) (i : Fin m) :
    (B19 m δ *ᵥ v) i = theta0 m δ * ∑ k, v k + (1 - theta0 m δ) * v i := by
  simp only [B19, mulVec, dotProduct]
  have : ∀ k, (if i = k then (1 : ℝ) else theta0 m δ) * v k
      = theta0 m δ * v k + (if i = k then (1 - theta0 m δ) * v i else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib, Finset.sum_ite_eq,
    ← Finset.mul_sum]
  simp

theorem cost_eq (m : ℕ) (x : Fin m → ℝ) (v : Fin m → ℝ) :
    c19 m ⬝ᵥ x + d19 m ⬝ᵥ v = ∑ i, v i := by
  simp [c19, d19, dotProduct]

theorem mem0 (m : ℕ) (δ : ℝ) : (0 : Fin m → ℝ) ∈ U19 m δ :=
  subset_convexHull ℝ _ (by simp)

theorem memE (m : ℕ) (δ : ℝ) (j : Fin m) : (Pi.single j (1 : ℝ) : Fin m → ℝ) ∈ U19 m δ :=
  subset_convexHull ℝ _ (by simp)

theorem memC (m : ℕ) (δ : ℝ) : (fun _ => 1 / Real.sqrt m : Fin m → ℝ) ∈ U19 m δ :=
  subset_convexHull ℝ _ (by simp)

theorem memB (m : ℕ) (δ : ℝ) (S : Finset (Fin m)) (hS : S.card = rr m δ) :
    blockPt m δ S ∈ U19 m δ :=
  subset_convexHull ℝ _ ((Set.mem_union _ _ _).2 (Or.inr ⟨S, hS, rfl⟩))

/-- Numerical facts about the instance. -/
theorem nums (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) :
    2 ≤ m ∧ 14 < (m : ℝ) ^ (δ / 2) ∧
      (m : ℝ) ^ (δ / 2) * (m : ℝ) ^ (δ / 2) = (m : ℝ) ^ δ ∧
      theta0 m δ = (m : ℝ) ^ (δ / 2) / Real.sqrt m ∧
      (m : ℝ) ≤ (rr m δ : ℝ) * ((m : ℝ) ^ (δ / 2) * (m : ℝ) ^ (δ / 2)) ∧
      1 ≤ rr m δ ∧ rr m δ < m := by
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · rw [Nat.cast_zero, Real.zero_rpow hδ.ne'] at hm; linarith
      · rw [Nat.cast_one, Real.one_rpow] at hm; linarith
    · exact h
  have hmpos : (0 : ℝ) < m := by positivity
  set s := (m : ℝ) ^ (δ / 2) with hs
  have hs2 : s * s = (m : ℝ) ^ δ := by rw [hs, ← Real.rpow_add hmpos]; ring_nf
  have hspos : 0 < s := by positivity
  have hs14 : 14 < s := by nlinarith
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hth : theta0 m δ = s / Real.sqrt m := by
    have h1 : (m : ℝ) ^ ((1 - δ) / 2) * s = Real.sqrt m := by
      rw [hs, ← Real.rpow_add hmpos, Real.sqrt_eq_rpow]; ring_nf
    have h2 : (0 : ℝ) < (m : ℝ) ^ ((1 - δ) / 2) := by positivity
    unfold theta0
    rw [← h1]; field_simp
  have hpow : (m : ℝ) ^ (1 - δ) = m / (s * s) := by
    rw [hs2, Real.rpow_sub hmpos, Real.rpow_one]
  have hceil : (m : ℝ) ^ (1 - δ) ≤ (rr m δ : ℝ) := Nat.le_ceil _
  have hceil2 : (rr m δ : ℝ) < (m : ℝ) ^ (1 - δ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hpos1 : (0 : ℝ) < (m : ℝ) ^ (1 - δ) := by positivity
  refine ⟨hm2, hs14, hs2, hth, ?_, ?_, ?_⟩
  · rw [hpow] at hceil
    rw [div_le_iff₀ (by positivity)] at hceil
    linarith
  · have : (0 : ℝ) < rr m δ := lt_of_lt_of_le hpos1 hceil
    exact_mod_cast this
  · have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have : (m : ℝ) / (s * s) < m / 200 := by
      rw [hs2]; exact div_lt_div_of_pos_left hmpos (by norm_num) hm
    have : (rr m δ : ℝ) < m := by rw [hpow] at hceil2; linarith
    exact_mod_cast this

/-- Every feasible affine worst-case cost bound `t` satisfies `√m ≤ t (1 + 2 m^{δ/2})`. -/
theorem lower (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ)
    (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (t : ℝ)
    (hf : Feasible (A19 m) (B19 m δ) (U19 m δ) x (affinePolicy P q))
    (hc : CostLE (c19 m) (d19 m) (U19 m δ) x (affinePolicy P q) t) :
    Real.sqrt m ≤ t * (1 + 2 * (m : ℝ) ^ (δ / 2)) := by
  obtain ⟨hm2, hs14, hs2, hth, hrs, hr1, hrm⟩ := nums δ hδ m hm
  set s := (m : ℝ) ^ (δ / 2) with hs
  set sq := Real.sqrt m with hsqd
  set θ := theta0 m δ with hθd
  set r := rr m δ with hrd
  have hmpos : (0 : ℝ) < m := by positivity
  have hsq : 0 < sq := Real.sqrt_pos.mpr hmpos
  have hsqsq : sq * sq = m := Real.mul_self_sqrt hmpos.le
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hsq1 : 1 ≤ sq := by nlinarith
  have hθpos : 0 < θ := by rw [hth]; positivity
  set y := affinePolicy P q with hy
  -- values of the policy
  have hy0 : y 0 = q := by simp [hy, affinePolicy]
  have hyE : ∀ i k, y (Pi.single i 1) k = P k i + q k := by
    intro i k; simp [hy, affinePolicy, mulVec, dotProduct, Pi.single_apply]
  have hyB : ∀ (S : Finset (Fin m)) i, y (blockPt m δ S) i = ∑ j ∈ S, θ * P i j + q i := by
    intro S i
    simp only [hy, affinePolicy, mulVec, dotProduct, blockPt, Pi.add_apply, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hyC : ∀ i, y (fun _ => 1 / sq) i = (∑ j, P i j) * (1 / sq) + q i := by
    intro i; simp [hy, affinePolicy, mulVec, dotProduct, Finset.sum_mul]
  -- (i) q ≥ 0 and Σ q ≤ t
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i; have := (hf.2 0 (mem0 m δ)).1 i; rw [hy0] at this; simpa using this
  have hQ : ∑ i, q i ≤ t := by
    have := hc 0 (mem0 m δ); rw [cost_eq, hy0] at this; exact this
  -- (ii) diagonal
  have hdiag : ∀ i, 1 - θ * t ≤ P i i + q i := by
    intro i
    have h1 := (hf.2 _ (memE m δ i)).2 i
    have hnn := (hf.2 _ (memE m δ i)).1
    have hcost := hc _ (memE m δ i)
    rw [cost_eq] at hcost
    simp only [A19, zero_mulVec, Pi.add_apply, Pi.zero_apply, zero_add, Bmul,
      Pi.single_eq_same] at h1
    have hvi := hnn i
    simp only [Pi.zero_apply] at hvi
    rw [hyE] at h1 hvi
    nlinarith [mul_le_mul_of_nonneg_left hcost hθpos.le, mul_nonneg hθpos.le hvi]
  -- (iii) off-diagonal row sums
  have hoff : ∀ i, -(q i) * ((m : ℝ) - 1) ≤ r * (θ * ∑ j ∈ univ.erase i, P i j) := by
    intro i
    have hcard : (univ.erase i).card = m - 1 := by simp
    have hav := avg_le (univ.erase i) r hr1 (by rw [hcard]; omega) (fun j => θ * P i j) (-(q i))
      (by
        intro S hS
        rw [mem_powersetCard] at hS
        have := (hf.2 _ (memB m δ S hS.2)).1 i
        simp only [Pi.zero_apply] at this
        rw [hyB] at this
        linarith)
    rw [hcard, Nat.cast_sub (by omega), Nat.cast_one, ← Finset.mul_sum] at hav
    exact hav
  -- (iv) the center scenario
  have hcen : ∑ i, ((∑ j, P i j) * (1 / sq) + q i) ≤ t := by
    have := hc _ (memC m δ); rw [cost_eq, ← hsqd] at this
    simpa only [hyC] using this
  -- aggregate
  set D := ∑ i, P i i with hD
  set O := ∑ i, ∑ j ∈ univ.erase i, P i j with hO
  set Q := ∑ i, q i with hQd
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => hq0 i)
  have hrow : ∀ i, ∑ j, P i j = P i i + ∑ j ∈ univ.erase i, P i j := by
    intro i; rw [Finset.add_sum_erase _ _ (mem_univ i)]
  have hcen' : (D + O) * (1 / sq) + Q ≤ t := by
    have : ∑ i, ((∑ j, P i j) * (1 / sq) + q i) = (D + O) * (1 / sq) + Q := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [hrow, Finset.sum_add_distrib, hD, hO, hQd]
    linarith
  have hD' : (m : ℝ) * (1 - θ * t) ≤ D + Q := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => hdiag i)
    simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_add_distrib] at this
    linarith
  have hO' : -Q * ((m : ℝ) - 1) ≤ r * θ * O := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => hoff i)
    rw [← Finset.sum_mul, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
    linarith
  -- numerics
  have hθs : θ * sq = s := by rw [hth]; field_simp
  have hw : sq ≤ r * θ * s := by
    -- r s s ≥ m = sq sq, θ = s / sq
    have h1 : sq * sq ≤ (r : ℝ) * (s * s) := by rw [hsqsq]; exact hrs
    have h2 : r * θ * s * sq = (r : ℝ) * (s * s) := by
      rw [show r * θ * s * sq = (r : ℝ) * s * (θ * sq) by ring, hθs]; ring
    nlinarith
  have hspos : 0 < s := by linarith
  have hOb : -(Q * s * sq) ≤ O := by
    by_contra hneg
    push Not at hneg
    have hOneg : O < 0 := by nlinarith [mul_nonneg (mul_nonneg hQ0 hspos.le) hsq.le]
    -- r θ s O ≤ sq O
    have h1 : r * θ * s * O ≤ sq * O := mul_le_mul_of_nonpos_right hw hOneg.le
    have h2 : -Q * ((m : ℝ) - 1) * s ≤ r * θ * O * s := mul_le_mul_of_nonneg_right hO' hspos.le
    have h3 : -Q * (sq * sq) * s ≤ -Q * ((m : ℝ) - 1) * s := by
      rw [hsqsq]; nlinarith
    have h4 : sq * O < sq * (-(Q * s * sq)) := mul_lt_mul_of_pos_left hneg hsq
    nlinarith
  -- final: t ≥ sq - s t - Q s  and Q ≤ t
  have hmain : sq - s * t - Q * s ≤ t := by
    have e1 : (D + O) * (1 / sq) ≥ (m * (1 - θ * t) - Q - Q * s * sq) * (1 / sq) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e2 : (m * (1 - θ * t) - Q - Q * s * sq) * (1 / sq) = sq - s * t - Q / sq - Q * s := by
      rw [← hsqsq, ← hθs]; field_simp
    have e3 : Q / sq ≤ Q := div_le_self hQ0 hsq1
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hQ hspos.le]

theorem zAdapt_le_one (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) :
    zAdapt (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) ≤ 1 := by
  obtain ⟨hm2, hs14, hs2, hth, hrs, hr1, hrm⟩ := nums δ hδ m hm
  have hmpos : (0 : ℝ) < m := by positivity
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hsq1 : 1 ≤ Real.sqrt m := by rw [Real.one_le_sqrt]; exact hm1
  have hθ0 : 0 ≤ theta0 m δ := by rw [hth]; positivity
  have hθc : 1 / Real.sqrt m ≤ theta0 m δ := by
    rw [hth]; exact div_le_div_of_nonneg_right (by linarith) hsq.le
  set K : Set (Fin m → ℝ) := {b | ∃ v : Fin m → ℝ, 0 ≤ v ∧ b ≤ B19 m δ *ᵥ v ∧ ∑ k, v k ≤ 1}
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
  have hsub : U19 m δ ⊆ K := by
    unfold U19
    apply convexHull_min _ hKc
    rintro b (((hb | ⟨j, rfl⟩) | hb) | ⟨S, hS, rfl⟩)
    · rw [Set.mem_singleton_iff] at hb; subst hb
      exact ⟨0, le_refl _, by simp, by simp⟩
    · refine ⟨Pi.single j 1, ?_, ?_, by simp⟩
      · intro k; by_cases h : k = j <;> simp [h]
      · intro i
        rw [Bmul]
        by_cases h : i = j
        · subst h; simp
        · simp [h, hθ0]
    · rw [Set.mem_singleton_iff] at hb; subst hb
      refine ⟨fun _ => 1 / (m : ℝ), fun k => by simp, ?_, ?_⟩
      · intro i
        rw [Bmul]
        simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hw : (m : ℝ) * (1 / m) = 1 := by field_simp
        rw [hw]
        have hu : 1 / Real.sqrt m ≤ 1 := by rw [div_le_one hsq]; exact hsq1
        have hw1 : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one hmpos]; exact hm1
        have hw0 : 0 ≤ 1 / (m : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hθc (by linarith : (0:ℝ) ≤ 1 - 1 / (m : ℝ)),
          mul_nonneg hw0 (by linarith : (0:ℝ) ≤ 1 - 1 / Real.sqrt m)]
      · simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp; rfl
    · obtain ⟨i0, hi0⟩ : ∃ i0, i0 ∉ S := by
        by_contra h
        push Not at h
        have : S = univ := eq_univ_of_forall h
        rw [this, card_univ, Fintype.card_fin] at hS
        omega
      refine ⟨Pi.single i0 1, ?_, ?_, by simp⟩
      · intro k; by_cases h : k = i0 <;> simp [h]
      · intro i
        rw [Bmul]
        simp only [blockPt]
        by_cases h : i = i0
        · subst h; simp [hi0]
        · by_cases hiS : i ∈ S <;> simp [h, hiS, hθ0]
  classical
  let y : (Fin m → ℝ) → Fin m → ℝ := fun b => if h : b ∈ K then h.choose else 0
  have hyK : ∀ b ∈ U19 m δ, 0 ≤ y b ∧ b ≤ B19 m δ *ᵥ y b ∧ ∑ k, y b k ≤ 1 := by
    intro b hb
    have hbK := hsub hb
    simp only [y, dif_pos hbK]
    exact hbK.choose_spec
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨x, y', hf, hc⟩
    have h1 := hc 0 (mem0 m δ)
    rw [cost_eq] at h1
    have h2 := (hf.2 0 (mem0 m δ)).1
    have : 0 ≤ ∑ i, y' 0 i := Finset.sum_nonneg (fun i _ => h2 i)
    linarith
  · refine ⟨0, y, ⟨le_refl _, fun b hb => ⟨(hyK b hb).1, ?_⟩⟩, fun b hb => ?_⟩
    · simp only [A19, zero_mulVec, zero_add]; exact (hyK b hb).2.1
    · rw [cost_eq]; exact (hyK b hb).2.2

theorem zAff_ne (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) :
    {t | ∃ (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ),
      Feasible (A19 m) (B19 m δ) (U19 m δ) x (affinePolicy P q) ∧
      CostLE (c19 m) (d19 m) (U19 m δ) x (affinePolicy P q) t}.Nonempty := by
  obtain ⟨hm2, hs14, hs2, hth, hrs, hr1, hrm⟩ := nums δ hδ m hm
  have hmpos : (0 : ℝ) < m := by positivity
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hsq1 : 1 ≤ Real.sqrt m := by rw [Real.one_le_sqrt]; exact hm1
  have hθ0 : 0 ≤ theta0 m δ := by rw [hth]; positivity
  set C := 1 + theta0 m δ with hC
  have hbd : ∀ b ∈ U19 m δ, ∀ i, b i ≤ C := by
    have hconv : Convex ℝ {b : Fin m → ℝ | ∀ i, b i ≤ C} := by
      intro b1 hb1 b2 hb2 a c ha hc hac i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hb1 i) ha, mul_le_mul_of_nonneg_left (hb2 i) hc]
    intro b hb
    unfold U19 at hb
    refine convexHull_min ?_ hconv hb
    rintro b (((hb | ⟨j, rfl⟩) | hb) | ⟨S, hS, rfl⟩)
    · rw [Set.mem_singleton_iff] at hb; subst hb; intro i; simp; linarith
    · intro i; by_cases h : i = j
      · subst h; simp; linarith
      · simp [h]; linarith
    · rw [Set.mem_singleton_iff] at hb; subst hb; intro i
      have hu : 1 / Real.sqrt m ≤ 1 := by rw [div_le_one hsq]; exact hsq1
      simp only; linarith
    · intro i; simp only [blockPt]; split_ifs <;> linarith
  refine ⟨(m : ℝ) * C, 0, 0, fun _ => C, ⟨le_refl _, fun b hb => ⟨?_, ?_⟩⟩, fun b hb => ?_⟩
  · intro i; simp [affinePolicy]; linarith
  · intro i
    simp only [A19, zero_mulVec, zero_add, affinePolicy, Pi.add_apply, Pi.zero_apply]
    rw [Bmul]
    simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have := hbd b hb i
    nlinarith [mul_nonneg hθ0 (by linarith : (0:ℝ) ≤ (m : ℝ) - 1)]
  · rw [cost_eq]
    simp [affinePolicy]

theorem main (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) :
    (m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4 * zAdapt (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) <
      zAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) := by
  obtain ⟨hm2, hs14, hs2, hth, hrs, hr1, hrm⟩ := nums δ hδ m hm
  set s := (m : ℝ) ^ (δ / 2) with hs
  have hmpos : (0 : ℝ) < m := by positivity
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hspos : 0 < s := by linarith
  have hlow : Real.sqrt m / (1 + 2 * s) ≤ zAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) := by
    apply le_csInf (zAff_ne δ hδ m hm)
    rintro t ⟨x, P, q, hf, hc⟩
    rw [div_le_iff₀ (by positivity)]
    exact lower δ hδ m hm x P q t hf hc
  have hR : (m : ℝ) ^ ((1 : ℝ) / 2 - δ) = Real.sqrt m / (s * s) := by
    rw [hs2, Real.sqrt_eq_rpow, Real.rpow_sub hmpos]
  have hK0 : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4 := by positivity
  have h1 : (m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4 * zAdapt (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ)
      ≤ (m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4 := by
    have := mul_le_mul_of_nonneg_left (zAdapt_le_one δ hδ m hm) hK0
    linarith
  have h2 : (m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4 < Real.sqrt m / (1 + 2 * s) := by
    rw [hR, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    have : 1 + 2 * s < s * s * 4 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left this hsq]
  linarith

end P5aaa8fc0

open AffinePolicies.LargeGap in
theorem solution (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ) :
    (m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4 * AffinePolicies.Simplex.zAdapt (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) <
      AffinePolicies.Simplex.zAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) := by
  exact P5aaa8fc0.main δ hδ m hm
