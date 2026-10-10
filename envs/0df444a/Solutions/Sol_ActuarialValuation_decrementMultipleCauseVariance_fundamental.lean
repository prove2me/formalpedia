-- Prove2me | solution 1 for ActuarialValuation.decrementMultipleCauseVariance_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:10.425176+00:00
-- url     : https://prove2.me/submissions/139f738b-00c9-4a1f-9be6-330b31609ede

import Mathlib
import Definitions.Def_actuarial_decrementFiniteExposure
import Definitions.Def_actuarial_decrementAnnualRisk
import Definitions.Def_actuarial_decrementTailMass
import Definitions.Def_actuarial_decrementYearMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (n : ℕ)
  (hw : Summable (fun k : ℕ => decrementYearMass w k))
  (hn : ∀ k e, 0 ≤ w k e)
  (hS : ∀ t, 0 < decrementTailMass w t)
  (hTotal : (∑' k : ℕ, decrementYearMass w k) = 1) :
  (∑' k : ℕ, ∑ d : C, w k d * (decrementFiniteExposure w rho n k d) ^ 2) = ∑ t ∈ Finset.range n, decrementAnnualRisk w rho t := by
  classical
  let D : ℕ → ℝ := fun t => decrementYearMass w t
  let S : ℕ → ℝ := fun t => decrementTailMass w t
  let M : ℕ → ℝ := fun t => ∑ c : C, w t c * rho t c
  let q : ℕ → ℝ := fun t => M t / S t
  let B : ℕ → ℝ := fun t => ∑ j ∈ Finset.range t, q j
  let F : ℕ → ℕ → C → ℝ := decrementFiniteExposure w rho
  let g : ℕ → ℕ → ℝ := fun m k => ∑ d : C, w k d * (F m k d) ^ 2
  have hD (k : ℕ) : 0 ≤ D k := by dsimp [D, decrementYearMass]; exact Finset.sum_nonneg (fun d _ => hn k d)
  have htailSumm (t : ℕ) : Summable (fun k : ℕ => if t ≤ k then D k else 0) := by
    apply Summable.of_nonneg_of_le
    · intro k; split_ifs <;> first | exact hD k | exact le_refl 0
    · intro k; split_ifs <;> first | exact le_refl _ | exact hD k
    · exact hw
  have hsingle (t : ℕ) (a : ℝ) : Summable (fun k : ℕ => if k = t then a else 0) := by
    apply summable_of_finite_support; apply (Set.finite_singleton t).subset
    intro k hk; by_contra hkt; exact hk (if_neg hkt)
  have hSrec (t : ℕ) : S t = D t + S (t + 1) := by
    have hpoint (k : ℕ) : (if t ≤ k then D k else 0) = (if k = t then D t else 0) + (if t + 1 ≤ k then D k else 0) := by
      by_cases hk : k = t
      · subst k; simp
      · by_cases hle : t ≤ k
        · simp [hk, hle, show t + 1 ≤ k by omega]
        · simp [hk, hle, show ¬ t + 1 ≤ k by omega]
    have hfun : (fun k : ℕ => if t ≤ k then D k else 0) =
        (fun k : ℕ => (if k = t then D t else 0) +
          (if t + 1 ≤ k then D k else 0)) := funext hpoint
    change (∑' k : ℕ, if t ≤ k then D k else 0) =
      D t + (∑' k : ℕ, if t + 1 ≤ k then D k else 0)
    rw [hfun, (hsingle t (D t)).tsum_add (htailSumm (t + 1))]
    simp only [tsum_ite_eq]
  have hBrec (t : ℕ) : B (t + 1) = B t + q t := by simp [B, Finset.sum_range_succ]
  have hshock (t k : ℕ) (d : C) : (∑ c : C, rho t c * decrementCauseInnovation w t c k d) = (if k = t then rho t d else 0) - (if t ≤ k then q t else 0) := by
    have hevent : (∑ c : C, rho t c * (if k = t ∧ d = c then (1 : ℝ) else 0)) = if k = t then rho t d else 0 := by
      by_cases hk : k = t
      · subst k; simp
      · simp [hk]
    have hcorrect : (∑ c : C, rho t c * ((w t c / S t) * (if t ≤ k then (1 : ℝ) else 0))) = if t ≤ k then q t else 0 := by
      by_cases hle : t ≤ k
      · simp only [if_pos hle, mul_one]
        calc
          (∑ c : C, rho t c * (w t c / S t)) = ∑ c : C, (w t c * rho t c) / S t := by
              apply Finset.sum_congr rfl; intro c _; ring
          _ = (∑ c : C, w t c * rho t c) / S t := by rw [Finset.sum_div]
          _ = q t := rfl
      · simp [hle]
    unfold decrementCauseInnovation; simp_rw [mul_sub]; rw [Finset.sum_sub_distrib, hevent]
    have hcorrect' : (∑ c : C, rho t c * ((w t c / decrementTailMass w t) * (if t ≤ k then (1 : ℝ) else 0))) = if t ≤ k then q t else 0 := hcorrect
    rw [hcorrect']
  have hFpoint (m k : ℕ) (d : C) : F m k d = (if k < m then rho k d else 0) - (∑ t ∈ Finset.range m, if t ≤ k then q t else 0) := by
    dsimp [F, decrementFiniteExposure]; simp_rw [hshock]; rw [Finset.sum_sub_distrib]
    have hfirst : (∑ t ∈ Finset.range m, if k = t then rho t d else 0) = if k < m then rho k d else 0 := by
      by_cases hk : k < m <;> simp [hk, Finset.sum_ite_eq']
    rw [hfirst]
  have hFearly (m k : ℕ) (d : C) (hk : k < m) : F m k d = rho k d - B (k + 1) := by
    rw [hFpoint]; simp only [if_pos hk]
    have hfilter : (Finset.range m).filter (fun t => t ≤ k) = Finset.range (k + 1) := by ext t; simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]; omega
    rw [← Finset.sum_filter, hfilter]
  have hFlate (m k : ℕ) (d : C) (hk : m ≤ k) : F m k d = -(B m) := by
    rw [hFpoint]
    have hnot : ¬ k < m := by omega
    simp only [if_neg hnot, zero_sub]; congr 1
    dsimp [B]; apply Finset.sum_congr rfl
    intro t ht
    have hle : t ≤ k := by have ht' := Finset.mem_range.mp ht; omega
    simp [hle]
  have hgearly (m k : ℕ) (hk : k < m) : g m k = ∑ d : C, w k d * (rho k d - B (k + 1)) ^ 2 := by
    dsimp [g]; apply Finset.sum_congr rfl
    intro d _; rw [hFearly m k d hk]
  have hglate (m k : ℕ) (hk : m ≤ k) : g m k = D k * (B m) ^ 2 := by
    dsimp [g]
    calc
      (∑ d : C, w k d * F m k d ^ 2) = ∑ d : C, w k d * (B m) ^ 2 := by
            apply Finset.sum_congr rfl; intro d _; rw [hFlate m k d hk]; ring
      _ = D k * (B m) ^ 2 := by rw [← Finset.sum_mul]; rfl
  have hgsumm (m : ℕ) : Summable (g m) := by
    have hbase : Summable (fun k : ℕ => D k * (B m) ^ 2) := (show Summable D from (by simpa [D] using hw)).mul_right _
    have hdiff : Summable (fun k : ℕ => g m k - D k * (B m) ^ 2) := by
      apply summable_of_finite_support; apply (Finset.range m).finite_toSet.subset
      intro k hk; by_contra hkm
      have hmk : m ≤ k := by
        have hnk : ¬ k < m := by simpa using hkm
        omega
      apply hk; change g m k - D k * (B m) ^ 2 = 0
      rw [hglate m k hmk]; ring
    have hsum := hdiff.add hbase
    apply hsum.congr; intro k; ring
  have hvarformula (m : ℕ) : (∑' k : ℕ, g m k) = (∑ k ∈ Finset.range m, ∑ d : C, w k d * (rho k d - B (k + 1)) ^ 2) + S m * (B m) ^ 2 := by
    have hsplit := (hgsumm m).sum_add_tsum_compl (s := Finset.range m)
    have hcomplement : (∑' k : ℕ, if k ∈ Finset.range m then (0 : ℝ) else g m k) = S m * (B m) ^ 2 := by
      calc
        _ = ∑' k : ℕ, (if m ≤ k then D k else 0) * (B m) ^ 2 := by
              apply tsum_congr; intro k; by_cases hm : m ≤ k
              · simp [Finset.mem_range, not_lt.mpr hm, hm, hglate m k hm]
              · have hk : k < m := by omega
                simp [Finset.mem_range, hk, hm]
        _ = S m * (B m) ^ 2 := by rw [tsum_mul_right]; rfl
    have hprefix : (∑ k ∈ Finset.range m, g m k) = ∑ k ∈ Finset.range m, ∑ d : C, w k d * (rho k d - B (k + 1)) ^ 2 := by
      apply Finset.sum_congr rfl; intro k hk; exact hgearly m k (Finset.mem_range.mp hk)
    have hind (k : ℕ) :
        Set.indicator ((Finset.range m : Set ℕ)ᶜ) (g m) k =
          (if k ∈ Finset.range m then 0 else g m k) := by
      by_cases hk : k < m <;> simp [Set.indicator, Finset.mem_range, hk]
    rw [tsum_subtype] at hsplit
    simp_rw [hind] at hsplit; rw [hprefix, hcomplement] at hsplit; exact hsplit.symm
  have hannual (m : ℕ) : (∑ d : C, w m d * (rho m d - B (m + 1)) ^ 2) + S (m + 1) * B (m + 1) ^ 2 - S m * B m ^ 2 = decrementAnnualRisk w rho m := by
    have hSnz : decrementTailMass w m ≠ 0 := ne_of_gt (hS m)
    have hsq : (∑ d : C, w m d * (rho m d - B (m + 1)) ^ 2) = (∑ d : C, w m d * (rho m d) ^ 2) - 2 * B (m + 1) * M m + D m * B (m + 1) ^ 2 := by
      calc
        _ = ∑ d : C, (w m d * (rho m d) ^ 2 -
            2 * B (m+1) * (w m d * rho m d) + B (m+1)^2 * w m d) := by
              apply Finset.sum_congr rfl; intro d _; ring
        _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              dsimp [M, D, decrementYearMass]; ring
    have hs' : S (m + 1) = S m - D m := by linarith [hSrec m]
    rw [hsq, hBrec, hs']; unfold decrementAnnualRisk
    dsimp [q, M, D, S, decrementYearMass]; field_simp [hSnz]; ring
  have hfinite (m : ℕ) : (∑ k ∈ Finset.range m, ∑ d : C, w k d * (rho k d - B (k + 1)) ^ 2) + S m * (B m) ^ 2 = ∑ t ∈ Finset.range m, decrementAnnualRisk w rho t := by
    induction m with
    | zero => simp [B]
    | succ m ih =>
        simp only [Finset.sum_range_succ]
        calc
          (∑ k ∈ Finset.range m, ∑ d : C, w k d * (rho k d - B (k + 1)) ^ 2) + (∑ d : C, w m d * (rho m d - B (m + 1)) ^ 2) + S (m + 1) * B (m + 1) ^ 2 = ((∑ k ∈ Finset.range m, ∑ d : C, w k d * (rho k d - B (k + 1)) ^ 2) + S m * B m ^ 2) + ((∑ d : C, w m d * (rho m d - B (m + 1)) ^ 2) + S (m + 1) * B (m + 1) ^ 2 - S m * B m ^ 2) := by
                 ring
          _ = (∑ t ∈ Finset.range m, decrementAnnualRisk w rho t) + decrementAnnualRisk w rho m := by rw [ih, hannual m]
  calc
    (∑' k : ℕ, ∑ d : C, w k d * F n k d ^ 2) = (∑' k : ℕ, g n k) := rfl
    _ = (∑ k ∈ Finset.range n, ∑ d : C, w k d * (rho k d - B (k + 1)) ^ 2) + S n * B n ^ 2 := hvarformula n
    _ = ∑ t ∈ Finset.range n, decrementAnnualRisk w rho t := hfinite n
