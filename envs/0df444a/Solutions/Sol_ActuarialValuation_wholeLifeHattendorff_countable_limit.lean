-- Prove2me | solution 1 for ActuarialValuation.wholeLifeHattendorff_countable_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:59:16.96468+00:00
-- url     : https://prove2.me/submissions/ab640cfe-5c10-4712-bc53-38299f707e56

import Mathlib
import Definitions.Def_actuarial_wholeLifeCompleteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass
import Theorems.Thm_ActuarialValuation_wholeLifeTailMass_zero
import Theorems.Thm_ActuarialValuation_wholeLifeTailMass_succ_helperXXIII
import Theorems.Thm_ActuarialValuation_wholeLifeHattendorff_prefixMomentsXXIII
import Theorems.Thm_ActuarialValuation_wholeLifeHattendorff_summableMomentsXXIII
import Theorems.Thm_ActuarialValuation_wholeLifeHattendorff_finiteTailEnergyXXIII
import Theorems.Thm_ActuarialValuation_hattendorffEnergy_boundary_tendstoXXIII
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
theorem solution (w rho : ℕ → ℝ)
  (hw : Summable w) (hNonneg : ∀ k, 0 ≤ w k)
  (hTotal : (∑' k : ℕ, w k) = 1)
  (hS : ∀ t, 0 < wholeLifeTailMass w t)
  (hVar : Summable (fun t : ℕ =>
    (rho t) ^ 2 * w t *
      (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t))) :
  (∑' k : ℕ, w k * wholeLifeCompleteInnovation w rho k) = 0 ∧
  (∑' k : ℕ, w k * (wholeLifeCompleteInnovation w rho k) ^ 2) =
    ∑' t : ℕ, (rho t) ^ 2 * w t *
      (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t) := by
  classical
  let S (t : ℕ) : ℝ := wholeLifeTailMass w t
  let A (n : ℕ) : ℝ := -(∑ t ∈ Finset.range n, rho t * (w t / S t))
  let a (t : ℕ) : ℝ := rho t ^ 2 * w t * (S (t + 1) / S t)
  have htail (t : ℕ) : S t = w t + S (t + 1) :=
    wholeLifeTailMass_succ_helperXXIII w t hw
  have hmass (n : ℕ) : (∑ k ∈ Finset.range n, w k) + S n = 1 := by
    induction n with
    | zero =>
      simpa [S] using wholeLifeTailMass_zero w hTotal
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [htail n]
  have hStendsto : Filter.Tendsto S Filter.atTop (nhds 0) := by
    have hsum : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, w k) Filter.atTop (nhds (1 : ℝ)) := by
      simpa only [hTotal] using hw.tendsto_sum_tsum_nat
    have hc : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) := tendsto_const_nhds
    have hzero' : Filter.Tendsto (fun n : ℕ => 1 - ∑ k ∈ Finset.range n, w k) Filter.atTop (nhds (0 : ℝ)) := by
      simpa using (hc.sub hsum)
    have hident : S = fun n : ℕ => 1 - ∑ k ∈ Finset.range n, w k := by
      funext n
      linarith [hmass n]
    rw [hident]
    exact hzero'
  have han : ∀ n, 0 ≤ a n := by
    intro n
    dsimp [a, S]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hNonneg n))
      (div_nonneg (le_of_lt (hS (n + 1))) (le_of_lt (hS n)))
  have hpref (n : ℕ) :
      (∑ k ∈ Finset.range n, w k * wholeLifeCompleteInnovation w rho k) =
        -(S n * A n) ∧
      (∑ k ∈ Finset.range n,
        w k * wholeLifeCompleteInnovation w rho k ^ 2) =
        (∑ t ∈ Finset.range n, a t) - S n * A n ^ 2 := by
    simpa only [S, A, a] using
      (wholeLifeHattendorff_prefixMomentsXXIII w rho hw hS n)
  have hsums : Summable (fun k : ℕ => w k * wholeLifeCompleteInnovation w rho k) ∧
    Summable (fun k : ℕ => w k * wholeLifeCompleteInnovation w rho k ^ 2) := by
    apply wholeLifeHattendorff_summableMomentsXXIII w rho hw
      hNonneg hTotal hS hVar
    intro n
    exact (hpref n).2
  have hdiff (T N : ℕ) (hTN : T ≤ N) :
      A N - A T = -(∑ t ∈ Finset.Ico T N,
        rho t * (w t / S t)) := by
    dsimp [A]
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun t : ℕ => rho t * (w t / S t)) hTN
    rw [← hsplit]
    ring
  have henergy (T N : ℕ) (hTN : T ≤ N) :
      S N * (A N - A T) ^ 2 ≤ ∑ t ∈ Finset.Ico T N, a t := by
    rw [hdiff T N hTN]
    have he := wholeLifeHattendorff_finiteTailEnergyXXIII
      w rho T N hTN hNonneg hS
      (by intro t; exact htail t)
    simpa only [S, a, neg_sq] using he
  have hboundary : Filter.Tendsto (fun n => S n * A n ^ 2) Filter.atTop (nhds 0) :=
    hattendorffEnergy_boundary_tendstoXXIII S A a
      (by intro n; exact hS n) hStendsto hVar han henergy
  have habs (n : ℕ) : |S n * A n| ≤ (S n + S n * A n ^ 2) / 2 := by
    have hs : 0 ≤ S n := le_of_lt (hS n)
    have hh := mul_nonneg hs (sq_nonneg (|A n| - 1))
    have heq : |S n * A n| = S n * |A n| := by
      rw [abs_mul, abs_of_nonneg hs]
    rw [heq]
    nlinarith [sq_abs (A n)]
  have habslim : Filter.Tendsto (fun n => |S n * A n|) Filter.atTop (nhds 0) := by
    have hh : Filter.Tendsto (fun n => (S n + S n * A n ^ 2) / 2) Filter.atTop (nhds 0) := by
      convert (hStendsto.add hboundary).div_const 2 using 1 <;> ring
    exact squeeze_zero (fun n => abs_nonneg _) habs hh
  have hmeanlim : Filter.Tendsto (fun n => S n * A n) Filter.atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2
      (by simpa only [Real.norm_eq_abs] using habslim)
  have hp : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, w k * wholeLifeCompleteInnovation w rho k)
      Filter.atTop (nhds 0) := by
    simpa only [show ∀ n, (∑ k ∈ Finset.range n,
      w k * wholeLifeCompleteInnovation w rho k) = -(S n * A n)
        from fun n => (hpref n).1, neg_zero] using hmeanlim.neg
  have hq : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, w k * wholeLifeCompleteInnovation w rho k ^ 2)
      Filter.atTop (nhds (∑' t : ℕ, a t)) := by
    have ht := hVar.tendsto_sum_tsum_nat.sub hboundary
    simpa only [show ∀ n, (∑ k ∈ Finset.range n,
      w k * wholeLifeCompleteInnovation w rho k ^ 2) =
      (∑ t ∈ Finset.range n, a t) - S n * A n ^ 2
        from fun n => (hpref n).2, sub_zero] using ht
  constructor
  · exact tendsto_nhds_unique hsums.1.tendsto_sum_tsum_nat hp
  · simpa [a, S] using (tendsto_nhds_unique
      hsums.2.tendsto_sum_tsum_nat hq)
