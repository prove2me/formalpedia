-- Prove2me | Definitions.Def_SourceProof_e36e45a75f5c05df94c01778
-- name    : SourceProof_e36e45a75f5c05df94c01778
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:35.544721+00:00
-- url     : https://prove2.me/theorems/12a37242-49fb-4308-9643-0d4db2d76d04
-- title:
--   StochLean source theorem: ProbabilityTheory.CauchyUCP.exists_seq_ae_locallyUniform_cauchy

import Definitions.Def_StochLean_Probability_Process_UCP_Cauchy_F000
import Definitions.Def_SourceProof_90976d0ead60ac7e57a9b706

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP-Cauchy sequences and a common-event uniform Cauchy subsequence

The criterion uses the existing UCP strict-deviation events. The subsequence is
constructed by a summable-probability diagonal, without assuming measurable paths
or continuity of an outer measure on arbitrary decreasing sets.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

namespace CauchyUCP
theorem _root_.Prove2MeSourceProof.h_e36e45a75f5c05df94c01778 (hc : CauchyUCP P X) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      UniformCauchySeqOn (fun n t ↦ X (k n) t ω) atTop (Icc 0 T) := by
  classical
  let r : ℕ → ℝ≥0∞ := fun n ↦ (2⁻¹ : ℝ≥0∞) ^ n
  have hrpos : ∀ n, 0 < r n := fun n ↦ ENNReal.pow_pos (by simp) n
  have hrfin : (∑' n, r n) ≠ ∞ := by
    simpa only [r, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞)
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ, ∀ i m n, N i ≤ m → N i ≤ n →
      P {ω | ∃ t ≤ (i : ℝ≥0), (2⁻¹ : ℝ) ^ i < ‖X m t ω - X n t ω‖} ≤ r i := by
    choose N hN using fun i : ℕ ↦ hc i ((2⁻¹ : ℝ) ^ i) (by positivity) (r i) (hrpos i)
    exact ⟨N, hN⟩
  let k : ℕ → ℕ := fun n ↦ n + ∑ i ∈ Finset.range (n + 1), N i
  have hkN : ∀ n, N n ≤ k n := by
    intro n
    exact (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (N i))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))).trans (Nat.le_add_left _ _)
  have hk : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp only [k]
    rw [Finset.sum_range_succ (n := n + 1)]
    omega
  let A : ℕ → Set Ω := fun n ↦
    {ω | ∃ t ≤ (n : ℝ≥0), (2⁻¹ : ℝ) ^ n < ‖X (k n) t ω - X (k (n + 1)) t ω‖}
  have hA : ∀ n, P (A n) ≤ r n := fun n ↦
    hN n (k n) (k (n + 1)) (hkN n) ((hkN n).trans (hk.monotone (Nat.le_succ n)))
  have hsumA : (∑' n, P (A n)) ≠ ∞ :=
    ne_top_of_le_ne_top hrfin (ENNReal.tsum_le_tsum hA)
  refine ⟨k, hk, ?_⟩
  filter_upwards [ae_eventually_notMem hsumA] with ω hω
  intro T
  obtain ⟨NT, hNT⟩ := exists_nat_ge T
  apply _root_.Prove2MeSourceProof.h_90976d0ead60ac7e57a9b706
  filter_upwards [hω, eventually_ge_atTop NT] with n hn hNTn
  intro t ht
  have htn : t ≤ (n : ℝ≥0) := ht.2.trans (hNT.trans (by exact_mod_cast hNTn))
  have hbound : ‖X (k n) t ω - X (k (n + 1)) t ω‖ ≤ (2⁻¹ : ℝ) ^ n :=
    le_of_not_gt (fun h ↦ hn ⟨t, htn, h⟩)
  rw [edist_dist, dist_eq_norm_sub]
  convert ENNReal.ofReal_le_ofReal hbound using 1
  simp [ENNReal.ofReal_pow, ENNReal.inv_pow]
end CauchyUCP

end ProbabilityTheory


