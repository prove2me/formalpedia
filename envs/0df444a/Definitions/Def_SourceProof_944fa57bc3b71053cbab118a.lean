-- Prove2me | Definitions.Def_SourceProof_944fa57bc3b71053cbab118a
-- name    : SourceProof_944fa57bc3b71053cbab118a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:16.889857+00:00
-- url     : https://prove2.me/theorems/25ce8176-5edf-461d-a486-ff5be3353c45
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.exists_seq_ae_locallyUniform

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_cc9d1824ad64b2323f63380a

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform convergence on compact time intervals in probability

The compact deviation has an extended nonnegative value, so it never uses a
default real supremum of an unbounded set. Its equality with a countable dense
supremum is proved on right-continuous paths. Measurability is then a theorem,
not an assumption hidden in the definition of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP

theorem _root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a {X : ℕ → ℝ≥0 → Ω → ℝ}
    (hX : TendstoUCP P X atTop Y) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        Tendsto (fun n ↦ compactDeviation (X (k n)) Y T ω) atTop (𝓝 0) := by
  classical
  let r : ℕ → ℝ≥0∞ := fun n ↦ (2⁻¹ : ℝ≥0∞) ^ n
  have hrpos : ∀ n, 0 < r n := fun n ↦ ENNReal.pow_pos (by simp) n
  have hrfin : (∑' n, r n) ≠ ∞ := by
    simpa only [r, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞)
  have hthreshold : ∀ n : ℕ, ∃ N : ℕ, ∀ j ≥ N,
      P {ω | r n ≤ ProbabilityTheory.compactDeviation (X j) Y n ω} ≤ r n := by
    intro n
    exact ENNReal.tendsto_atTop_zero.mp (hX n (r n) (hrpos n)) (r n) (hrpos n)
  choose N hN using hthreshold
  let k : ℕ → ℕ := fun n ↦ n + ∑ i ∈ Finset.range (n + 1), N i
  have hkN : ∀ n, N n ≤ k n := by
    intro n
    have hsum : N n ≤ ∑ i ∈ Finset.range (n + 1), N i :=
      Finset.single_le_sum (fun i _ ↦ Nat.zero_le (N i)) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    exact hsum.trans (Nat.le_add_left _ _)
  have hk : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp only [k]
    rw [Finset.sum_range_succ (n := n + 1)]
    omega
  let A : ℕ → Set Ω := fun n ↦ {ω | r n ≤ ProbabilityTheory.compactDeviation (X (k n)) Y n ω}
  have hA : ∀ n, P (A n) ≤ r n := fun n ↦ hN n (k n) (hkN n)
  have hsumA : (∑' n, P (A n)) ≠ ∞ :=
    ne_top_of_le_ne_top hrfin (ENNReal.tsum_le_tsum hA)
  refine ⟨k, hk, ?_⟩
  filter_upwards [ae_eventually_notMem hsumA] with ω hω
  intro T
  obtain ⟨NT, hNT⟩ := exists_nat_ge T
  obtain ⟨NA, hNA⟩ := eventually_atTop.mp hω
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε hε
  obtain ⟨NE, hNE⟩ := ENNReal.tendsto_atTop_zero.mp
    (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hrfin) ε hε
  refine ⟨max NT (max NA NE), fun n hn ↦ ?_⟩
  have hTn : T ≤ (n : ℝ≥0) := hNT.trans (by
    exact_mod_cast (le_max_left NT (max NA NE)).trans hn)
  have hAn : ProbabilityTheory.compactDeviation (X (k n)) Y n ω < r n :=
    lt_of_not_ge (hNA n ((le_max_left NA NE).trans ((le_max_right NT (max NA NE)).trans hn)))
  exact (_root_.Prove2MeSourceProof.h_cc9d1824ad64b2323f63380a hTn ω).trans (hAn.le.trans
    (hNE n ((le_max_right NA NE).trans ((le_max_right NT (max NA NE)).trans hn))))
end TendstoUCP

end ProbabilityTheory


