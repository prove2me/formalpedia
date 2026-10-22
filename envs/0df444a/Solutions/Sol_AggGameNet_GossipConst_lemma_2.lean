-- Prove2me | solution 1 for AggGameNet.GossipConst.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:46:39.93944+00:00
-- url     : https://prove2.me/submissions/ff5fee76-d3e6-4973-b5b8-c4435dee7f01

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Gossip
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators

theorem kk_colsum {N : ℕ} (a b j : Fin N) : ∑ i, AggGameNet.Gossip.gossipW a b i j = 1 := by
  unfold AggGameNet.Gossip.gossipW
  have h1 : ∑ i : Fin N, ((if i = a then (1:ℝ) else 0) - (if i = b then 1 else 0)) = 0 := by
    simp [Finset.sum_sub_distrib]
  have h2 : ∑ i : Fin N, (1 / 2 : ℝ) * ((if i = a then (1:ℝ) else 0) - (if i = b then 1 else 0)) *
      ((if j = a then (1:ℝ) else 0) - (if j = b then 1 else 0)) = 0 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, h1]; simp
  rw [Finset.sum_sub_distrib, h2]
  simp

theorem solution {N n : ℕ} (hN : 0 < N) {Ω : Type*}
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (I J : ℕ → Ω → Fin N) (alpha : Fin N → ℝ)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (hrun : AggGameNet.GossipConst.IsGossipRun K F I J alpha x v) :
    ∀ k ω, AggGameNet.Gossip.yavg v k ω = (1 / (N : ℝ)) • ∑ i, x k ω i := by
  intro k ω
  obtain ⟨x₀, -, h0, hstep⟩ := hrun
  have hrec : ∀ k i, v (k + 1) ω i = AggGameNet.Gossip.vhat I J v k ω i + x (k + 1) ω i - x k ω i :=
    fun k i => (hstep ω k i).2.2
  have key : ∀ k, ∑ i, v k ω i = ∑ i, x k ω i := by
    intro k
    induction k with
    | zero => rw [(h0 ω).1, (h0 ω).2]
    | succ k ih =>
      have hv : ∑ i, AggGameNet.Gossip.vhat I J v k ω i = ∑ i, v k ω i := by
        unfold AggGameNet.Gossip.vhat
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_smul, kk_colsum, one_smul]
      simp_rw [hrec k, Finset.sum_sub_distrib, Finset.sum_add_distrib, hv, ih]
      abel
  unfold AggGameNet.Gossip.yavg
  rw [key k]
