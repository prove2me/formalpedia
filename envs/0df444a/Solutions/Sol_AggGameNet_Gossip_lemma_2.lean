-- Prove2me | solution 1 for AggGameNet.Gossip.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:13:01.267337+00:00
-- url     : https://prove2.me/submissions/d0808d64-7288-45f1-b8cf-ab9f1d5bd3d0

import Mathlib
import Definitions.Def_AggGameNet_Gossip_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators
open AggGameNet.Gossip

theorem gg_colsum {N : ℕ} (a b j : Fin N) : ∑ i, gossipW a b i j = 1 := by
  unfold gossipW
  have h1 : ∑ i : Fin N, ((if i = a then (1:ℝ) else 0) - (if i = b then 1 else 0)) = 0 := by
    simp [Finset.sum_sub_distrib]
  have h2 : ∑ i : Fin N, (1 / 2 : ℝ) * ((if i = a then (1:ℝ) else 0) - (if i = b then 1 else 0)) *
      ((if j = a then (1:ℝ) else 0) - (if j = b then 1 else 0)) = 0 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, h1]; simp
  rw [Finset.sum_sub_distrib, h2]
  simp

theorem solution {N n : ℕ} (hN : 0 < N) {Ω : Type*}
    (I J : ℕ → Ω → Fin N)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (h0 : ∀ ω, v 0 ω = x 0 ω)
    (hrec : ∀ ω k i,
      v (k + 1) ω i = vhat I J v k ω i + x (k + 1) ω i - x k ω i) :
    ∀ ω k, yavg v k ω = (1 / (N : ℝ)) • ∑ i, x k ω i := by
  intro ω k
  have key : ∀ k, ∑ i, v k ω i = ∑ i, x k ω i := by
    intro k
    induction k with
    | zero => rw [h0 ω]
    | succ k ih =>
      have hv : ∑ i, vhat I J v k ω i = ∑ i, v k ω i := by
        unfold vhat
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_smul, gg_colsum, one_smul]
      simp_rw [hrec ω k, Finset.sum_sub_distrib, Finset.sum_add_distrib, hv, ih]
      abel
  unfold yavg
  rw [key k]
