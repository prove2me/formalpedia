-- Prove2me | solution 1 for AggGameNet.Sync.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:47:12.474317+00:00
-- url     : https://prove2.me/submissions/d16bca74-f913-4671-901f-aaf51cbdaa33

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting
set_option autoImplicit false
open Filter

theorem solution {N n : ℕ} (hN : 0 < N)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ)
    (x v : ℕ → Fin N → AggGameNet.Sync.E n)
    (hcol : ∀ k i, ∑ j, W k j i = 1)
    (hinit : v 0 = x 0)
    (hrec : ∀ k i, v (k + 1) i = AggGameNet.Sync.vhat W v k i + x (k + 1) i - x k i) :
    ∀ k, AggGameNet.Sync.yavg v k = (1 / (N : ℝ)) • ∑ i, x k i := by
  intro k
  have key : ∀ k, ∑ i, v k i = ∑ i, x k i := by
    intro k
    induction k with
    | zero => rw [hinit]
    | succ k ih =>
      have hv : ∑ i, AggGameNet.Sync.vhat W v k i = ∑ i, v k i := by
        unfold AggGameNet.Sync.vhat
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_smul, hcol, one_smul]
      simp_rw [hrec k, Finset.sum_sub_distrib, Finset.sum_add_distrib, hv, ih]
      abel
  unfold AggGameNet.Sync.yavg
  rw [key k]
