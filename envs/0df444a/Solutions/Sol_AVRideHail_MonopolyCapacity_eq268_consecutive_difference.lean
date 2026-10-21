-- Prove2me | solution 1 for AVRideHail.MonopolyCapacity.eq268_consecutive_difference
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:15:50.270957+00:00
-- url     : https://prove2.me/submissions/c528f5fe-cdb0-44b7-8a7d-2fe4b8752e3e

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model
set_option autoImplicit false
open AVRideHail.MonopolyCapacity

theorem solution (P : AVRideHail.PureHV.MarketParams) (cv cf : ℝ) (I : ℕ)
    (prob : Fin I → ℝ) (ns : Fin I → ℝ) (hns : StrictMono ns) (k k' : Fin I)
    (hkk' : k'.val = k.val + 1) :
    profit20 P cv cf prob ns (ns k') - profit20 P cv cf prob ns (ns k) =
      ((∑ j ∈ Finset.Ici k', prob j) * (P.w0 - cv) - cf) * (ns k' - ns k) := by
  unfold profit20
  have hlt : ns k < ns k' := hns (by rw [Fin.lt_def]; omega)
  have hpt : ∀ i, prob i * min (ns k') (ns i) - prob i * min (ns k) (ns i) =
      if k' ≤ i then prob i * (ns k' - ns k) else 0 := by
    intro i
    split_ifs with h
    · have h1 : ns k' ≤ ns i := hns.monotone h
      rw [min_eq_left h1, min_eq_left (le_trans hlt.le h1)]
      ring
    · have h2 : i ≤ k := by
        rw [Fin.le_def]
        have : ¬ k'.val ≤ i.val := fun hh => h (Fin.le_def.mpr hh)
        omega
      have h3 : ns i ≤ ns k := hns.monotone h2
      rw [min_eq_right (le_trans h3 hlt.le), min_eq_right h3]
      ring
  have key : ∑ i, prob i * min (ns k') (ns i) - ∑ i, prob i * min (ns k) (ns i) =
      (∑ j ∈ Finset.Ici k', prob j) * (ns k' - ns k) := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [← Finset.sum_filter, Finset.sum_mul]
    have : Finset.filter (fun i => k' ≤ i) Finset.univ = Finset.Ici k' := by
      ext i; simp
    rw [this]
  have e : (P.w0 - cv) * ∑ i, prob i * min (ns k') (ns i) - cf * ns k' -
      ((P.w0 - cv) * ∑ i, prob i * min (ns k) (ns i) - cf * ns k) =
      (P.w0 - cv) * (∑ i, prob i * min (ns k') (ns i) - ∑ i, prob i * min (ns k) (ns i)) -
        cf * (ns k' - ns k) := by ring
  rw [e, key]
  ring
