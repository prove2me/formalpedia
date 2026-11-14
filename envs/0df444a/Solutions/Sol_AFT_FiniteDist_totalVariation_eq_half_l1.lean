-- Prove2me | solution 1 for AFT.FiniteDist.totalVariation_eq_half_l1
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:21:32.328922+00:00
-- url     : https://prove2.me/submissions/65f8d1e9-9681-4975-bb84-4be6e1792a0f

import Definitions.Def_InfoLossLAR_Native_AFT_TotalVariation
import Mathlib



/-! Exact finite total variation and contraction by a stochastic kernel. -/

namespace AFT
end AFT
section AFT
open AFT

open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]



namespace AFT.FiniteDist
end AFT.FiniteDist
section FiniteDist
open AFT
open AFT.FiniteDist



theorem _root_.AFT.FiniteDist.signedMass_difference (p q : FiniteDist α) :
    signedMass (fun a => p.weight a - q.weight a) = 0 := by
  simp [signedMass, Finset.sum_sub_distrib, p.sum_one, q.sum_one]



/-- Conventional half-`L¹` formula, proved from the normalized weights. -/
theorem solution (p q : FiniteDist α) :
    totalVariation p q = (∑ a, |p.weight a - q.weight a|) / 2 := by
  let weight := fun a => p.weight a - q.weight a
  have hmass : positiveMass weight = negativeMass weight := by
    have hz : signedMass weight = 0 := signedMass_difference p q
    simpa only [hz, zero_add] using positiveMass_eq weight
  have habs (a : α) : |weight a| = max (weight a) 0 + max (-weight a) 0 := by
    by_cases ha : 0 ≤ weight a
    · simp [abs_of_nonneg ha, max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
    · have ha' : weight a ≤ 0 := le_of_not_ge ha
      simp [abs_of_nonpos ha', max_eq_right ha', max_eq_left (neg_nonneg.mpr ha')]
  change positiveMass weight = (∑ a, |weight a|) / 2
  simp_rw [habs]
  rw [Finset.sum_add_distrib]
  change positiveMass weight = (positiveMass weight + negativeMass weight) / 2
  rw [← hmass]
  ring











end FiniteDist
end AFT
