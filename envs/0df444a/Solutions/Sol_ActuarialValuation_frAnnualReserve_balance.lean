-- Prove2me | solution 1 for ActuarialValuation.frAnnualReserve_balance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:50.256982+00:00
-- url     : https://prove2.me/submissions/6242e30a-d181-4f54-b3e7-2fe22fc9a8b2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frAnnualReserve
open ActuarialValuation

theorem solution (assets premium benefit q growth : ℝ) (hq : 1-q ≠ 0) : frAnnualReserve assets premium benefit q growth * (1-q) + q*benefit = (assets+premium)*growth := by
  simp only [frAnnualReserve]
  grind
