-- Prove2me | solution 1 for ActuarialValuation.xlFiniteOptimalRetentionLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:20:18.738697+00:00
-- url     : https://prove2.me/submissions/9627a5e3-2d98-48cc-bb81-9819b5d87e06

import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_actuarial_xlFiniteOptimalRetentionCost
import Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω A : Type*} [Fintype Ω] [Fintype A] [Nonempty A] (w z : Ω → ℝ) (retention : A → ℝ) (θ kap : ℝ) (a : A)
  :
  xlFiniteOptimalRetentionCost w z retention θ kap ≤
    xlRiskAdjustedRetentionCost w z θ kap (retention a) := by
  classical
  unfold xlFiniteOptimalRetentionCost
  exact Finset.inf'_le
      (fun x : A => xlRiskAdjustedRetentionCost w z θ kap (retention x))
      (Finset.mem_univ a)
