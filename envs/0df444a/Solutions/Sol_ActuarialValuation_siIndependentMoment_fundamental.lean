-- Prove2me | solution 1 for ActuarialValuation.siIndependentMoment_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:17:05.529008+00:00
-- url     : https://prove2.me/submissions/f5ad7d3b-b140-4d6b-b04e-4133a5e84137

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrossMean
import Definitions.Def_actuarial_siGrossSecond
import Definitions.Def_actuarial_siIndependentTwoMean
import Definitions.Def_actuarial_siIndependentTwoSecond

import Theorems.Thm_ActuarialValuation_siIndependentTwoMean_factor
import Theorems.Thm_ActuarialValuation_siIndependentTwoSecond_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) (r : Fin m → ℝ) (s : Fin n → ℝ) : siIndependentTwoMean p q r s=siGrossMean p r*siGrossMean q s ∧ siIndependentTwoSecond p q r s=siGrossSecond p r*siGrossSecond q s := by
  exact ⟨siIndependentTwoMean_factor p q r s,
    siIndependentTwoSecond_factor p q r s⟩
