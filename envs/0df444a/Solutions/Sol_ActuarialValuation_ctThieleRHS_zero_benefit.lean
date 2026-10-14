-- Prove2me | solution 1 for ActuarialValuation.ctThieleRHS_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:13:26.47536+00:00
-- url     : https://prove2.me/submissions/3f56b567-4e25-4b4f-bbac-eed5bcee3b6a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctBackward
import Definitions.Def_actuarial_ctThieleRHS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : Fin 3 → Fin 3 → ℝ) (δ : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) : ctThieleRHS q δ (fun _ => 0) v i = δ*v i-ctBackward q v i := by
  simp [ctThieleRHS]
