-- Prove2me | solution 1 for ActuarialValuation.ctThieleRHS_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:13:38.024849+00:00
-- url     : https://prove2.me/submissions/e43a644b-9d7f-464f-9ad4-7f1652f19af3

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

theorem solution (q : Fin 3 → Fin 3 → ℝ) (b v : Fin 3 → ℝ) (i : Fin 3) : ctThieleRHS q 0 b v i = -b i-ctBackward q v i := by
  simp [ctThieleRHS]
