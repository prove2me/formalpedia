-- Prove2me | solution 1 for APFFinitePairing.singleton_form
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-02T09:21:42.116002+00:00
-- url     : https://prove2.me/submissions/99fa6e35-a715-4658-ada6-425acd774539

import Definitions.Def_APFFinitePairing_form
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open APFFinitePairing
variable {I J : Type*} [Fintype I] [Fintype J]
theorem solution (c : ℝ) :
    form (fun (_ : Fin 1) (_ : Fin 1) => c) (fun _ => 1) (fun _ => 1) = c := by
  simp [form]
