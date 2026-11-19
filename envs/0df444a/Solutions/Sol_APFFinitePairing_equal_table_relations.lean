-- Prove2me | solution 1 for APFFinitePairing.equal_table_relations
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-02T11:49:18.520987+00:00
-- url     : https://prove2.me/submissions/b83cb824-ea2b-4465-bccb-3e83bb537d09

import Definitions.Def_APFFinitePairing_LeftRad
import Definitions.Def_APFFinitePairing_RightRad
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open APFFinitePairing
variable {I J : Type*} [Fintype I] [Fintype J]
theorem solution (M N : I → J → ℝ) (h : M=N) :
    LeftRad M = LeftRad N ∧ RightRad M = RightRad N := by subst N; exact ⟨rfl,rfl⟩
