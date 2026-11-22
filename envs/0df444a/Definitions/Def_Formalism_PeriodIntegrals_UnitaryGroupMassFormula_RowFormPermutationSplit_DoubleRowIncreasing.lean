-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_DoubleRowIncreasing
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_DoubleRowIncreasing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:47:44.535981+00:00
-- url     : https://prove2.me/theorems/6f54959f-88cb-42b6-8cbe-a4e726f0d6b1
-- title:
--   Double Row Increasing
-- statement:
--   Definitions and structural lemmas for Double Row Increasing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowFormPermutationSplit/DoubleRowIncreasing.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.QmRowForm
def opE {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Fin n → Fin n → Aᵐᵒᵖ :=
  fun a b => MulOpposite.op (E b a)
def revConj (t : ℕ) : Equiv.Perm (Fin t) ≃ Equiv.Perm (Fin t) where
  toFun τ := Fin.revPerm * τ * Fin.revPerm
  invFun τ := Fin.revPerm * τ * Fin.revPerm
  left_inv τ := by ext k; simp
  right_inv τ := by ext k; simp
end PI.UnitaryGroupMassFormula.QmRowForm


