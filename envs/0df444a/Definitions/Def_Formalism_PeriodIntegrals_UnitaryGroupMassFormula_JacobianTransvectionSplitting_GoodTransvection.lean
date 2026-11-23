-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:10.429726+00:00
-- url     : https://prove2.me/theorems/f61be152-dd8c-47ed-9d43-1b16e077cd22
-- title:
--   Good Transvection
-- statement:
--   Definitions and structural lemmas for Good Transvection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/GoodTransvection.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
namespace PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
def phiM (M : Matrix ι ι F) (hM : IsUnit M.det) : (ι → F) ≃ₜ+ (ι → F) where
  toFun x := M *ᵥ x
  invFun x := M⁻¹ *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM]
  right_inv x := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM]
  map_add' x y := Matrix.mulVec_add M x y
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id
def chiM (M : Matrix ι ι F) (hM : IsUnit M.det) : ℝ≥0 :=
  letI := borel (ι → F)
  haveI : BorelSpace (ι → F) := ⟨rfl⟩
  addEquivAddHaarChar (phiM M hM)
def Good (M : Matrix ι ι F) : Prop :=
  ∀ h : IsUnit M.det, (chiM M h : ℝ≥0∞) = modF F M.det
end PI.NglqJacSplitW


