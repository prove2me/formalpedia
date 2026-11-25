-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:09.630887+00:00
-- url     : https://prove2.me/theorems/966d629b-b551-4a5f-8618-49d072f6db53
-- title:
--   Im Form Apply
-- statement:
--   Definitions and structural lemmas for Im Form Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImFormApply.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGauss.transl_apply
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.pderivEval_X


set_option autoImplicit false
namespace GlobalTheory.UpperHalfImaginaryForm
open ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {ι : Type} [Fintype ι]
def imForm : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (Hf x y).im)
    (fun x y z => by simp [Hf, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Hf, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum, smul_eq_mul]
      simp)
    (fun x y z => by simp [Hf, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
        mul_left_comm _ (c : ℂ), ← Finset.mul_sum, smul_eq_mul]
      simp)
variable {n : ℕ}
def upper (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) :
    EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℝ :=
  b.constr ℝ fun i => b.constr ℝ fun j => if i < j then imForm (b i) (b j) else 0
end
end GlobalTheory.UpperHalfImaginaryForm


