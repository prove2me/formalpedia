-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:41:57.454444+00:00
-- url     : https://prove2.me/theorems/2b5c43ee-1cb5-4a50-8853-fecd0359d2a6
-- title:
--   YOperator Leibniz Rule
-- statement:
--   Definitions and structural lemmas for YOperator Leibniz Rule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace QnYLeibnizW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Gen
variable {n : ℕ}
def evL (w : Fin n → ℂ) (p : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (M *ᵥ w) p
      map_add' := fun M N => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
def hermL (H : Matrix (Fin n) (Fin n) ℂ) (w x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => herm H (M *ᵥ w) x
      map_add' := fun M N => by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c M => by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }
end Gen
section Pos
variable {k r : ℕ} {i : Fin (r + 1)}
end Pos
section Deriv
variable {k r : ℕ} {i : Fin (r + 1)}
end Deriv
end QnYLeibnizW


