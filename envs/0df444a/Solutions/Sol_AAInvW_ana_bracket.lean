-- Prove2me | solution 1 for AAInvW.ana_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:34:59.494433+00:00
-- url     : https://prove2.me/submissions/b715fcf3-508a-4c35-8e50-3fa2652175d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique

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
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
namespace AAInvW
theorem _root_.solution {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (hY : inLH H Y) :
    inLH H (X * Y - Y * X) := by
  unfold inLH at *
  have hX' : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * H = H * Y * X := by
    rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * H = H * X * Y := by
    rw [Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2,
    Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  abel
end AAInvW
