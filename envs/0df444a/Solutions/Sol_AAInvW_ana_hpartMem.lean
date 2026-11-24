-- Prove2me | solution 1 for AAInvW.ana_hpartMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:19:07.267969+00:00
-- url     : https://prove2.me/submissions/eb1b0e3a-9197-46bf-ab2e-055a93bb2c19

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Theorems.Thm_AAInvW_ana_HXH
import Theorems.Thm_AAInvW_ana_hpart1_eq
import Theorems.Thm_AAInvW_ana_hpart2_eq
import Theorems.Thm_AAInvW_ana_thetaH
import Theorems.Thm_AAInvW_ana_Htheta
import Theorems.Thm_Formalism_REAL_star_one_div_two_I
import Theorems.Thm_Formalism_REAL_star_one_half


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
theorem _root_.solution (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inLH H (hpart1 H Z) ∧ inLH H (hpart2 H Z) ∧ Z = hpart1 H Z + Complex.I • hpart2 H Z ∧
      (inLH H Z → hpart1 H Z = Z ∧ hpart2 H Z = 0) := by
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold inLH
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul,
      ana_thetaH hH, Matrix.mul_smul, Matrix.mul_sub, ana_Htheta hH, star_one_half, ← smul_add]
    simp
  · unfold inLH
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul,
      ana_thetaH hH, Matrix.mul_smul, Matrix.mul_add, ana_Htheta hH, star_one_div_two_I, neg_smul,
      add_comm (H * Z), neg_add_cancel]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
    norm_num
  · intro hX
    rw [ana_HXH hH hX, sub_neg_eq_add, add_neg_cancel, smul_zero, ← two_smul ℂ Z, smul_smul]
    norm_num
end AAInvW
