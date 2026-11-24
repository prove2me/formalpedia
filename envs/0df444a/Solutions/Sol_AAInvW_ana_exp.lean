-- Prove2me | solution 1 for AAInvW.ana_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:18:15.824843+00:00
-- url     : https://prove2.me/submissions/52f6ee99-4659-4d91-a807-09b53c15c9c7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Theorems.Thm_AAInvW_ana_inv
import Theorems.Thm_AAInvW_ana_isUnit

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
theorem _root_.solution (hH : HInvol H) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inLH H Y) :
    inUH H (NormedSpace.exp Y) := by
  have hY' : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
    rw [ana_inv hH, Matrix.mul_neg, ← hY', Matrix.mul_assoc, hH.2, Matrix.mul_one]
  have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ (ana_isUnit hH), ana_inv hH]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  unfold inUH
  rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH.2, Matrix.mul_one, Matrix.mul_assoc, hc,
    Matrix.mul_one]
end AAInvW
