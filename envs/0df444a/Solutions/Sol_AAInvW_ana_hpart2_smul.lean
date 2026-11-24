-- Prove2me | solution 1 for AAInvW.ana_hpart2_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:18:20.469675+00:00
-- url     : https://prove2.me/submissions/05ffceaf-3aaa-4720-a699-f2748c1d6b15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Theorems.Thm_AAInvW_ana_hpart1_eq
import Theorems.Thm_AAInvW_ana_hpart2_eq
import Theorems.Thm_AAInvW_ana_inv2I

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
theorem _root_.solution (hH : HInvol H) (x y : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (((x : ℂ) + (y : ℂ) * Complex.I) • Z) = (x : ℂ) • hpart2 H Z + (y : ℂ) • hpart1 H Z := by
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, ana_inv2I, conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul]
  have hs : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hs]
  match_scalars <;> first | ring1 | linear_combination ((y : ℂ) / 2) * Complex.I_sq | linear_combination (-(y : ℂ) / 2) * Complex.I_sq
end AAInvW
