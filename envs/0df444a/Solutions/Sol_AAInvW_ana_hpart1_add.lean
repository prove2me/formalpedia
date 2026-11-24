-- Prove2me | solution 1 for AAInvW.ana_hpart1_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:36:38.476104+00:00
-- url     : https://prove2.me/submissions/961496cd-d2e2-4bdc-9110-f1b7c16733d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Theorems.Thm_AAInvW_ana_hpart1_eq

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
theorem _root_.solution (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (Z + W) = hpart1 H Z + hpart1 H W := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart1_eq hH, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  module
end AAInvW
