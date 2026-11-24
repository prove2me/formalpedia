-- Prove2me | solution 1 for AAInvW.ana_Htheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:59:50.464886+00:00
-- url     : https://prove2.me/submissions/7780efe3-239b-49ad-9dbc-651d5a23ab4c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Theorems.Thm_AAInvW_ana_HH_left

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
theorem _root_.solution (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) : H * (H * Zᴴ * H) = Zᴴ * H := by
  rw [Matrix.mul_assoc, ana_HH_left hH]
end AAInvW
