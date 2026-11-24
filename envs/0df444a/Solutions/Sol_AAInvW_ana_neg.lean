-- Prove2me | solution 1 for AAInvW.ana_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:59:52.795862+00:00
-- url     : https://prove2.me/submissions/57240c78-d8a9-4640-a415-8baa4b1c8320

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
theorem _root_.solution {A : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) : inLH H (-A) := by
  unfold inLH at *
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hA, neg_zero]
end AAInvW
