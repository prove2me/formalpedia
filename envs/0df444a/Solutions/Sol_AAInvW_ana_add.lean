-- Prove2me | solution 1 for AAInvW.ana_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:37:59.792131+00:00
-- url     : https://prove2.me/submissions/073deb8c-75cf-4f6e-9b47-1b440d91b261

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
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) (hB : inLH H B) : inLH H (A + B) := by
  unfold inLH at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Aᴴ * H + Bᴴ * H + (H * A + H * B) = (Aᴴ * H + H * A) + (Bᴴ * H + H * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]
end AAInvW
