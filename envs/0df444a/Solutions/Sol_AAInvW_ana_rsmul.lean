-- Prove2me | solution 1 for AAInvW.ana_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:02:44.858393+00:00
-- url     : https://prove2.me/submissions/f37d23ef-ad30-4503-8371-846bd5a5aa45

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
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (r : ℝ) : inLH H ((r : ℂ) • X) := by
  unfold inLH at *
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]
end AAInvW
