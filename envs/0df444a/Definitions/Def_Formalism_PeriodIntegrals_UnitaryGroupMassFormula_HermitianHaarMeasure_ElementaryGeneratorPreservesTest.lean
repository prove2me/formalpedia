-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:49:06.624189+00:00
-- url     : https://prove2.me/theorems/7faa61ac-a73a-4b63-bc14-9bc581130525
-- title:
--   Elementary Generator Preserves Test
-- statement:
--   Definitions and structural lemmas for Elementary Generator Preserves Test, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorPreservesTest.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end Linfty
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def yExt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) (g : Mx k r) : ℂ :=
  ∑ l, Hpk k r (posL k r i c) l * star (∑ m, star ((Hpk k r *ᵥ fvec k r z i) m) * g m l)
def bExt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) (g : Mx k r) : ℂ :=
  ∑ j, star (fvec k r z i j) * ∑ l, Hpk k r j l * g l (posL k r i c)
end PI.QnHermHaar


