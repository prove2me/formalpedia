-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T15:13:46.576669+00:00
-- url     : https://prove2.me/theorems/2732910d-3993-439d-93da-ced592b304b3
-- title:
--   Ana Hpart Unique
-- statement:
--   Definitions and structural lemmas for Ana Hpart Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/AnaHpartUnique.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
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
namespace AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def inLH {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) : Prop := Xᴴ * H + H * X = 0
section Basic
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
end Basic
end AAInvW


