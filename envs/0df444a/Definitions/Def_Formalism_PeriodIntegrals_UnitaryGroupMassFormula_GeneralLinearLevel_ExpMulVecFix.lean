-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:59.290032+00:00
-- url     : https://prove2.me/theorems/ec06410e-9120-414f-9a92-1631086b85fa
-- title:
--   Exp Mul Vec Fix
-- statement:
--   Definitions and structural lemmas for Exp Mul Vec Fix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ExpMulVecFix.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
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
namespace Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Flow (G : Set (Matrix (Fin n) (Fin n) ℂ)) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G
def LocExt (G : Set (Matrix (Fin n) (Fin n) ℂ)) (f F : Matrix (Fin n) (Fin n) ℂ → E)
    (U : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ h ∈ U, h ∈ G → f h = F h
end Formalism.FourierDecayAlt.Q.EabGlW


