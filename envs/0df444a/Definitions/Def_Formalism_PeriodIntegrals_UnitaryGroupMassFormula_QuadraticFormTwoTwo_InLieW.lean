-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:10:58.448345+00:00
-- url     : https://prove2.me/theorems/5b0bedfc-5ddb-4158-85ce-7b739305bab0
-- title:
--   In Lie W
-- statement:
--   Definitions and structural lemmas for In Lie W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/InLieW.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def Pp (P : M.Par) : M.Par := ⟨P.k, P.r, P.T, P.T', P.u', P.u'⟩
def Pq (P : M.Par) : M.Par := ⟨P.k, P.r, P.T, P.T', P.u, P.u⟩
def inLieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) : Prop :=
  Xᴴ * Hpk k r + Hpk k r * X = 0 ∧ X *ᵥ z = 0 ∧
    ∀ a : Fin r, X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0
def SmVec {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (π : Mx k r → (Wp →L[ℂ] Wp)) : Set Wp :=
  {x | ∀ h ∈ UWset k r z, ∀ X : Mx k r, inLieW k r z X →
    DifferentiableAt ℝ (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) x) 0}
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors


