-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:10:37.450395+00:00
-- url     : https://prove2.me/theorems/c7872f11-ae42-4d60-8835-bae3a559c115
-- title:
--   Casimir Eigenvalue Coefficients
-- statement:
--   Definitions and structural lemmas for Casimir Eigenvalue Coefficients, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean

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
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
def SV (σ : Mx k r → (Vs →L[ℂ] Vs)) (w : Vs) : Prop := CkOn ⊤ (GV k r) (fun g => σ g w)
variable {σ : Mx k r → (Vs →L[ℂ] Vs)}
def stepV (σ : Mx k r → (Vs →L[ℂ] Vs)) (c : ℂ) (a b : Fin (2 * r + k + 1)) (y : Vs) : Vs :=
  (if a = b then c • y else 0) + EcRep (Hpk k r) σ (Matrix.single a b 1) y
end Qb1
end Formalism.FourierDecayAlt.P


