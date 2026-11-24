-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:37:07.076727+00:00
-- url     : https://prove2.me/theorems/076703b3-16fd-474e-8266-d565c401eacc
-- title:
--   Has Deriv At Cvs
-- statement:
--   Definitions and structural lemmas for Has Deriv At Cvs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtCvs.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def fct (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) : ℂ :=
  (Dmin k r z z' g l)⁻¹ ^ a l * (star (Dmin k r z z' g l))⁻¹ ^ b l
end Formalism.FourierDecayAlt.P.MinorPolynomials


