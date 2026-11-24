-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:08:53.473337+00:00
-- url     : https://prove2.me/theorems/c41a6c07-5cb5-4411-ad43-8c50046a6175
-- title:
--   Zinv Bound
-- statement:
--   Definitions and structural lemmas for Zinv Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZinvBound.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
section ube
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def UBL (f : Mat k r → E) (S : Set (Mat k r)) (n e γ : ℕ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ UB f S n C e γ) ∧ LSS f S
end ube
def zinv (c : ℝ) (m : ℕ) (z : ℂ) : ℂ := (sc c (Complex.normSq z) : ℂ) * z⁻¹ ^ m
end Formalism.FourierDecayAlt.P.AdmissibleLieWords


