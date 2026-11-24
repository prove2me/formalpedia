-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:41:44.511749+00:00
-- url     : https://prove2.me/theorems/1a281a8d-57f7-4582-9d29-210303231bc7
-- title:
--   Admissible Word Length Le
-- statement:
--   Definitions and structural lemmas for Admissible Word Length Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
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
section defs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def LSS (f : Mat k r → E) (S : Set (Mat k r)) : Prop :=
  ∀ g ∈ S, ∃ f' : Mat k r → E, ContDiff ℝ ∞ f' ∧ ∃ V : Set (Mat k r), IsOpen V ∧ g ∈ V ∧
    ∀ g' ∈ GV k r, g' ∈ V → f g' = f' g'
def UB (f : Mat k r → E) (S : Set (Mat k r)) (n : ℕ) (C : ℝ) (e γ : ℕ) : Prop :=
  ∀ w, admitted n w → ∀ g ∈ S, ‖Dw w f g‖ ≤ C * gN g ^ (e + γ * w.length)
end defs
section app
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
end app
end Formalism.FourierDecayAlt.P.AdmissibleLieWords


