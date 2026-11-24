-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:10:34.488193+00:00
-- url     : https://prove2.me/theorems/6531bb2e-a78c-4aa6-b3aa-05324a6c79c0
-- title:
--   Ae Equality From Test Functions
-- statement:
--   Definitions and structural lemmas for Ae Equality From Test Functions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
def pl (a b k x : ℝ) : ℝ := Real.smoothTransition (k * (x - a)) * Real.smoothTransition (k * (b - x))
def FinT (f : ℝ × ℝ → ℝ≥0∞) : Prop :=
  ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
    (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * f τ ∂(volume.restrict Quad)) ≠ ∞
end Formalism.FourierDecayAlt.P.B3
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B3
end Formalism.FourierDecayAlt.P


