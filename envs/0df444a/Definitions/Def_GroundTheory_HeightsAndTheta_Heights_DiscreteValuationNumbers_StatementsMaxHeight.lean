-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMaxHeight
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMaxHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:46.203083+00:00
-- url     : https://prove2.me/theorems/425f3b87-d34c-4990-9386-e73c2e7c230b
-- title:
--   Statements Max Height
-- statement:
--   Definitions and structural lemmas for Statements Max Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsMaxHeight.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
def MaximalIdealHeightFG.Statement : Prop :=
  ∀ (F : Type u) [Field F] (A : Type u) [CommRing A] [IsDomain A] [Algebra F A]
    [Algebra.FiniteType F A] (m : Ideal A), m.IsMaximal → (m.height : WithBot ℕ∞) = ringKrullDim A
section Examples
example : Algebra.FiniteType ℚ (MvPolynomial (Fin 2) ℚ) := inferInstance
example : IsDomain (MvPolynomial (Fin 2) ℚ) := inferInstance
end Examples
end GroundTheory.Heights₂.Heights.NumbersDVR


