-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:12.611196+00:00
-- url     : https://prove2.me/theorems/7ab4c460-60dc-47b1-a610-29e64ecc13b0
-- title:
--   Statements Deg Zero Loc Quot
-- statement:
--   Definitions and structural lemmas for Statements Deg Zero Loc Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLocQuot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
def DegZeroLocQuot.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [DecidableEq K] (ι : K → Type) (P : Ideal (MRing ι F))
    [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))), (∀ W ∈ 𝒲, W.IsPrime) →
    ∀ x ∈ degZeroLoc P 𝒲, ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
      g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧
      x = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


