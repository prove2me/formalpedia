-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:31:55.333173+00:00
-- url     : https://prove2.me/theorems/b0789678-1072-46d3-970f-9756cc5f6e47
-- title:
--   Statements Deg Zero Loc Residue
-- statement:
--   Definitions and structural lemmas for Statements Deg Zero Loc Residue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLocResidue.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
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
def DegZeroLocResidue.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [DecidableEq K] (ι : K → Type) (P : Ideal (MRing ι F))
    [P.IsPrime] (W : Ideal (MRing ι F)) [W.IsPrime], P ≤ W →
    ∃ ρ : degZeroLoc P {W} →+* FractionRing (MRing ι F ⧸ W),
      (∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b →
        IsMultiHomog g b → g ∉ W →
        (x : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) →
        ρ x = algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W f) /
            algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W g)) ∧
      (∀ x : degZeroLoc P {W},
        ρ x = 0 ↔ ¬ ∃ y ∈ degZeroLoc P {W}, (x : FractionRing (MRing ι F ⧸ P)) * y = 1) ∧
      ∀ z : FractionRing (MRing ι F ⧸ W), z ∈ homFracDegZero W ↔ ∃ x, ρ x = z
end
end GroundTheory.Heights₂.Heights.FieldNumbers


