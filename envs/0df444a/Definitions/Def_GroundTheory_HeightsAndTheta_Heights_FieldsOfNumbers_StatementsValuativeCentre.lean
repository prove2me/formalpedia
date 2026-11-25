-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:42.237488+00:00
-- url     : https://prove2.me/theorems/a6e63aec-9d6a-4c06-9f11-68b775198514
-- title:
--   Statements Valuative Centre
-- statement:
--   Definitions and structural lemmas for Statements Valuative Centre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsValuativeCentre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
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
def ValuativeCentre.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P),
    haveI := hP.isPrime
    ∀ R : ValuationSubring (FractionRing (MRing ι F ⧸ P)),
      (∀ c : F, algebraMap F (FractionRing (MRing ι F ⧸ P)) c ∈ R) →
      ∃ y : Ideal (MRing ι F), IsMultiProjPrime y ∧ P ≤ y ∧
        ∀ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
              algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ R ∧
            (f ∈ y ↔ algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
                (Ideal.Quotient.mk P f) / algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈
              R.nonunits)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


