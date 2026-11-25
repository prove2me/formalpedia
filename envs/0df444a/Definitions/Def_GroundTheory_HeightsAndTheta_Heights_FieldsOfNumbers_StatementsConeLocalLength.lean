-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalLength
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalLength
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:30.029924+00:00
-- url     : https://prove2.me/theorems/782b80ff-4bb9-550e-b3a0-351b27d82cc3
-- title:
--   Statements Cone Local Length
-- statement:
--   Definitions and structural lemmas for Statements Cone Local Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsConeLocalLength.lean

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
def ConeLocalLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W), P ≤ W →
    ∀ (c : K → ℕ) (a h : MRing ι F), IsMultiHomog a c → IsMultiHomog h c → h ∉ W →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ α : degZeroLoc P {W},
      (α : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P a) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P h) →
        multAt (P ⊔ Ideal.span {a}) W =
          Ring.ord (degZeroLoc P {W}) α
end
end GroundTheory.Heights₂.Heights.FieldNumbers


