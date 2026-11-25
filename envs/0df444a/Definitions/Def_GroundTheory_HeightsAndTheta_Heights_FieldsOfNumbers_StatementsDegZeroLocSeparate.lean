-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocSeparate
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocSeparate
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:05:29.109932+00:00
-- url     : https://prove2.me/theorems/f4636ab2-a1e1-54be-ab8c-7a563f719cc7
-- title:
--   Statements Deg Zero Loc Separate
-- statement:
--   Definitions and structural lemmas for Statements Deg Zero Loc Separate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLocSeparate.lean

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
def DegZeroLocSeparate.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) →
    haveI := hP.isPrime
    ∀ W₁ ∈ 𝒲, ∀ W₂ ∈ 𝒲, ¬ W₁ ≤ W₂ →
      ∃ x ∈ degZeroLoc P 𝒲, (¬ ∃ y ∈ degZeroLoc P {W₁}, x * y = 1) ∧
        ∃ y ∈ degZeroLoc P {W₂}, x * y = 1
section Example
abbrev lineOtherPointIdeal : Ideal LineRing := Ideal.span {X ⟨(), (1 : Fin 2)⟩}
end Example
end
end GroundTheory.Heights₂.Heights.FieldNumbers


