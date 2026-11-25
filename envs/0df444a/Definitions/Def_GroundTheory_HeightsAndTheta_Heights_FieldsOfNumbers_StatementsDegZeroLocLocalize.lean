-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocalize
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocalize
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:19:40.366255+00:00
-- url     : https://prove2.me/theorems/8e650642-99d9-4182-9d93-92076ca7c643
-- title:
--   Statements Deg Zero Loc Localize
-- statement:
--   Definitions and structural lemmas for Statements Deg Zero Loc Localize, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLocLocalize.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocSeparate
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
def DegZeroLocLocalize.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) →
    haveI := hP.isPrime
    ∀ W ∈ 𝒲, ∀ y ∈ degZeroLoc P {W}, ∃ b ∈ degZeroLoc P 𝒲, ∃ s ∈ degZeroLoc P 𝒲,
      (∃ t ∈ degZeroLoc P {W}, s * t = 1) ∧ y * s = b
end
end GroundTheory.Heights₂.Heights.FieldNumbers


