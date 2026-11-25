-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:06:53.408681+00:00
-- url     : https://prove2.me/theorems/78b86019-7dfd-4da3-a636-56c8b3eeeff5
-- title:
--   Statements Deg Zero Loc Frac
-- statement:
--   Definitions and structural lemmas for Statements Deg Zero Loc Frac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLocFrac.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFiniteRank
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
def DegZeroLocFrac.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W) →
    haveI := hP.isPrime
    ∀ x ∈ homFracDegZero P, ∃ y ∈ degZeroLoc P 𝒲, ∃ z ∈ degZeroLoc P 𝒲, z ≠ 0 ∧ x = y / z
end
end GroundTheory.Heights₂.Heights.FieldNumbers


