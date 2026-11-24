-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFiniteAlgebraLengthSum
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFiniteAlgebraLengthSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:35.902059+00:00
-- url     : https://prove2.me/theorems/78b8fade-33c2-4f72-be30-4c2bda9f3425
-- title:
--   Statements Finite Algebra Length Sum
-- statement:
--   Definitions and structural lemmas for Statements Finite Algebra Length Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsFiniteAlgebraLengthSum.lean

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
def FiniteAlgebraLengthSum.Statement : Prop :=
  ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (ι : Type u) [Fintype ι] (𝔪 : ι → Ideal B) (h𝔪 : ∀ i, (𝔪 i).IsMaximal),
    Function.Injective 𝔪 → (∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) →
    ∀ (C : ι → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)],
      (∀ i, haveI := (h𝔪 i).isPrime
        IsLocalization.AtPrime (C i) (𝔪 i)) →
      ∀ α : A,
        Module.length A (B ⧸ LinearMap.range (LinearMap.lsmul A B α)) =
          ∑ i, Ring.ord (C i) (algebraMap B (C i) (algebraMap A B α)) *
            Module.length A (B ⧸ 𝔪 i)
instance span_two_isPrime : (Ideal.span {(2 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
abbrev ZLocTwo : Type := Localization.AtPrime (Ideal.span {(2 : ℤ)})
end
end GroundTheory.Heights₂.Heights.FieldNumbers


