-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatCompMultSimple
-- name    : Formalism_CharacterColumnKernels_StatCompMultSimple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:16.651369+00:00
-- url     : https://prove2.me/theorems/76aa9c4a-eef4-4d56-a655-e799b4de5dc0
-- title:
--   Stat Comp Mult Simple
-- statement:
--   Definitions and structural lemmas for Stat Comp Mult Simple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatCompMultSimple.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
noncomputable section
namespace Formalism.NG
universe u v w
def StatCompMultAdd : Prop :=
  ∀ (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (S : Type v) [AddCommGroup S]
    [Module R S], IsFiniteLength R M → ∀ N : Submodule R M,
    compMult R M S = compMult R N S + compMult R (M ⧸ N) S
def StatCompMultSimple : Prop :=
  ∀ (R : Type*) [Ring R] (T : Type u) [AddCommGroup T] [Module R T] (S : Type v) [AddCommGroup S]
    [Module R S], IsSimpleModule R T →
    compMult R T S = if Nonempty (T ≃ₗ[R] S) then 1 else 0
def StatCompMultCongr : Prop :=
  ∀ (R : Type*) [Ring R] (M M' : Type u) [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (S : Type v) (S' : Type w) [AddCommGroup S] [Module R S] [AddCommGroup S']
    [Module R S'], (M ≃ₗ[R] M') → (S ≃ₗ[R] S') → compMult R M S = compMult R M' S'
def StatEpsCount : Prop :=
  ∀ (O Λ : Type*) (S : Type v) [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]
    [AddCommGroup S] [Module Λ S] (ε : Λ), IsIdempotentElem ε → IsSimpleModule Λ S →
    (∃ s : S, ε • s ≠ 0) →
    (∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ) →
    (∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ) →
    ∀ (T : Type u) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower O Λ T],
      IsSimpleModule Λ T →
      Module.length O (epsImg O (M := T) ε) = if Nonempty (T ≃ₗ[Λ] S) then 1 else 0
def StatEpsMultCount : Prop :=
  ∀ (O Λ : Type*) (M : Type u) (S : Type v) [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]
    [AddCommGroup M] [Module Λ M] [Module O M] [IsScalarTower O Λ M] [AddCommGroup S]
    [Module Λ S] (ε : Λ), IsIdempotentElem ε → IsSimpleModule Λ S → (∃ s : S, ε • s ≠ 0) →
    (∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ) →
    (∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ) →
    IsFiniteLength Λ M →
    Module.length O (epsImg O (M := M) ε) = compMult Λ M S
def StatFinLenIff : Prop :=
  ∀ (O Λ M : Type*) [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ] [Module.Finite O Λ]
    [AddCommGroup M] [Module Λ M] [Module O M] [IsScalarTower O Λ M],
    IsFiniteLength Λ M ↔ IsFiniteLength O M
end Formalism.NG


