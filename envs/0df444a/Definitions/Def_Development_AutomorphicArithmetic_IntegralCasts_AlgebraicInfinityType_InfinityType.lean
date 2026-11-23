-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_AlgebraicInfinityType_InfinityType
-- name    : Development_AutomorphicArithmetic_IntegralCasts_AlgebraicInfinityType_InfinityType
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:21.686201+00:00
-- url     : https://prove2.me/theorems/a8cb59f0-cdef-472c-850c-6e127e3811ec
-- title:
--   Infinity Type
-- statement:
--   Definitions and structural lemmas for Infinity Type, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/AlgebraicInfinityType/InfinityType.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Reformulated.AlgebraicInfinityType
open NumberField
@[ext]
structure InfinityType (F : Type*) [Field F] (n : ℕ) where

  pairs : (F →+* ℂ) → Multiset (ℂ × ℂ)
  card_pairs : ∀ σ, Multiset.card (pairs σ) = n
  sub_int : ∀ σ, ∀ p ∈ pairs σ, ∃ m : ℤ, p.1 - p.2 = m
  pairs_conjugate : ∀ σ, pairs (ComplexEmbedding.conjugate σ) = (pairs σ).map Prod.swap
namespace InfinityType
variable {F : Type*} [Field F] {n : ℕ}
def exponents (t : InfinityType F n) (σ : F →+* ℂ) : Multiset ℂ :=
  (t.pairs σ).map Prod.fst
def IsLAlgebraic (t : InfinityType F n) : Prop :=
  ∀ σ, ∀ a ∈ t.exponents σ, ∃ m : ℤ, a = m
def IsAlgebraic (t : InfinityType F n) : Prop :=
  ∀ σ, ∀ a ∈ t.exponents σ, ∃ m : ℤ, a = ((n : ℂ) - 1) / 2 + m
def IsRegular (t : InfinityType F n) : Prop :=
  ∀ σ, (t.exponents σ).Nodup
def IsRegularAlgebraic (t : InfinityType F n) : Prop :=
  t.IsAlgebraic ∧ t.IsRegular
def twist (t : InfinityType F n) (s : ℂ) : InfinityType F n where
  pairs σ := (t.pairs σ).map fun p => (p.1 + s, p.2 + s)
  card_pairs σ := by simp [t.card_pairs]
  sub_int σ p hp := by
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
    simpa using t.sub_int σ q hq
  pairs_conjugate σ := by simp [t.pairs_conjugate]
end InfinityType
def RegularAlgebraicInfinityType (F : Type*) [Field F] (n : ℕ) : Type _ :=
  {t : InfinityType F n // t.IsRegularAlgebraic}
end Reformulated.AlgebraicInfinityType


