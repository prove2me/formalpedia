-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
-- name    : ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:47.656291+00:00
-- url     : https://prove2.me/theorems/c0271266-d29e-4dac-b8c8-e49efafd87a4
-- title:
--   Eigen Length Frobenius Statement
-- statement:
--   Definitions and structural lemmas for Eigen Length Frobenius Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigenLengthFrobeniusStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section Defs
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
def bt2 (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H) : Matrix (Fin g) (Ix g) R :=
  ∑ i, U.εL i * H.Bt * U.εT i
end Defs
def EigenLengthProductStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    ∀ X : Fin m → NNReal, (∀ i, HasLen v R (xModE Ht Bt εT εL π i) (X i)) →
      ∏ i, X i = v (algebraMap R C (fromRows Ht Bt).det)
def EigenLengthFrobeniusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) →
    ∏ i, X i = v (algebraMap R C cp) ^ g →
    ∀ i, X i ^ p ≤ X (U.φ i) * v (algebraMap R C (p : R)) ^ U.r (U.φ i)
end ReciprocityTheory.PGsh.Up


