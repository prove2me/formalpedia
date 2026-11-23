-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_LenIdStatement
-- name    : ReciprocityTheory_DualLattices_LenIdStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:44.783514+00:00
-- url     : https://prove2.me/theorems/1bf11a27-0e99-468c-adc0-6e50df463bc5
-- title:
--   Len Id Statement
-- statement:
--   Definitions and structural lemmas for Len Id Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LenIdStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthStatement
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
def qE {R : Type} [CommRing R] {g m : ℕ} (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    Submodule R (Fin g ⊕ Fin g → R) :=
  (LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)).comap (LinearMap.funLeft R R Sum.inl) ⊓
    (LinearMap.range (Matrix.mulVecLin (εL i))).comap (LinearMap.funLeft R R Sum.inr)
abbrev xModE {R : Type} [CommRing R] {g m : ℕ} (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) :=
  qE εL i (π i) ⧸
    ((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin (fromRows Ht Bt))).comap
      (qE εL i (π i)).subtype
def LenIdStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R) (E : Matrix (Ix g) (Ix g) R)
    (cp : R), cp ≠ 0 → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
    ∀ (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    ∀ (i : Fin m) (d : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin d → R)) →
    ∀ c₁ c₂ : NNReal, HasLen v R (cokE Ht εT εL i (π i)) c₁ →
      HasLen v R (cokE Ht εT εL (π i) i) c₂ →
      ∃ X : NNReal, HasLen v R (xModE Ht Bt εT εL π i) X ∧ X * c₁ = v (algebraMap R C cp) ^ d * c₂
end ReciprocityTheory.PGsh.Up


