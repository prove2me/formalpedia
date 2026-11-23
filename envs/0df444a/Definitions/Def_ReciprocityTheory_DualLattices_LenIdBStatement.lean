-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
-- name    : ReciprocityTheory_DualLattices_LenIdBStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:58.397382+00:00
-- url     : https://prove2.me/theorems/ef7da6e4-f79f-416f-8bf7-e221668ebfa7
-- title:
--   Len Id BStatement
-- statement:
--   Definitions and structural lemmas for Len Id BStatement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LenIdBStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
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
variable {R : Type} [CommRing R] {g m : ℕ}
def inclE (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    LinearMap.range (Matrix.mulVecLin (εL i)) →ₗ[R] qE εL i j where
  toFun x := ⟨Sum.elim (0 : Fin g → R) (x : Fin g → R), by
    refine ⟨?_, ?_⟩
    · show (Sum.elim (0 : Fin g → R) (x : Fin g → R)) ∘ Sum.inl ∈ LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)
      exact ⟨0, by funext k; simp⟩
    · show (Sum.elim (0 : Fin g → R) (x : Fin g → R)) ∘ Sum.inr ∈ LinearMap.range (Matrix.mulVecLin (εL i))
      exact x.2⟩
  map_add' x y := by ext k; rcases k with k | k <;> simp
  map_smul' c x := by ext k; rcases k with k | k <;> simp
def projE (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    qE εL i j →ₗ[R] LinearMap.range (Matrix.mulVecLin (εL j)ᵀ) where
  toFun q := ⟨(q : Fin g ⊕ Fin g → R) ∘ Sum.inl, q.2.1⟩
  map_add' x y := rfl
  map_smul' c x := rfl
abbrev sxE (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    Submodule R (qE εL i (π i)) :=
  ((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin (fromRows Ht Bt))).comap
    (qE εL i (π i)).subtype
abbrev yModE (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :=
  LinearMap.range (Matrix.mulVecLin (εL i)) ⧸ (sxE Ht Bt εT εL π i).comap (inclE εL i (π i))
def LenIdBStatement : Prop :=
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
    ∀ c₁ : NNReal, HasLen v R (cokE Ht εT εL i (π i)) c₁ →
      ∃ y : NNReal, HasLen v R (yModE Ht Bt εT εL π i) y ∧ y * c₁ = v (algebraMap R C cp) ^ d
end ReciprocityTheory.PGsh.Up


