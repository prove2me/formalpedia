-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
-- name    : ReciprocityTheory_DualLattices_DualLenStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:04.350074+00:00
-- url     : https://prove2.me/theorems/52f30143-d312-4b9f-81b9-375c925e8a7d
-- title:
--   Dual Len Statement
-- statement:
--   Definitions and structural lemmas for Dual Len Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualLenStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
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
def zSub {R : Type} [CommRing R] {d : ℕ} {κ : Type} [Fintype κ] (A : Matrix (Fin d) κ R) (c : R) :
    Submodule R (Fin d → R) where
  carrier := {y | ∃ z, Aᵀ *ᵥ y = c • z}
  add_mem' := by
    rintro y y' ⟨z, hz⟩ ⟨z', hz'⟩
    exact ⟨z + z', by rw [mulVec_add, hz, hz', smul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a y ⟨z, hz⟩
    exact ⟨a • z, by rw [mulVec_smul, hz, smul_comm]⟩
def DualLenStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix (Fin d) κ R)
    (c : R), c ≠ 0 → (∀ w : Fin d → R, ∃ t, A *ᵥ t = c • w) →
    ∀ c₁ : NNReal, HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) c₁ →
      ∃ y : NNReal, HasLen v R ((Fin d → R) ⧸ zSub A c) y ∧ y * c₁ = v (algebraMap R C c) ^ d
section Coord
variable {R : Type} [CommRing R] {g d : ℕ} (P : Matrix (Fin g) (Fin g) R) (hP : P * P = P)
  (φ : LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R))
def matU : Matrix (Fin g) (Fin d) R := Matrix.of fun k l => ((φ.symm (Pi.single l 1)) : Fin g → R) k
def matV : Matrix (Fin d) (Fin g) R :=
  Matrix.of fun l k => φ ⟨P *ᵥ Pi.single k 1, ⟨_, rfl⟩⟩ l
end Coord
end ReciprocityTheory.PGsh.Up


