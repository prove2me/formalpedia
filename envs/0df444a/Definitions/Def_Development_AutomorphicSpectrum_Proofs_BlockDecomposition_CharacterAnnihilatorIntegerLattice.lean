-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CharacterAnnihilatorIntegerLattice
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CharacterAnnihilatorIntegerLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:32.87127+00:00
-- url     : https://prove2.me/theorems/95848d08-a7d7-4d38-93c4-86aa05bf2e6c
-- title:
--   Character Annihilator Integer Lattice
-- statement:
--   Definitions and structural lemmas for Character Annihilator Integer Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CharacterAnnihilatorIntegerLattice.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.CharLattice
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def annihilator (ψ : AddChar k Circle) (n : ℕ) (b : k) : AddSubgroup (Fin n → k) where
  carrier := {x | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1}
  zero_mem' := fun t _ => by simp
  add_mem' := fun {x y} hx hy t ht => by
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, hx t ht, hy t ht, one_mul]
  neg_mem' := fun {x} hx t ht => by
    rw [dotProduct_neg, mul_neg, AddChar.map_neg_eq_inv, hx t ht, inv_one]
end GlobalTheory.CompanionTheory.CharLattice


