-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_IrreducibleCharacters_CuspidalCharacters
-- name    : Development_AbelianVarietyTheory_BlockTheory_IrreducibleCharacters_CuspidalCharacters
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:49:54.134178+00:00
-- url     : https://prove2.me/theorems/aa3c25f0-f3a2-469f-8554-3d7eecfd7db8
-- title:
--   Cuspidal Characters
-- statement:
--   Definitions and structural lemmas for Cuspidal Characters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/IrreducibleCharacters/CuspidalCharacters.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
open Matrix
def IsCharacter {G : Type*} [Group G] (χ : G → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ∀ g : G, χ g = ρ.character g
def IsIrreducibleCharacter {G : Type*} [Group G] [Finite G] (χ : G → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V),
    ρ.IsIrreducible ∧ ∀ g : G, χ g = ρ.character g
def InUpperRightBlock {F : Type*} [Field F] {d : ℕ} (a : ℕ) (N : Matrix (Fin d) (Fin d) F) :
    Prop :=
  ∀ i j : Fin d, ¬ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) → N i j = 0
theorem InUpperRightBlock.mul_eq_zero {F : Type*} [Field F] {d a : ℕ}
    {M N : Matrix (Fin d) (Fin d) F} (hM : InUpperRightBlock a M) (hN : InUpperRightBlock a N) :
    M * N = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < a
  · rw [hM i k (by omega), zero_mul]
  · rw [hN k j (by omega), mul_zero]
def unipotentRadical (F : Type*) [Field F] (d a : ℕ) : Subgroup (GL (Fin d) F) where
  carrier := {g | InUpperRightBlock a ((g : Matrix (Fin d) (Fin d) F) - 1)}
  one_mem' := by
    intro i j _
    simp
  mul_mem' := by
    intro g h hg hh i j hij
    have h0 := InUpperRightBlock.mul_eq_zero hg hh
    have e : ((g * h : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) - 1
        = ((g : Matrix (Fin d) (Fin d) F) - 1) * ((h : Matrix (Fin d) (Fin d) F) - 1)
          + ((g : Matrix (Fin d) (Fin d) F) - 1) + ((h : Matrix (Fin d) (Fin d) F) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, h0, zero_add, Matrix.add_apply, hg i j hij, hh i j hij, add_zero]
  inv_mem' := by
    intro g hg i j hij
    have h0 := InUpperRightBlock.mul_eq_zero hg hg
    have h1 : ((g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * (g : Matrix (Fin d) (Fin d) F)
        = 1 := Units.inv_mul g
    have e : ((g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) - 1
        = - ((g : Matrix (Fin d) (Fin d) F) - 1) := by
      set x := ((g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
      set y := (g : Matrix (Fin d) (Fin d) F)
      have h2 : x * ((y - 1) * (y - 1)) = (x * y) * y - 2 * (x * y) + x := by noncomm_ring
      rw [h0, h1, mul_zero] at h2
      have h3 : x = - (1 * y - 2 * 1) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2.symm
      rw [h3]; noncomm_ring
    rw [e, Matrix.neg_apply, hg i j hij, neg_zero]
def IsCuspidalRep {F : Type*} [Field F] {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin d) F) V) : Prop :=
  ∀ a : ℕ, 0 < a → a < d →
    ∀ v : V, (∀ u ∈ unipotentRadical F d a, ρ u v = v) → v = 0
def IsCuspidalCharacter (F : Type*) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ (GL (Fin d) F) V),
    ρ.IsIrreducible ∧ IsCuspidalRep ρ ∧ ∀ g, χ g = ρ.character g
noncomputable def lineRep {G : Type*} [Group G] (θ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := (θ g : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]
end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters


