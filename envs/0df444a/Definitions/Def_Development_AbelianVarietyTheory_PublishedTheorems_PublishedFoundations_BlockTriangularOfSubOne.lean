-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T17:54:42.951281+00:00
-- url     : https://prove2.me/theorems/391203d4-9e02-444b-ba5f-b293d9faf4d1
-- title:
--   Block Triangular Of Sub One
-- statement:
--   Definitions and structural lemmas for Block Triangular Of Sub One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_mul
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
namespace GlobalTheory.FiniteGL
section Radical
variable (k : Type) [Field k] {N : ℕ}
def IsStrictBlock {k : Type} [Field k] (b : Fin N → ℕ) (X : Matrix (Fin N) (Fin N) k) : Prop :=
  ∀ i j, b j ≤ b i → X i j = 0
variable {k}
theorem IsStrictBlock.mul_blockTriangular {b : Fin N → ℕ} {X Y : Matrix (Fin N) (Fin N) k}
    (hX : IsStrictBlock b X) (hY : Y.BlockTriangular b) : IsStrictBlock b (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b l ≤ b i
  · rw [hX i l hl, zero_mul]
  · rw [hY (lt_of_le_of_lt hij (not_le.mp hl)), mul_zero]
theorem blockTriangular_of_sub_one {b : Fin N → ℕ} {X : Matrix (Fin N) (Fin N) k}
    (hX : IsStrictBlock b (X - 1)) : X.BlockTriangular b := by
  intro i j hij
  have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
  have h := hX i j hij.le
  rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h
variable (k)
def unipRadical (b : Fin N → ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {u | IsStrictBlock b ((u : Matrix (Fin N) (Fin N) k) - 1)}
  one_mem' := by
    intro i j _
    simp
  mul_mem' := by
    intro u v hu hv i j hij
    have e : ((u * v : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 =
        ((u : Matrix (Fin N) (Fin N) k) - 1) * (v : Matrix (Fin N) (Fin N) k) +
          ((v : Matrix (Fin N) (Fin N) k) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, Matrix.add_apply, (IsStrictBlock.mul_blockTriangular hu (blockTriangular_of_sub_one hv)) i j hij,
      hv i j hij, add_zero]
  inv_mem' := by
    intro u hu i j hij
    letI := u.invertible
    have hi : ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular b := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_of_sub_one hu)
    have e : ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 =
        -(((u : Matrix (Fin N) (Fin N) k) - 1) * ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) := by
      rw [sub_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, neg_sub]
    rw [e, Matrix.neg_apply, (IsStrictBlock.mul_blockTriangular hu hi) i j hij, neg_zero]
variable {k}
def IsCuspidal {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ b : Fin N → ℕ, Monotone b → (∃ i j, b i ≠ b j) →
    ∀ v : V, (∀ u ∈ unipRadical k b, ρ u v = v) → v = 0
def twoBlocks (N a : ℕ) : Fin N → ℕ := fun i => if (i : ℕ) < a then 0 else 1
end Radical
section Generic
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
def genericChar (ψ₀ : AddChar k ℂ) : uniSub k n →* ℂ where
  toFun u := ψ₀ (supd (((u : mirabSub k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
  map_one' := by
    rw [OneMemClass.coe_one, OneMemClass.coe_one, Units.val_one, supd_one, AddChar.map_zero_eq_one]
  map_mul' u v := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, supd_mul _ _ u.2 v.2, AddChar.map_add_eq_mul]
def genericLine (ψ₀ : AddChar k ℂ) : Representation ℂ (uniSub k n) ℂ :=
  (Algebra.lsmul ℂ ℂ ℂ).toMonoidHom.comp (genericChar n ψ₀)
abbrev MirabInducedSpace (ψ₀ : AddChar k ℂ) : Submodule ℂ (mirabSub k n → ℂ) :=
  Representation.coindV (uniSub k n).subtype (genericLine n ψ₀)
def mirabInduced (ψ₀ : AddChar k ℂ) : Representation ℂ (mirabSub k n) (MirabInducedSpace n ψ₀) :=
  Representation.coind (uniSub k n).subtype (genericLine n ψ₀)
def restrictMirab {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (n + 1)) k) V) :
    Representation ℂ (mirabSub k n) V :=
  ρ.comp (mirabSub k n).subtype
end Generic
section Examples
def lineRep {G : Type} [Group G] (χ : G →* ℂ) : Representation ℂ G (Fin 1 → ℂ) :=
  (Algebra.lsmul ℂ ℂ (Fin 1 → ℂ)).toMonoidHom.comp χ
def signGL₂ : GL (Fin 2) (ZMod 2) →* ℂ :=
  ((Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)).comp
    (Equiv.Perm.sign.comp (MulAction.toPermHom (GL (Fin 2) (ZMod 2)) (Fin 2 → ZMod 2)))
def transvGL₂ : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩
end Examples
end GlobalTheory.FiniteGL
namespace GlobalTheory.Published
open GlobalTheory.FiniteGL
def CuspidalExists : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n : ℕ),
    ∃ (d : ℕ) (ρ : Representation ℂ (GL (Fin (n + 1)) k) (Fin d → ℂ)), ρ.IsIrreducible ∧ IsCuspidal ρ
def CuspidalRestrictsToInduced : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (GL (Fin (n + 1)) k) V), ρ.IsIrreducible → IsCuspidal ρ →
      Nonempty ((restrictMirab n ρ).Equiv (mirabInduced n ψ₀))
def CuspidalMirabolic : Prop := CuspidalExists ∧ CuspidalRestrictsToInduced
end GlobalTheory.Published


