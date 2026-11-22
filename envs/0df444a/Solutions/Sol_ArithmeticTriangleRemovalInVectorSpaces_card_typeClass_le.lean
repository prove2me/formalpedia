-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.card_typeClass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:42.9098+00:00
-- url     : https://prove2.me/submissions/f4438337-4ff2-44e9-a974-765154583f9a

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_typeClass_nonempty
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.typeClass_nonempty
section
public section
open Finset Real
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {a b b' : Fin n → ℕ}
private lemma mem_typeClass : b ∈ typeClass a ↔ ∃ σ : Equiv.Perm (Fin n), a ∘ σ = b := by
  simp [typeClass]
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {a b b' : Fin n → ℕ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {p : ℕ} (ha : ∀ r, a r < p) : #(typeClass a) ≤ p ^ n := by
  have hsub : typeClass a ⊆ Fintype.piFinset fun _ ↦ range p := by
    intro b hb
    obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
    simp [ha]
  grw [card_le_card hsub]
  simp
end ArithmeticTriangleRemovalInVectorSpaces
