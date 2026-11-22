-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.comp_mem_typeClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:41.133133+00:00
-- url     : https://prove2.me/submissions/c5a5f384-3969-4d2e-8f8c-c2d0db89b6a0

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
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
theorem _root_.solution (hb : b ∈ typeClass a) (σ : Equiv.Perm (Fin n)) :
    b ∘ σ ∈ typeClass a := by
  obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
  exact mem_typeClass.2 ⟨τ * σ, rfl⟩
end ArithmeticTriangleRemovalInVectorSpaces
