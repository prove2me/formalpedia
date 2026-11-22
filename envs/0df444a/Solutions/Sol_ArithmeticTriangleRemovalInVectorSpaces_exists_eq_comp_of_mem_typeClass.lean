-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.exists_eq_comp_of_mem_typeClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:41.73393+00:00
-- url     : https://prove2.me/submissions/f116840f-0e32-454d-a010-181553c6d2fb

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
theorem _root_.solution (hb : b ∈ typeClass a) (hb' : b' ∈ typeClass a) :
    ∃ σ : Equiv.Perm (Fin n), b' = b ∘ σ := by
  obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
  obtain ⟨τ', rfl⟩ := mem_typeClass.1 hb'
  refine ⟨τ⁻¹ * τ', ?_⟩
  ext r
  simp
end ArithmeticTriangleRemovalInVectorSpaces
