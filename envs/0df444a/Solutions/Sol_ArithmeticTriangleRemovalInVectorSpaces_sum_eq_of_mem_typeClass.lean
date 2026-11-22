-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.sum_eq_of_mem_typeClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:42.283804+00:00
-- url     : https://prove2.me/submissions/835cbda4-23b1-4e07-b5cd-39909e90b524

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
theorem _root_.solution (hb : b ∈ typeClass a) : ∑ r, b r = ∑ r, a r := by
  obtain ⟨τ, rfl⟩ := mem_typeClass.1 hb
  exact Equiv.sum_comp τ a
end ArithmeticTriangleRemovalInVectorSpaces
