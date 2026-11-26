-- Prove2me | Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
-- name    : LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:18:24.442437+00:00
-- url     : https://prove2.me/theorems/f5599dc4-d711-4b97-a641-52ede7047aee
-- title:
--   Minor Closed
-- statement:
--   Definitions and structural lemmas for Minor Closed, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
namespace MinorModel
variable (M : MinorModel G H)
def SameBranch (u v : V) : Prop := u = v ∨ ∃ w, u ∈ M.branch w ∧ v ∈ M.branch w
theorem SameBranch.symm {M : MinorModel G H} {u v : V} (h : M.SameBranch u v) :
    M.SameBranch v u := by
  rcases h with rfl | ⟨w, hu, hv⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨w, hv, hu⟩
def Internal (z : G.Dart) : Prop := ∃ w, z.fst ∈ M.branch w ∧ z.snd ∈ M.branch w
end MinorModel
section Reduction
variable (M : MinorModel G H) (inK : G.Dart → Prop)
structure RedInv (A : Finset G.Dart) (σ α : Perm G.Dart) (r : V → V) : Prop where
  fix_out : ∀ z, z ∉ A → σ z = z ∧ α z = z
  symm_mem : ∀ z ∈ A, z.symm ∈ A
  α_eq : ∀ z ∈ A, α z = z.symm
  r_rot : ∀ z, r (σ z).fst = r z.fst
  cyc : ∀ z ∈ A, ∀ w ∈ A, r z.fst = r w.fst → SameCycle σ z w
  r_inj : ∀ u v, r u = r v → M.SameBranch u v
  internal : ∀ z, z ∉ A → M.Internal z → r z.fst = r z.snd
  K_sub : ∀ z, inK z → z ∈ A
variable {M inK}
variable [DecidableEq V]
end Reduction
end LeanPool.K5MinorFreeChoosability


