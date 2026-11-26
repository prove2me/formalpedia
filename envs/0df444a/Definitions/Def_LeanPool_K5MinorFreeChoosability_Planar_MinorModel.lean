-- Prove2me | Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
-- name    : LeanPool_K5MinorFreeChoosability_Planar_MinorModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:12:57.362904+00:00
-- url     : https://prove2.me/theorems/420dda8c-8cd6-4036-acb5-b4d5f7a0d1ce
-- title:
--   Minor Model
-- statement:
--   Definitions and structural lemmas for Minor Model, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorModel.lean

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_connSet_iff_induce_connected
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_connSet_singleton
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
attribute [local simp] LeanPool.K5MinorFreeChoosability.restrict_adj


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
variable {V W : Type*}
structure MinorModel (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Finset V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_connected : ∀ w, (G.induce (↑(branch w) : Set V)).Connected
  branch_disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  branch_adjacent : ∀ w w', H.Adj w w' → ∃ u ∈ branch w, ∃ v ∈ branch w', G.Adj u v
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel G H)
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)
instance : DecidableRel K33.Adj := fun u v =>
  decidable_of_iff ((u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft)) Iff.rfl
def K33MinorFree (G : SimpleGraph V) : Prop := ¬ IsMinor K33 G
variable {G : SimpleGraph V} {k : ℕ}
def CliqueMinorModel.toMinorModel (M : CliqueMinorModel G k) :
    MinorModel G (⊤ : SimpleGraph (Fin k)) where
  branch := M.branch
  branch_nonempty := M.branch_nonempty
  branch_connected := M.branch_connected
  branch_disjoint := M.branch_disjoint
  branch_adjacent i j h := M.branch_adjacent i j h
def MinorModel.toCliqueMinorModel (M : MinorModel G (⊤ : SimpleGraph (Fin k))) :
    CliqueMinorModel G k where
  branch := M.branch
  branch_nonempty := M.branch_nonempty
  branch_connected := M.branch_connected
  branch_disjoint := M.branch_disjoint
  branch_adjacent i j h := M.branch_adjacent i j h
def MinorModel.ofIso {H : SimpleGraph W} (e : H ≃g G) : MinorModel G H where
  branch w := {e w}
  branch_nonempty w := Finset.singleton_nonempty _
  branch_connected w := by
    rw [← connSet_iff_induce_connected]
    simpa using connSet_singleton G (e w)
  branch_disjoint w w' h := by
    simpa using fun h' => h (e.injective h')
  branch_adjacent w w' h := ⟨e w, by simp, e w', by simp, e.map_adj_iff.2 h⟩
namespace MinorModel
variable {H : SimpleGraph W} (M : MinorModel G H)
end MinorModel
end LeanPool.K5MinorFreeChoosability


