-- Prove2me | Definitions.Def_RequestProject_Truncation
-- name    : RequestProject_Truncation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T12:26:23.794741+00:00
-- url     : https://prove2.me/theorems/d15d35e6-ca55-4098-a4e8-a7a36227480d
-- title:
--   Truncation
-- statement:
--   Definitions and structural lemmas for Truncation, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Truncation.lean

import Definitions.Def_RequestProject_Components
import Theorems.Thm_ChromaticReconstruction_compType_map_equiv
import Theorems.Thm_ChromaticReconstruction_edgeFinset_map_iso

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
def compCount (S : SimpleGraph V) (μ : Multiset ℕ) : ℕ :=
  (S.edgeFinset.powerset.filter fun F : Finset (Sym2 V) => compType (↑F : Set (Sym2 V)) = μ).card
lemma compCount_iso {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ≃g G') (μ : Multiset ℕ) :
    compCount G μ = compCount G' μ := by
  unfold compCount
  rw [edgeFinset_map_iso e]
  have h1 : ∀ x, e.toEquiv.symm (e x) = x := fun x => e.toEquiv.symm_apply_apply x
  have h2 : ∀ x, e (e.toEquiv.symm x) = x := fun x => e.toEquiv.apply_symm_apply x
  refine Finset.card_nbij' (fun A : Finset (Sym2 V) => A.map e.toEquiv.toEmbedding.sym2Map)
    (fun B : Finset (Sym2 W) => B.map e.toEquiv.symm.toEmbedding.sym2Map) ?_ ?_ ?_ ?_
  · intro A hA
    simp only [coe_filter, mem_powerset, Set.mem_setOf_eq] at hA ⊢
    refine ⟨Finset.map_subset_map.2 hA.1, ?_⟩
    rw [← hA.2, coe_map]
    exact compType_map_equiv e.toEquiv A
  · intro B hB
    simp only [coe_filter, mem_powerset, Set.mem_setOf_eq] at hB ⊢
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hz
      obtain ⟨x, hx, rfl⟩ := mem_map.1 (hB.1 hy)
      simpa [Sym2.map_map, h1] using hx
    · rw [← hB.2, coe_map]
      exact compType_map_equiv e.toEquiv.symm B
  · intro A _
    ext z; simp [Sym2.map_map, h1]
  · intro B _
    ext z; simp [Sym2.map_map, h2]
def truncation {k : ℕ} (t : ℕ) (S : SimpleGraph (Fin k)) :
    {μ : Nat.Partition k // k - t ≤ μ.parts.card} → ℕ :=
  fun μ => compCount S μ.1.parts
def treeSetoid (k : ℕ) : Setoid {S : SimpleGraph (Fin k) // S.IsTree} where
  r S S' := Nonempty (S.1 ≃g S'.1)
  iseqv := ⟨fun _ => ⟨SimpleGraph.Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨f.comp e⟩⟩
def TreeClass (k : ℕ) : Type := Quotient (treeSetoid k)
def truncationClass (k t : ℕ) :
    TreeClass k → ({μ : Nat.Partition k // k - t ≤ μ.parts.card} → ℕ) :=
  Quotient.lift (fun S => truncation t S.1) fun S S' ⟨e⟩ => by
    funext μ
    exact compCount_iso e _
def tau (k : ℕ) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : Function.Injective (truncationClass k t)), (t : ℕ∞)
def singletonFiberCount (k t : ℕ) : ℕ :=
  Nat.card {T : TreeClass k // truncationClass k t ⁻¹' {truncationClass k t T} = {T}}
end ChromaticReconstruction


