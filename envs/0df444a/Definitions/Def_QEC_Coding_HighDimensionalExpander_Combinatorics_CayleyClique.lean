-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
-- name    : QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:57:11.870168+00:00
-- url     : https://prove2.me/theorems/97e29a85-0003-49f4-adfa-1564cd1f73f8
-- title:
--   Cayley Clique
-- statement:
--   Definitions and structural lemmas for Cayley Clique, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
def cliqueComplex (G : SimpleGraph V) : AbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ G.IsClique (s : Set V)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, hs.2.subset ?_⟩
    simpa using hts
  singleton_mem x := by
    simp
@[simp]
theorem mem_cliqueComplex_iff (G : SimpleGraph V) (s : Finset V) :
    s ∈ cliqueComplex G ↔ s.Nonempty ∧ G.IsClique (s : Set V) :=
  Iff.rfl
theorem map_mem_cliqueComplex_iff
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (s : Finset V) :
    s.map e.toEquiv.toEmbedding ∈ cliqueComplex H ↔ s ∈ cliqueComplex G := by
  simp only [mem_cliqueComplex_iff, Finset.map_nonempty]
  constructor
  · rintro ⟨hsne, hs⟩
    refine ⟨hsne, ?_⟩
    intro x hx y hy hxy
    apply e.map_adj_iff.mp
    exact hs (by simpa using hx) (by simpa using hy) (by simpa using hxy)
  · rintro ⟨hsne, hs⟩
    refine ⟨hsne, ?_⟩
    intro x hx y hy hxy
    have hxFinset : x ∈ s.map e.toEquiv.toEmbedding := hx
    have hyFinset : y ∈ s.map e.toEquiv.toEmbedding := hy
    obtain ⟨x', hx', hxeq⟩ := Finset.mem_map.mp hxFinset
    obtain ⟨y', hy', hyeq⟩ := Finset.mem_map.mp hyFinset
    have hxmem : e.symm x ∈ s := by
      simpa [← hxeq] using hx'
    have hymem : e.symm y ∈ s := by
      simpa [← hyeq] using hy'
    have hadj : H.Adj (e (e.symm x)) (e (e.symm y)) := by
      apply e.map_adj_iff.mpr
      apply hs hxmem hymem
      intro heq
      exact hxy (e.symm.injective heq)
    simpa using hadj
section Finite
variable [Fintype V] [DecidableEq V]
noncomputable def extensionVertices
    (K : AbstractSimplicialComplex V) (s : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun x => x ∉ s ∧ insert x s ∈ K
@[simp]
theorem mem_extensionVertices_iff
    (K : AbstractSimplicialComplex V) (s : Finset V) (x : V) :
    x ∈ extensionVertices K s ↔ x ∉ s ∧ insert x s ∈ K := by
  classical
  simp [extensionVertices]
noncomputable def neighborVertices (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun y => G.Adj x y
omit [DecidableEq V] in
@[simp]
theorem mem_neighborVertices_iff (G : SimpleGraph V) (x y : V) :
    y ∈ neighborVertices G x ↔ G.Adj x y := by
  classical
  simp [neighborVertices]
end Finite
section Cayley
variable {Γ : Type u} [Group Γ]
def cayleyCliqueComplex (S : Set Γ) : AbstractSimplicialComplex Γ :=
  cliqueComplex (SimpleGraph.mulCayley S)
@[simp]
theorem mem_cayleyCliqueComplex_iff (S : Set Γ) (s : Finset Γ) :
    s ∈ cayleyCliqueComplex S ↔
      s.Nonempty ∧ (SimpleGraph.mulCayley S).IsClique (s : Set Γ) :=
  Iff.rfl
def cayleyLeftIso (S : Set Γ) (a : Γ) :
    SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley S where
  toEquiv := Equiv.mulLeft a
  map_rel_iff' := by
    intro x y
    exact SimpleGraph.mulCayley_adj_mul_iff_right
@[simp]
theorem leftMul_mem_cayleyCliqueComplex_iff
    (S : Set Γ) (a : Γ) (s : Finset Γ) :
    s.map (Equiv.mulLeft a).toEmbedding ∈ cayleyCliqueComplex S ↔
      s ∈ cayleyCliqueComplex S :=
  map_mem_cliqueComplex_iff (cayleyLeftIso S a) s
section Finite
variable [Fintype Γ] [DecidableEq Γ]
def cayleyNeighborCandidates (S : Finset Γ) (x : Γ) : Finset Γ :=
  (S.image fun g => x * g) ∪ (S.image fun g => x * g⁻¹)
end Finite
end Cayley
section Schreier
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
def schreierGraph (S : Set Γ) : SimpleGraph X :=
  SimpleGraph.fromRel fun x y => ∃ g ∈ S, g • x = y
@[simp]
theorem schreierGraph_adj (S : Set Γ) (x y : X) :
    (schreierGraph S).Adj x y ↔
      x ≠ y ∧ (∃ g ∈ S, g • x = y) ∨ x ≠ y ∧ (∃ g ∈ S, g • y = x) := by
  simp only [schreierGraph, SimpleGraph.fromRel_adj]
  aesop
def schreierCliqueComplex (S : Set Γ) : AbstractSimplicialComplex X :=
  cliqueComplex (schreierGraph S)
@[simp]
theorem mem_schreierCliqueComplex_iff (S : Set Γ) (s : Finset X) :
    s ∈ schreierCliqueComplex S ↔ s.Nonempty ∧ (schreierGraph S).IsClique (s : Set X) :=
  Iff.rfl
def schreierIsoOfCommutes
    (S : Set Γ) (e : X ≃ X) (h : ∀ g ∈ S, ∀ x, e (g • x) = g • e x) :
    schreierGraph (X := X) S ≃g schreierGraph (X := X) S where
  toEquiv := e
  map_rel_iff' := by
    intro x y
    simp only [schreierGraph_adj]
    constructor
    · rintro (⟨hne, g, hg, hxy⟩ | ⟨hne, g, hg, hyx⟩)
      · left
        refine ⟨fun hxy' => hne (congrArg e hxy'), g, hg, ?_⟩
        apply e.injective
        simpa [h g hg x] using hxy
      · right
        refine ⟨fun hxy' => hne (congrArg e hxy'), g, hg, ?_⟩
        apply e.injective
        simpa [h g hg y] using hyx
    · rintro (⟨hne, g, hg, hxy⟩ | ⟨hne, g, hg, hyx⟩)
      · left
        refine ⟨e.injective.ne hne, g, hg, ?_⟩
        simpa [h g hg x] using congrArg e hxy
      · right
        refine ⟨e.injective.ne hne, g, hg, ?_⟩
        simpa [h g hg y] using congrArg e hyx
section Finite
variable [Fintype X] [DecidableEq X] [DecidableEq Γ]
def schreierNeighborCandidates (S : Finset Γ) (x : X) : Finset X :=
  (S.image fun g => g • x) ∪ (S.image fun g => g⁻¹ • x)
end Finite
end Schreier
end QEC.Coding.HighDimensionalExpander.CayleyClique


