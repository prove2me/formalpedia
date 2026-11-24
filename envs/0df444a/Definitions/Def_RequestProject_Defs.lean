-- Prove2me | Definitions.Def_RequestProject_Defs
-- name    : RequestProject_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:47:17.498649+00:00
-- url     : https://prove2.me/theorems/ce0ac912-0bc3-4f00-8f0f-94dcdd967863
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Defs.lean

import Mathlib
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
section Components
variable {V : Type*} [Fintype V]
def compSets (A : Set (Sym2 V)) : Finset (Finset V) :=
  univ.image fun v => univ.filter fun w => (SimpleGraph.fromEdgeSet A).Reachable v w
def compType (A : Set (Sym2 V)) : Multiset ℕ :=
  (compSets A).val.map Finset.card
def typeMonomial (A : Set (Sym2 V)) : MvPolynomial ℕ ℚ :=
  ∏ C ∈ compSets A, X C.card
def chromSymm (G : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  ∑ A ∈ G.edgeFinset.powerset, (-1) ^ A.card * typeMonomial (A : Set (Sym2 V))
end Components
def killP1 : MvPolynomial ℕ ℚ →ₐ[ℚ] MvPolynomial ℕ ℚ :=
  aeval fun r => if r = 1 then 0 else X r
def phi {V : Type*} [Fintype V] (G : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  killP1 (pderiv 1 (chromSymm G))
section Trees
variable {V : Type*} [Fintype V]
def IsLeaf (G : SimpleGraph V) (v : V) : Prop := G.degree v = 1
def IsProperTree (G : SimpleGraph V) : Prop :=
  G.IsTree ∧ 3 ≤ Fintype.card V ∧ ∀ v, ¬ IsLeaf G v → ∃ u, G.Adj v u ∧ IsLeaf G u
abbrev SkelVert (G : SimpleGraph V) := {v : V // ¬ IsLeaf G v}
def skeleton (G : SimpleGraph V) : SimpleGraph (SkelVert G) :=
  G.induce {v | ¬ IsLeaf G v}
def skelWeight (G : SimpleGraph V) (c : SkelVert G) : ℕ :=
  1 + (univ.filter fun u => G.Adj c.1 u ∧ IsLeaf G u).card
def MultiplicityIsolated (G : SimpleGraph V) : Prop :=
  ∀ u v : SkelVert G, u ≠ v → skelWeight G u = skelWeight G v →
    (skeleton G).degree u = 1 ∧ (skeleton G).degree v = 1
end Trees
section LeafExt
variable {K : Type*}
def leafExtAdj (S : SimpleGraph K) (m : K → ℕ) :
    K ⊕ (Σ i, Fin (m i)) → K ⊕ (Σ i, Fin (m i)) → Prop
  | .inl i, .inl j => S.Adj i j
  | .inl i, .inr l => l.1 = i
  | .inr l, .inl i => l.1 = i
  | .inr _, .inr _ => False
def leafExt (S : SimpleGraph K) (m : K → ℕ) : SimpleGraph (K ⊕ (Σ i, Fin (m i))) where
  Adj := leafExtAdj S m
  symm := ⟨by
    intro x y h
    rcases x with i | ⟨i, a⟩ <;> rcases y with j | ⟨j, b⟩ <;>
      simp_all [leafExtAdj, S.adj_comm]⟩
  loopless := ⟨by
    intro x h
    rcases x with i | ⟨i, a⟩ <;> simp_all [leafExtAdj]⟩
def uniformLeafExt {V : Type*} (q : ℕ) (G : SimpleGraph V) :
    SimpleGraph (V ⊕ (Σ _ : V, Fin (q - 1))) :=
  leafExt G fun _ => q - 1
end LeafExt
end ChromaticReconstruction


