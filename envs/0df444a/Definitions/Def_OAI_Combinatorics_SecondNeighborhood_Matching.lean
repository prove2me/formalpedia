-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
-- name    : OAI_Combinatorics_SecondNeighborhood_Matching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:45:37.028089+00:00
-- url     : https://prove2.me/theorems/6b6b6398-7cf4-4a60-9762-f59f10ae80bd
-- title:
--   Matchings, maximum matchings and vertex covers in bipartite graphs
-- statement:
--   Let $L$ and $R$ be types and $E\subseteq L\times R$ a bipartite relation.
--
--   1. **Matching.** A finite set $M$ of edges of $E$ in which no two edges share a left endpoint or a right endpoint. The empty set is a matching.
--   2. **Maximum matching.** A matching of largest cardinality.
--   3. **Vertex cover.** Sets $A\subseteq L$ and $B\subseteq R$ such that every edge $(l,r)\in E$ has $l\in A$ or $r\in B$.
--   4. **Matched vertices.** The sets of left and right endpoints of $M$.
--
--   These are the objects of König's theorem, $\max|M|=\min(|A|+|B|)$, which supplies the matching-based deletion bounds in the pruning lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/Matching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/Matching.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SeymourSecondNeighborhood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions

namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*}

def IsMatching (E : L → R → Prop) (M : Finset (L × R)) : Prop :=
  (∀ e ∈ M, E e.1 e.2) ∧
    Set.InjOn Prod.fst (M : Set (L × R)) ∧
    Set.InjOn Prod.snd (M : Set (L × R))

def IsMaximumMatching (E : L → R → Prop) (M : Finset (L × R)) : Prop :=
  IsMatching E M ∧ ∀ N, IsMatching E N → N.card ≤ M.card

def IsVertexCover (E : L → R → Prop) (A : Finset L) (B : Finset R) : Prop :=
  ∀ l r, E l r → l ∈ A ∨ r ∈ B

@[simp] theorem isMatching_empty (E : L → R → Prop) :
    IsMatching E ∅ := by
  simp [IsMatching, Set.InjOn]

section DecidableEq

variable [DecidableEq L] [DecidableEq R]

def leftVertices (M : Finset (L × R)) : Finset L := M.image Prod.fst

def rightVertices (M : Finset (L × R)) : Finset R := M.image Prod.snd

omit [DecidableEq R] in
@[simp] theorem mem_leftVertices {M : Finset (L × R)} {l : L} :
    l ∈ leftVertices M ↔ ∃ r, (l, r) ∈ M := by
  simp only [leftVertices, Finset.mem_image]
  constructor
  · rintro ⟨⟨k, r⟩, hkr, hkl⟩
    cases hkl
    exact ⟨r, hkr⟩
  · rintro ⟨r, hr⟩
    exact ⟨(l, r), hr, rfl⟩

omit [DecidableEq L] in
@[simp] theorem mem_rightVertices {M : Finset (L × R)} {r : R} :
    r ∈ rightVertices M ↔ ∃ l, (l, r) ∈ M := by
  simp only [rightVertices, Finset.mem_image]
  constructor
  · rintro ⟨⟨l, s⟩, hls, hsr⟩
    cases hsr
    exact ⟨l, hls⟩
  · rintro ⟨l, hl⟩
    exact ⟨(l, r), hl, rfl⟩

end DecidableEq

section Finite

variable [Fintype L] [Fintype R]

end Finite

end SeymourSecondNeighborhood.Bipartite

end OAI


