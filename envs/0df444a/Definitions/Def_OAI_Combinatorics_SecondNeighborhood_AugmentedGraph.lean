-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
-- name    : OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:46:17.16378+00:00
-- url     : https://prove2.me/theorems/48d9f296-59a3-4993-8462-e0e3ef30f178
-- title:
--   The augmented bipartite conflict–cover graph of a pruning instance
-- statement:
--   Let $r$ be a relation on a finite set $V$. Consider finite sets $R,C\subseteq V\times V$ of pairs. A pair $a\in R$ and a pair $b\in C$ conflict if $a_1\to b_1$ and $b_2\to a_2$. A pair $a\in R$ left-covers $z$ if $a_2=z_2$ and $a_1\to z_1$, and $b\in C$ right-covers $z$ if $b_1=z_1$ and $b_2\to z_2$. $Z(R,C)$ is the set of pairs $z$ that are both left-covered by some element of $R$ and right-covered by some element of $C$.
--
--   1. **Vertices.** The left side is the disjoint union $R\sqcup Z(R,C)$ and the right side is $C\sqcup Z(R,C)$.
--   2. **Edges.** Edges join:
--      - $a\in R$ to $b\in C$ when they conflict;
--      - $a\in R$ to $z\in Z$ (right copy) when $a$ left-covers $z$;
--      - $z\in Z$ (left copy) to $b\in C$ when $b$ right-covers $z$.
--
--      There are no edges between the two copies of $Z$. The three edge types are the original, $\alpha$- and $\beta$-relations.
--   3. **Lifts and edge classes.** Each edge of the three relations lifts to an edge of the augmented graph. For a set $M$ of augmented edges, the original, $\alpha$- and $\beta$-edges of $M$ are the edges of each type whose lift lies in $M$.
--
--   A maximum matching and minimum vertex cover of this augmented graph determine which elements of $R$ and $C$ to delete in the pruning lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev LeftVertex (r : V → V → Prop) (R C : Finset (V × V)) :=
  ↥R ⊕ ↥(Z r R C)

abbrev RightVertex (r : V → V → Prop) (R C : Finset (V × V)) :=
  ↥C ⊕ ↥(Z r R C)

def AugmentedEdge (r : V → V → Prop) (R C : Finset (V × V)) :
    LeftVertex r R C → RightVertex r R C → Prop
  | Sum.inl a, Sum.inl b => Conflict r a.val b.val
  | Sum.inl a, Sum.inr z => LeftCovers r a.val z.val
  | Sum.inr z, Sum.inl b => RightCovers r b.val z.val
  | Sum.inr _, Sum.inr _ => False

def OriginalRelation (r : V → V → Prop) (R C : Finset (V × V))
    (a : R) (b : C) : Prop := Conflict r a.val b.val

def AlphaRelation (r : V → V → Prop) (R C : Finset (V × V))
    (z : Z r R C) (a : R) : Prop := LeftCovers r a.val z.val

def BetaRelation (r : V → V → Prop) (R C : Finset (V × V))
    (z : Z r R C) (b : C) : Prop := RightCovers r b.val z.val

variable {r : V → V → Prop} {R C : Finset (V × V)}

def originalLift (e : ↥R × ↥C) : LeftVertex r R C × RightVertex r R C :=
  (Sum.inl e.1, Sum.inl e.2)

def alphaLift (e : ↥(Z r R C) × ↥R) :
    LeftVertex r R C × RightVertex r R C :=
  (Sum.inl e.2, Sum.inr e.1)

def betaLift (e : ↥(Z r R C) × ↥C) :
    LeftVertex r R C × RightVertex r R C :=
  (Sum.inr e.1, Sum.inl e.2)

noncomputable def originalEdges
    (M : Finset (LeftVertex r R C × RightVertex r R C)) : Finset (↥R × ↥C) := by
  classical
  exact Finset.univ.filter (fun e => originalLift e ∈ M)

noncomputable def alphaEdges
    (M : Finset (LeftVertex r R C × RightVertex r R C)) :
    Finset (↥(Z r R C) × ↥R) := by
  classical
  exact Finset.univ.filter (fun e => alphaLift e ∈ M)

noncomputable def betaEdges
    (M : Finset (LeftVertex r R C × RightVertex r R C)) :
    Finset (↥(Z r R C) × ↥C) := by
  classical
  exact Finset.univ.filter (fun e => betaLift e ∈ M)

@[simp] theorem mem_originalEdges
    {M : Finset (LeftVertex r R C × RightVertex r R C)} {e : ↥R × ↥C} :
    e ∈ originalEdges M ↔ originalLift e ∈ M := by
  classical
  simp [originalEdges]

@[simp] theorem mem_alphaEdges
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    {e : ↥(Z r R C) × ↥R} : e ∈ alphaEdges M ↔ alphaLift e ∈ M := by
  classical
  simp [alphaEdges]

@[simp] theorem mem_betaEdges
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    {e : ↥(Z r R C) × ↥C} : e ∈ betaEdges M ↔ betaLift e ∈ M := by
  classical
  simp [betaEdges]

end SeymourSecondNeighborhood.Pruning

end OAI


