-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCompatibility
-- name    : OAI_Combinatorics_SecondNeighborhood_ExtremalCompatibility
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:02:38.579886+00:00
-- url     : https://prove2.me/theorems/17336570-9c3d-4113-96ee-64d8cbdd126d
-- title:
--   Admissible pairs of pair sets and their candidate extensions
-- statement:
--   Let $r$ be a relation on a finite set $V$ and let $P,Q\subseteq V\times V$ be sets of pairs. $(P,Q)$ is compatible (conflict-free) if there are no $a\in P$, $b\in Q$ with $a_1\to b_1$ and $b_2\to a_2$. The left image of $P$ is $\{z:\exists p,\ (p,z_2)\in P,\ p\to z_1\}$, and the right image of $Q$ is $\{z:\exists s,\ (z_1,s)\in Q,\ s\to z_2\}$.
--
--   1. **Admissible.** $(P,Q)$ is compatible and both $P$ and $Q$ contain the diagonal $\{(v,v)\}$.
--   2. **Candidates.** The left candidates for $Q$ are the pairs outside the right image of the right image of $Q$. The right candidates for $P$ are the pairs outside the left image of the left image of $P$.
--   3. **Uncovered pairs.** The pairs in neither the left image of $P$ nor the right image of $Q$.
--
--   The final argument starts from an admissible configuration that maximizes a counting objective and prunes its candidate sets to obtain another admissible configuration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/ExtremalCompatibility.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/ExtremalCompatibility.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalImages

namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

abbrev Compatible (r : V → V → Prop) (P Q : Finset (V × V)) : Prop :=
  ConflictFree r P Q

structure Admissible (r : V → V → Prop) (P Q : Finset (V × V)) : Prop where
  compatible : Compatible r P Q
  diagonal_left : diagonal ⊆ P
  diagonal_right : diagonal ⊆ Q

def leftCandidate (r : V → V → Prop) (Q : Finset (V × V)) : Finset (V × V) :=
  Finset.univ \ rightImage r (rightImage r Q)

def rightCandidate (r : V → V → Prop) (P : Finset (V × V)) : Finset (V × V) :=
  Finset.univ \ leftImage r (leftImage r P)

def uncovered (r : V → V → Prop) (P Q : Finset (V × V)) : Finset (V × V) :=
  Finset.univ \ (leftImage r P ∪ rightImage r Q)

@[simp] theorem mem_leftCandidate {r : V → V → Prop} {Q : Finset (V × V)}
    {z : V × V} : z ∈ leftCandidate r Q ↔ z ∉ rightImage r (rightImage r Q) := by
  classical
  simp [leftCandidate]

@[simp] theorem mem_rightCandidate {r : V → V → Prop} {P : Finset (V × V)}
    {z : V × V} : z ∈ rightCandidate r P ↔ z ∉ leftImage r (leftImage r P) := by
  classical
  simp [rightCandidate]

@[simp] theorem mem_uncovered {r : V → V → Prop} {P Q : Finset (V × V)}
    {z : V × V} : z ∈ uncovered r P Q ↔ ¬ Covered r P Q z := by
  classical
  simp [uncovered, Covered]

end
end SeymourSecondNeighborhood.Extremal

end OAI


