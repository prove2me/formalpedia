-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCounting
-- name    : OAI_Combinatorics_SecondNeighborhood_ExtremalCounting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:04:14.535493+00:00
-- url     : https://prove2.me/theorems/64d1366f-a09d-4f3c-bb1d-051da873381f
-- title:
--   The counting objective $|P|+|Q|+\#\text{uncovered}$
-- statement:
--   Let $r$ be a relation on a finite set $V$ and let $P,Q\subseteq V\times V$ be sets of pairs. $(P,Q)$ is compatible (conflict-free) if there are no $a\in P$, $b\in Q$ with $a_1\to b_1$ and $b_2\to a_2$. The left image of $P$ is $\{z:\exists p,\ (p,z_2)\in P,\ p\to z_1\}$, and the right image of $Q$ is $\{z:\exists s,\ (z_1,s)\in Q,\ s\to z_2\}$. Define
--   $$
--   u(P,Q)=\bigl|\,(V\times V)\setminus\bigl(\mathrm{left}(P)\cup\mathrm{right}(Q)\bigr)\bigr|,\qquad \Omega(P,Q)=|P|+|Q|+u(P,Q).
--   $$
--
--   $\Omega$ balances the sizes of the pair sets against how many pairs they leave uncovered. The final argument takes an admissible configuration maximizing $\Omega$ and, under strict subset growth, produces an admissible configuration with larger $\Omega$, a contradiction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/ExtremalCounting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/ExtremalCounting.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCompatibility

namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

def uncoveredCount (r : V → V → Prop) (P Q : Finset (V × V)) : ℕ :=
  (Finset.univ \ (leftImage r P ∪ rightImage r Q)).card

def objective (r : V → V → Prop) (P Q : Finset (V × V)) : ℕ :=
  P.card + Q.card + uncoveredCount r P Q

end

end SeymourSecondNeighborhood.Extremal

end OAI


