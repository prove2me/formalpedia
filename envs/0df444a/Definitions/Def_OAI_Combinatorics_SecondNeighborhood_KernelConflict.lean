-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
-- name    : OAI_Combinatorics_SecondNeighborhood_KernelConflict
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:53:37.758997+00:00
-- url     : https://prove2.me/theorems/f214442c-ed56-452a-b0d6-6e3049b9eaa5
-- title:
--   Local maximal-rank condition for coefficient matrices
-- statement:
--   Let $r$ be a relation on a finite set $X$, let $R,C\subseteq X\times X$, and let $b:X\times X\to\mathbb{R}$. The coefficients $b$ have locally maximal ranks if, for every arc $p\to i$ and every matrix $D$ supported on the local support (positions $(s,j)\in C_i\times R_p$ with $s\to j$),
--   $$
--   \operatorname{rank}D\le\operatorname{rank}D^{(p,i)}_b,
--   $$
--   where $D^{(p,i)}_b$ is the local matrix $(b(s,j))_{s\in C_i,\,j\in R_p}$.
--
--   Generic coefficients achieve this. It is the condition under which kernel dimensions of the coefficient matrices can be computed combinatorially from matchings.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/KernelConflict.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/KernelConflict.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Matrix
open SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel

variable {X : Type*} [Fintype X] [DecidableEq X]

def LocalMaximalRanks (r : X → X → Prop) (R C : Finset (X × X))
    (b : X → X → ℝ) : Prop :=
  ∀ p i, r p i → ∀ D : Matrix (PairFiber C i) (PairFiber R p) ℝ,
    SupportedOn (localSupport r R C p i) D → D.rank ≤ (matrixD R C b p i).rank

end SeymourSecondNeighborhood.Pruning

end OAI


