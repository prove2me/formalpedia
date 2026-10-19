-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
-- name    : OAI_Combinatorics_SecondNeighborhood_KernelRestriction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:52:06.822744+00:00
-- url     : https://prove2.me/theorems/cd83e4ed-89cf-4bb2-bbdf-09017a711233
-- title:
--   Fibres of a pair set and the local coefficient matrices
-- statement:
--   Let $X$ be a finite set, $P\subseteq X\times X$, and $p\in X$.
--
--   1. **Fibre.** $P_p=\{j:(p,j)\in P\}$, with the inclusion $j\mapsto(p,j)$ into $P$, and the restriction of a vector $u\in\mathbb{R}^P$ to the fibre.
--   2. **Local matrix.** For pair sets $R,C$, a coefficient function $b$ and $p,i\in X$, the matrix $D^{(p,i)}$ with rows indexed by $C_i$ and columns by $R_p$, given by $D^{(p,i)}_{s,j}=b(s,j)$.
--   3. **Local support.** The set of positions $(s,j)\in C_i\times R_p$ with $s\to j$.
--
--   These local matrices describe how the coefficient matrices act between the fibres over a single arc $p\to i$. Local rank conditions are imposed on them.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/KernelRestriction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/KernelRestriction.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Matrix
open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev PairFiber (P : Finset (X × X)) (p : X) := {j : X // (p, j) ∈ P}

def fiberIndex (P : Finset (X × X)) (p : X) (j : PairFiber P p) : ↥P :=
  ⟨(p, j.1), j.2⟩

def restrictFiber (P : Finset (X × X)) (p : X) (u : ↥P → ℝ) :
    PairFiber P p → ℝ :=
  fun j => u (fiberIndex P p j)

def matrixD (R C : Finset (X × X)) (b : X → X → ℝ) (p i : X) :
    Matrix (PairFiber C i) (PairFiber R p) ℝ :=
  fun s j => b s.1 j.1

def localSupport (r : X → X → Prop) (R C : Finset (X × X)) (p i : X) :
    Set (PairFiber C i × PairFiber R p) :=
  {q | r q.1.1 q.2.1}

end SeymourSecondNeighborhood.Pruning

end OAI


