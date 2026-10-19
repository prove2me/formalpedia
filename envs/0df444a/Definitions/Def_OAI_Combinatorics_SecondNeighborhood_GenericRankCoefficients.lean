-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
-- name    : OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:55:56.966355+00:00
-- url     : https://prove2.me/theorems/a32712d6-2374-4aa2-8d4f-8ca8883c4ff4
-- title:
--   Coefficient variables and their selection on arcs
-- statement:
--   Let $r$ be a relation on a finite set $X$. The coefficient variables are two copies of $X\times X$, one for $a$ and one for $b$. For an assignment $v$ of real values to the variables, the selected coefficients are
--   $$
--   a_v(x,y)=\begin{cases}v(\text{first copy},(x,y)),&x\to y,\\0,&\text{otherwise},\end{cases}\qquad b_v(x,y)=\begin{cases}v(\text{second copy},(x,y)),&x\to y,\\0,&\text{otherwise}.\end{cases}
--   $$
--
--   These are coefficients supported on the arcs. Choosing $v$ generically gives coefficient matrices of maximal rank for all their relevant minors simultaneously.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/GenericRankCoefficients.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRankCoefficients.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {X τ : Type*} [Fintype X] [DecidableEq X] [Fintype τ]

abbrev CoefficientVariables (X : Type*) := Sum (X × X) (X × X)

noncomputable def selectedA (r : X → X → Prop)
    (v : CoefficientVariables X → ℝ) (x y : X) : ℝ := by
  classical
  exact if r x y then v (Sum.inl (x, y)) else 0

noncomputable def selectedB (r : X → X → Prop)
    (v : CoefficientVariables X → ℝ) (x y : X) : ℝ := by
  classical
  exact if r x y then v (Sum.inr (x, y)) else 0

end SeymourSecondNeighborhood.Pruning

end OAI


