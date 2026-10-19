-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
-- name    : OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:47:39.397132+00:00
-- url     : https://prove2.me/theorems/a764b27d-d912-46c2-a050-9e303dc73354
-- title:
--   Matrices of independent variables on a prescribed support
-- statement:
--   Let $R$ be a commutative semiring, and let $m,n$ index rows and columns. Given a support relation on $m\times n$ and a labelling of positions by variables in $\sigma$, the supported variable matrix has entries
--   $$
--   M_{ij}=\begin{cases}X_{\ell(i,j)},&(i,j)\text{ in the support},\\0,&\text{otherwise},\end{cases}
--   $$
--   in the polynomial ring $R[X_s:s\in\sigma]$.
--
--   When distinct support positions carry distinct variables, every square minor indexed by a matching inside the support has nonzero determinant. So the generic rank is at least the size of any such matching. This is the Edmonds-type link between bipartite matchings and ranks of matrices with prescribed zero patterns.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/GenericRankMatching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRankMatching.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood

open MvPolynomial

variable {R σ m n κ β : Type*}

noncomputable def supportedVariableMatrix [CommSemiring R]
    (support : m → n → Prop) (label : m → n → σ) :
    Matrix m n (MvPolynomial σ R) := by
  classical
  exact fun i j => if support i j then X (label i j) else 0

end SeymourSecondNeighborhood

end OAI


