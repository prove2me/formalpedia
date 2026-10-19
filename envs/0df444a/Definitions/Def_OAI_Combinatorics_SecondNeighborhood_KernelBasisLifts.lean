-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
-- name    : OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:59:52.524363+00:00
-- url     : https://prove2.me/theorems/d407ed2c-5355-4aeb-b2fa-cde6c385a8dd
-- title:
--   Lifting coordinate vectors into the kernel using a column cover
-- statement:
--   Let $F$ be a field, $M$ an $I\times J$ matrix over $F$, and $\mathrm{col}:\kappa\to J$ a selection of columns. Suppose the selected columns span the image of $M$: for every $x\in F^J$ there is $y\in F^\kappa$ with
--   $$
--   Mx=M_{\mathrm{col}}\,y .
--   $$
--
--   1. **Extension.** For $y\in F^\kappa$, the vector $\sum_ky_k\,e_{\mathrm{col}(k)}\in F^J$ places the coordinates of $y$ at the selected columns.
--   2. **Lift coefficients.** For each $j\in J$, a chosen $y^{(j)}\in F^\kappa$ with $Me_j=M_{\mathrm{col}}y^{(j)}$.
--   3. **Kernel lift.** $k_j=e_j-\sum_ky^{(j)}_k\,e_{\mathrm{col}(k)}$, which lies in the kernel of $M$.
--
--   The vectors $k_j$ for unselected $j$ form a kernel basis adapted to a column cover. This is how kernel vectors with controlled supports are produced in the pruning argument.
--
--   **Formalization Note** The lift coefficients are chosen with `Classical.choose`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/KernelBasisLifts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/KernelBasisLifts.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open scoped BigOperators Matrix

variable {I J F κ E : Type*}
variable [Fintype J] [Fintype κ] [DecidableEq J] [Field F]

def extendSelected (col : κ → J) (y : κ → F) : J → F :=
  ∑ k, Pi.single (col k) (y k)

noncomputable def liftCoefficients (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j : J) : κ → F :=
  Classical.choose (cover (Pi.single j 1))

noncomputable def kernelLift (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j : J) : J → F :=
  Pi.single j 1 - extendSelected col (liftCoefficients M col cover j)

end SeymourSecondNeighborhood.Pruning

end OAI


