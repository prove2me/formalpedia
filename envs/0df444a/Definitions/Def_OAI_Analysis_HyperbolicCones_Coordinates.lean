-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
-- name    : OAI_Analysis_HyperbolicCones_Coordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:53:38.232764+00:00
-- url     : https://prove2.me/theorems/cb36a10c-2260-4aaa-851d-f201fb4d58b9
-- title:
--   Upper-triangular coordinates identify symmetric $4\times4$ matrices with $\mathbb{R}^{10}$
-- statement:
--   Let $\mathrm{Sym}_4$ be the real vector space of symmetric real $4\times4$ matrices, with rows and columns indexed by $\{0,1,2,3\}$. Let $\mathcal I=\{(i,j): 0\le i\le j\le3\}$ be the set of the $10$ upper-triangular index pairs. For $v\in\mathbb{R}^{\mathcal I}$, let $S(v)$ be the $4\times4$ matrix with
--   $$
--   S(v)_{ij}=\begin{cases}v_{(i,j)}, & i\le j,\\ v_{(j,i)}, & i>j.\end{cases}
--   $$
--
--   The file contains two items.
--
--   1. **Symmetry.** For every $v\in\mathbb{R}^{\mathcal I}$, the matrix $S(v)$ is symmetric.
--   2. **Coordinate isomorphism.** The map $\mathrm{Sym}_4\to\mathbb{R}^{\mathcal I}$, $X\mapsto(X_{ij})_{(i,j)\in\mathcal I}$, is a linear isomorphism, with inverse $v\mapsto S(v)$.
--
--   The polynomial of the main theorem is a polynomial in $23=10+10+3$ real coordinates: the upper-triangular entries of two symmetric matrices $X,Z$ and the three entries of $y\in\mathbb{R}^3$. It is formed by substituting $S(\cdot)$ of the coordinate variables for $X$ and $Z$. The isomorphism translates between the matrix description and this coordinate description. It is used, for example, for the dimension count and to evaluate the polynomial at points given as triples of matrices and a vector.
--
--   **Formalization Note** The index set $\mathcal I$ is the subtype `SymIndex` of `Fin 4 × Fin 4`, and `S` is the base definition `symmetricCoordinates`. The two items are `symmetricCoordinates_isHermitian` and the linear equivalence `symmetricCoordinateEquiv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/Coordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/Coordinates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit

namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

theorem symmetricCoordinates_isHermitian (v : SymIndex → ℝ) :
    (symmetricCoordinates v).IsHermitian := by
  change (symmetricCoordinates v)ᴴ = symmetricCoordinates v
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have h : i = j := le_antisymm hij hji
      subst j
      rfl
    · simp [symmetricCoordinates, hij, hji]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    simp [symmetricCoordinates, hij, hji]

def symmetricCoordinateEquiv : Sym 4 ≃ₗ[ℝ] (SymIndex → ℝ) where
  toFun X ij := (X : Mat 4 ℝ) ij.val.1 ij.val.2
  invFun v := ⟨symmetricCoordinates v, symmetricCoordinates_isHermitian v⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    by_cases h : i ≤ j
    · simp [symmetricCoordinates, h]
    · have hX : (X : Mat 4 ℝ).IsHermitian := X.property
      simpa [symmetricCoordinates, h] using hX.apply i j
  right_inv v := by
    funext ij
    simp [symmetricCoordinates, ij.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Paper256

end

end OAI


