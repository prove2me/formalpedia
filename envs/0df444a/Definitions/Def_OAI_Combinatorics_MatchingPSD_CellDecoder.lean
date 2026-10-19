-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder
-- name    : OAI_Combinatorics_MatchingPSD_CellDecoder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:16:36.213921+00:00
-- url     : https://prove2.me/theorems/9193ec14-b255-41a8-9cbb-5cb661ba5ad9
-- title:
--   Local cut value of a cross vector
-- statement:
--   This file defines the affine function giving the slack of a local odd cut in terms of a cross vector.
--
--   For a bit $b\in\{\mathrm{false},\mathrm{true}\}$ and a point $x=(x_0,x_1,x_2)\in\mathbb{R}^3$,
--   $$
--   \operatorname{cut}_b(x)=\begin{cases}x_0+x_1-1, & b=\mathrm{false},\\ x_0+x_2-1, & b=\mathrm{true}.\end{cases}
--   $$
--
--   If $x=(e_{AB},e_{AC},e_{BC})$ is the cross vector of a matching of two blocks $A$, $B$ and a third block $C$ (the numbers of $A$–$B$, $A$–$C$ and $B$–$C$ edges), then the cut with side $A$ is crossed by $e_{AB}+e_{AC}$ edges and the cut with side $A\cup C$ by $e_{AB}+e_{BC}$ edges, so $\operatorname{cut}_b(x)$ is the crossing number minus one, i.e. the odd-cut slack of the side $A$ (for $b=\mathrm{false}$) or $A\cup C$ (for $b=\mathrm{true}$). At the five special points $(1,0,0)$, $(0,1,1)$, $(3,0,0)$, $(1,2,0)$, $(1,0,2)$ it takes the values $0,0,2,2,0$ for $b=\mathrm{false}$ and $0,0,2,0,2$ for $b=\mathrm{true}$. This pattern lets a single cell carry one bit: the two configurations $(1,2,0)$ and $(1,0,2)$ are separated by the two cuts, while $(3,0,0)$ has slack $2$ and $(0,1,1)$ has slack $0$ for both.
--
--   **Formalization Note** The Lean name is `cutValue b x = x 0 + x (if b then 2 else 1) - 1` with `b : Bool` and `x : Point`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/CellDecoder.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/CellDecoder.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells

namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

noncomputable def cutValue (b : Bool) (x : Point) : ℝ := x 0+x (if b then 2 else 1)-1

end MatchingInterpolation

end OAI


