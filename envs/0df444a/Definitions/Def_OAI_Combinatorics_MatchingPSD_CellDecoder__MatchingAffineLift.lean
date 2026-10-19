-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_CellDecoder__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:57:37.12683+00:00
-- url     : https://prove2.me/theorems/f8eb6d1d-2201-404c-86df-1b545feb2845
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
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells__MatchingAffineLift

namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

noncomputable def cutValue (b : Bool) (x : Point) : ℝ := x 0+x (if b then 2 else 1)-1

end MatchingInterpolation

end OAI


