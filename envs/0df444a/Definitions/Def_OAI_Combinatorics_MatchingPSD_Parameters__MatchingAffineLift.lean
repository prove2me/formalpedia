-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_Parameters__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_Parameters__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:11:15.135036+00:00
-- url     : https://prove2.me/theorems/9997ff35-bf2e-4e5e-9c20-91311132c223
-- title:
--   Block size and vertex count of the lower-bound construction
-- statement:
--   This file fixes the two size parameters of the global construction as functions of a degree bound $d$ and a cell count $t$.
--
--   For $d,t\in\mathbb{N}$:
--
--   1. **Block size.**
--   $$
--   \mathrm{bs}(d,t)=4(d+1)t^4 .
--   $$
--   2. **Vertex size.**
--   $$
--   \mathrm{vs}(d,t)=2\,\mathrm{bs}(d,t)\,(t+2)+2 .
--   $$
--
--   The global vertex set of the construction consists of two blocks of size $2s+1$ and $q$ cells of size $2s$, hence has $2s(q+2)+2$ vertices. With $s=\mathrm{bs}(d,t)$ and $q=t$ this number is exactly $\mathrm{vs}(d,t)$. The choice $s=4(d+1)t^4$ guarantees $s\ge t^4$ and $s\ge 2t^4d$, so that grids of spacing $2t^4$ and degree $d$ fit inside the blocks. In the final argument, for an even $n\ge\mathrm{vs}(d,t)$ the global vertex set is padded to $n$ vertices, and $t$ is chosen with $\mathrm{vs}(d,t)\le n<\mathrm{vs}(d,t+1)$, so that $n$ is polynomially bounded in $t$ while the lower bound obtained is exponential in $t$.
--
--   **Formalization Note** The Lean names are `blockSize d t` and `vertexSize d t`, both natural-number valued; the inequalities in the last paragraph are proved in separate lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Parameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Parameters.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AffineSlacks
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding__MatchingAffineLift

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

def blockSize (d t : ℕ) : ℕ := 4*(d+1)*t^4
def vertexSize (d t : ℕ) : ℕ := 2*blockSize d t*(t+2)+2

end PerfectMatchingPSD

end OAI


