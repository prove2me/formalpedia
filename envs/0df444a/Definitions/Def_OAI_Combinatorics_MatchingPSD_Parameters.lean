-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_Parameters
-- name    : OAI_Combinatorics_MatchingPSD_Parameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:26:31.062259+00:00
-- url     : https://prove2.me/theorems/163b569a-d1bf-4bbf-afb0-86b66fe58856
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

def blockSize (d t : ℕ) : ℕ := 4*(d+1)*t^4
def vertexSize (d t : ℕ) : ℕ := 2*blockSize d t*(t+2)+2

end PerfectMatchingPSD

end OAI


