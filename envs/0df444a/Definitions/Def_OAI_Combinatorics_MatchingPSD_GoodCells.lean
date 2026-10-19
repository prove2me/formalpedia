-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells
-- name    : OAI_Combinatorics_MatchingPSD_GoodCells
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:15:31.539093+00:00
-- url     : https://prove2.me/theorems/eecf87a8-80ef-4f85-8816-0a114e3bffe0
-- title:
--   Sample points: five special cross vectors together with a scaled grid
-- statement:
--   This file indexes the finite set of points at which cell matrices are compared with polynomials.
--
--   **Setting.** Points are elements of $\mathbb{R}^3$, with base point and directions $o=(1,0,0)$, $a=(0,2,0)$, $b=(0,0,2)$, $\star=(2,0,0)$ and $p=(-1,1,1)$. The five special points are $z_0=o$, $z_1=o+p$, $z_2=o+\star$, $z_3=o+a$, $z_4=o+b$, and for $L\in\mathbb{R}$ and a grid index $g\in\{0,\dots,d\}^3$ the scaled grid node is $o+Lg=(1+Lg_0,Lg_1,Lg_2)$.
--
--   1. **Sample indices.** $\mathcal S_d=\{0,1,2,3,4\}\sqcup\{0,\dots,d\}^3$, a set with $5+(d+1)^3$ elements.
--   2. **Sample points.** For $L\in\mathbb{R}$, the map $\mathcal S_d\to\mathbb{R}^3$ given by
--   $$
--   j\mapsto z_j\quad (j\in\{0,\dots,4\}),\qquad g\mapsto o+Lg\quad\bigl(g\in\{0,\dots,d\}^3\bigr).
--   $$
--
--   In the lower-bound argument $L=2l$ for a positive integer $l$, and when the blocks are large enough (block parameter $s\ge1$ and $2ld\le s$) every sample point is the cross vector of an actual local matching. After a suitable relabelling, the cell matrices of a factorisation are approximated entrywise by polynomials of total degree at most $d$ simultaneously at all sample points, and the interpolation identity then transfers the information from the grid nodes to the five special points.
--
--   **Formalization Note** `SampleIndex d` is `Fin 5 ⊕ GridIndex d` and `samplePoint d L = Sum.elim specialPoint (scaledNode L)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/GoodCells.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/GoodCells.lean by skeleton subtraction
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

namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev SampleIndex (d : ℕ) := Fin 5 ⊕ GridIndex d
noncomputable def samplePoint (d : ℕ) (L : ℝ) : SampleIndex d → Point :=
  Sum.elim specialPoint (scaledNode L)

end MatchingInterpolation

end OAI


