-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_AffineSlacks
-- name    : OAI_Combinatorics_MatchingPSD_AffineSlacks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:00:15.616897+00:00
-- url     : https://prove2.me/theorems/df4c36b1-c79d-42b6-ab28-848b71380dfc
-- title:
--   The slack inequalities of the matching polytope as affine functions
-- statement:
--   For an even $n$, an edge is a pair $(u,v)$ of vertices of $\{0,\dots,n-1\}$ with $u<v$, and a perfect matching is a set of edges covering every vertex exactly once. The rows of the slack matrix are the edges $e$ and the odd cuts $U\subseteq\{0,\dots,n-1\}$ with $|U|$ odd. The slack of a matching $M$ is $[e\in M]$ for an edge row and $|\{e\in M:e\text{ crosses }U\}|-1$ for an odd-cut row.
--
--   For a row $i$ the affine function $\sigma_i:\mathbb{R}^{\text{edges}}\to\mathbb{R}$ is
--   $$
--   \sigma_e(x)=x_e,\qquad\sigma_U(x)=\sum_{e\text{ crosses }U}x_e-1 .
--   $$
--
--   These are the edge nonnegativity and odd-cut inequalities of Edmonds' description of the perfect matching polytope. At the indicator vector of a perfect matching they evaluate to its slacks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/AffineSlacks.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/AffineSlacks.lean by skeleton subtraction
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

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

noncomputable def slackAffine {n : ℕ} (i : Row n) : (Edge n → ℝ) →ᵃ[ℝ] ℝ := by
  classical
  cases i with
  | inl e => exact (LinearMap.proj e).toAffineMap
  | inr U =>
    exact (∑ e : Edge n, if Crosses U.1 e then LinearMap.proj e else 0).toAffineMap -
      AffineMap.const ℝ (Edge n → ℝ) 1

end PerfectMatchingPSD

end OAI


