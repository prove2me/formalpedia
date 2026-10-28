-- Prove2me | Definitions.Def_OAIB3Zr003
-- name    : OAIB3Zr003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T13:12:30.039253+00:00
-- url     : https://prove2.me/theorems/f993147a-6b57-41dc-865c-1212e7015bfe
-- title:
--   Definitions bundle OAIB3Zr003 of the split of OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 13 definitions. The definitions and types are `OAI.Zarankiewicz.finiteCrossingCount`, `OAI.Zarankiewicz.firstIntersectionParameter`, `OAI.Zarankiewicz.flattenBi`, `OAI.Zarankiewicz.lineAvoidancePolynomial`, `OAI.Zarankiewicz.monomialVector`, `OAI.Zarankiewicz.periodicPolygon`, `OAI.Zarankiewicz.rowCrossingCount`, `OAI.Zarankiewicz.secondIntersectionParameter`, `OAI.Zarankiewicz.similarityCoordinates`, `OAI.Zarankiewicz.swapBi`, `OAI.Zarankiewicz.triangleCoordEquiv`, `OAI.Zarankiewicz.triangleDiagonalWeight`, `OAI.Zarankiewicz.triangleMatrix`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Crossing_Bivariate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/Bivariate.lean), [`Crossing_FiniteIntersectionDrawing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/FiniteIntersectionDrawing.lean), [`Crossing_FiniteLineAvoidance`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/FiniteLineAvoidance.lean), [`Crossing_PeriodicPolygon`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/PeriodicPolygon.lean), [`Crossing_RowCrossingCount`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/RowCrossingCount.lean), [`Crossing_SegmentParameters`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/SegmentParameters.lean), [`Crossing_SimilarityCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/SimilarityCoordinates.lean), [`Crossing_TriangleFactorization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/TriangleFactorization.lean), [`Crossing_TwoTriangleBasis`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/TwoTriangleBasis.lean).
--
--   **Imports.** It imports the published bundle `Def_BipartiteCrossing`; the bundles `OAIB3Zr000` and `OAIB3Zr001` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.Zarankiewicz.finite_intersection_normalization`; the proofs of `OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation`, `OAI_Zarankiewicz_TruncatedSpokeCoordinates_closed_cycle_matrix_sum`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.diagonal_detector_isUnit`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius`, `OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_complete_edge_intersection_radius`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cycle_block_radius`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.odd_normalized_crossing_lower_bound`, `OAI.Zarankiewicz.VertexTruncation.exists_all_edge_shift_radius`, `OAI.Zarankiewicz.finite_intersection_normalization`, `OAI.Zarankiewicz.mainTarget_proof` and `OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse`.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr000
import Definitions.Def_OAIB3Zr001

section
-- module Solutions.OAIB3_Zar.Crossing_Bivariate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule

def flattenBi : BiPoly ≃ₗ[ℝ] (ℕ × ℕ →₀ ℝ) :=
  ((coeffLinearEquiv ℝ ℝ).trans
    (Finsupp.mapRange.linearEquiv (coeffLinearEquiv ℝ ℝ))).trans
    (Finsupp.curryLinearEquiv ℝ).symm

def swapBi : BiPoly ≃ₗ[ℝ] BiPoly :=
  (flattenBi.trans (Finsupp.mapDomain.linearEquiv ℝ ℝ (Equiv.prodComm ℕ ℕ))).trans
    flattenBi.symm

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteIntersectionDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def finiteCrossingCount {m n : ℕ} (D : FiniteIntersectionDrawing m n) : ℕ :=
  D.crossings_finite.toFinset.card

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteLineAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators Classical

def lineAvoidancePolynomial (z a v : Plane) : ℝ[X] :=
  C v.2 * X - C v.1 * X^2 + C (det2 (z-a) v)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PeriodicPolygon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def periodicPolygon (n : ℕ) (hn : 0 < n) (p : Fin n → Plane) (i : ℕ) : Plane := p (cyclicIndex n hn i)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RowCrossingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical
variable {m n : ℕ}

def rowCrossingCount (D : AdmissibleDrawing m n) (i k : Fin m) : ℕ :=
  ∑ p : Fin n, ∑ q : Fin n, (pairCrossings D (i,p) (k,q)).card

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def firstIntersectionParameter (a b c d : Plane) : ℝ :=
  det2 (d-c) (a-c) / det2 (b-a) (d-c)

def secondIntersectionParameter (a b c d : Plane) : ℝ :=
  -det2 (b-a) (c-a) / det2 (b-a) (d-c)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SimilarityCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def similarityCoordinates (o u x : Plane) : Plane :=
  (dot2 u (x-o)/squaredLength u,det2 u (x-o)/squaredLength u)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TwoTriangleBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators

def triangleCoordEquiv (s : ℕ) : BiExponent s ≃ TriangleIndex s :=
  Fintype.equivOfCardEq (by simp [BiExponent, TriangleIndex, card_twoTriangle])

def monomialVector (s : ℕ) (node : ℕ → ℝ) (p q : ℕ) : BiExponent s → ℝ :=
  fun ab => node p ^ ab.1.val * node q ^ ab.2.val

def triangleMatrix (s : ℕ) (node : ℕ → ℝ) : Matrix (BiExponent s) (BiExponent s) ℝ :=
  fun ab j => monomialVector s node (triangleCoordEquiv s j).val.1
    (triangleCoordEquiv s j).val.2 ab

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def triangleDiagonalWeight (s : ℕ) (node : OrderedNode s → ℝ) (j : BiExponent s) : ℝ :=
  let pq := triangleNodePair s (triangleCoordEquiv s j)
  triangleCoefficient s pq.1 pq.2 * detectorWeight node pq.1 pq.2

end Zarankiewicz

end

end OAI
end


