-- Prove2me | Definitions.Def_OAIB3Zr004
-- name    : OAIB3Zr004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T13:15:30.151978+00:00
-- url     : https://prove2.me/theorems/d2d35654-c568-4e40-b92f-7824426eb961
-- title:
--   Definitions bundle OAIB3Zr004 of the split of OpenAI, The crossing number of complete bipartite graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Zarankiewicz.mainTarget_proof`, carved from OpenAI's openai/math development (OpenAI, *The crossing number of complete bipartite graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 9 definitions and 4 theorems. The definitions and types are `OAI.Zarankiewicz.evalKernelEquiv`, `OAI.Zarankiewicz.nodeEvaluation`, `OAI.Zarankiewicz.nodeEvaluationEquiv`, `OAI.Zarankiewicz.offsetParameter`, `OAI.Zarankiewicz.orientedTriangleIndicator`, `OAI.Zarankiewicz.rankDetector`, `OAI.Zarankiewicz.rankIncrement`, `OAI.Zarankiewicz.triangleIndicator`, `OAI.Zarankiewicz.triangleSegmentIntersection`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Crossing_CircleOffsetParameter`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/CircleOffsetParameter.lean), [`Crossing_Interpolation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/Interpolation.lean), [`Crossing_PolygonalWalks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/PolygonalWalks.lean), [`Crossing_PolynomialKernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/PolynomialKernel.lean), [`Crossing_RankDetector`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/RankDetector.lean), [`Crossing_TriangleEntryExit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/TriangleEntryExit.lean), [`Crossing_TriangleOrientations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/TriangleOrientations.lean).
--
--   **Imports.** It imports the published bundle `Def_BipartiteCrossing`; the bundle `OAIB3Zr002` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.diagonal_detector_isUnit`, `OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_chord_edge_radius` and `OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_complete_edge_intersection_radius`; the proofs of `OAI.Zarankiewicz.TruncatedSpokeCoordinates.additive_detector_relation`, `OAI_Zarankiewicz_TruncatedSpokeCoordinates_closed_cycle_matrix_sum`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.diagonal_detector_isUnit`, `OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_chord_edge_radius`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_closed_cycle_intersection_radius`, `OAI_Zarankiewicz_TruncatedSpokeCoordinates_exists_complete_edge_intersection_radius`, `OAI.Zarankiewicz.TruncatedSpokeCoordinates.exists_cycle_block_radius` and `OAI.Zarankiewicz.TruncatedSpokeCoordinates.odd_normalized_crossing_lower_bound`.
-- source:
--   OpenAI, The crossing number of complete bipartite graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002

section
-- module Solutions.OAIB3_Zar.Crossing_CircleOffsetParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

def offsetParameter (a δ : ℝ) : ℝ :=
  (circleOffset (circlePoint a) δ).2/(1+(circleOffset (circlePoint a) δ).1)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolynomialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

variable {ι : Type*}

variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

theorem toEvalKernel_injective (k : ℕ) (t : ℝ) :
    Function.Injective (toEvalKernel U node Z k t) := by
  intro p q he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_mulRoot_eq_zero t k (p.val-q.val)
  · exact bounded_sub p.property.1 q.property.1
  · have hh := congrArg (fun r : LinearMap.ker (constrainedEval U node Z (k+1) t) => r.val.val) he
    change mulRoot t p.val = mulRoot t q.val at hh
    change (mulRootLinear t) (p.val-q.val) = 0
    rw [map_sub, show mulRootLinear t p.val = mulRootLinear t q.val from hh, sub_self]

theorem toEvalKernel_surjective (k : ℕ) (t : ℝ) (ht : ∀ i, node i ≠ t) :
    Function.Surjective (toEvalKernel U node Z k t) := by
  intro p
  obtain ⟨q, hq, eq⟩ := exists_mulRoot_of_eval_zero t k p.val.val p.val.property.1 p.property
  have hqU : ∀ i, Z.subtype (eval (node i) q) ∈ U i := by
    intro i
    have hp := p.val.property.2 i
    rw [← eq, eval_mulRoot] at hp
    exact (U i).smul_mem_iff (sub_ne_zero.mpr (ht i)) |>.mp hp
  refine ⟨⟨q, hq, hqU⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact eq

def evalKernelEquiv (k : ℕ) (t : ℝ) (ht : ∀ i, node i ≠ t) :
    constrained U node Z k ≃ₗ[ℝ] LinearMap.ker (constrainedEval U node Z (k+1) t) :=
  LinearEquiv.ofBijective (toEvalKernel U node Z k t)
    ⟨toEvalKernel_injective U node Z k t, toEvalKernel_surjective U node Z k t ht⟩

def rankIncrement (h : ℕ) : ℕ :=
  Module.finrank ℝ (constrained U node Z (h+1)) - Module.finrank ℝ (constrained U node Z h)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_Interpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ι : Type*}

variable [Fintype ι]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

def nodeEvaluation : constrained U node Z (Fintype.card ι) →ₗ[ℝ] (∀ i, ↥(U i ⊓ Z)) where
  toFun p i := ⟨Z.subtype (eval (node i) p.val), p.property.2 i,
    (eval (node i) p.val).property⟩
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

theorem nodeEvaluation_injective (hn : Function.Injective node) :
    Function.Injective (nodeEvaluation U node Z) := by
  intro p q he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_node_roots node hn Finset.univ (p.val-q.val)
  · simpa using bounded_sub p.property.1 q.property.1
  · intro i hi
    rw [map_sub, sub_eq_zero]
    apply Subtype.ext
    exact congrArg (fun x : ↥(U i ⊓ Z) => x.val) (congrFun he i)

theorem nodeEvaluation_surjective (hn : Function.Injective node) :
    Function.Surjective (nodeEvaluation U node Z) := by
  intro z
  have hu : ∀ i, Z.subtype (eval (node i) (vectorInterpolant U node Z z)) ∈ U i := by
    intro i
    rw [eval_vectorInterpolant U node Z hn z i]
    exact (z i).property.1
  refine ⟨⟨vectorInterpolant U node Z z, bounded_vectorInterpolant U node Z hn z, hu⟩, ?_⟩
  funext i
  apply Subtype.ext
  exact congrArg Z.subtype (eval_vectorInterpolant U node Z hn z i)

def nodeEvaluationEquiv (hn : Function.Injective node) :
    constrained U node Z (Fintype.card ι) ≃ₗ[ℝ] (∀ i, ↥(U i ⊓ Z)) :=
  LinearEquiv.ofBijective (nodeEvaluation U node Z)
    ⟨nodeEvaluation_injective U node Z hn, nodeEvaluation_surjective U node Z hn⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def triangleSegmentIntersection (o a b c d : Plane) : ℝ :=
  segmentCrossingSign o a c d + segmentCrossingSign a b c d + segmentCrossingSign b o c d

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RankDetector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rankDetector (s : ℕ) (node : ι → ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix (BiExponent s) (BiExponent s) ℝ where
  toFun H := ∑ p, ∑ q, H p q • detectorAtom s node p q
  map_add' H K := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c H := by simp [smul_smul, Finset.smul_sum]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleEntryExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

def triangleIndicator (a b c z : Plane) : ℝ :=
  ∏ i : Fin 3, positiveIndicator (orient2 (triangleStart a b c i) (triangleEnd a b c i) z)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_TriangleOrientations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

def orientedTriangleIndicator (a b c z : Plane) : ℝ :=
  if 0 < orient2 a b c then triangleIndicator a b c z else -triangleIndicator a c b z

end Zarankiewicz

end

end OAI
end


