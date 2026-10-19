-- Prove2me | Definitions.Def_OAIQWUFI003
-- name    : OAIQWUFI003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:44:48.332826+00:00
-- url     : https://prove2.me/theorems/e58e2156-8889-4303-8d99-f576c52934a9
-- title:
--   OpenAI universal F∞ group split: skeleta of CW complexes (definitions bundle 4 of 9)
-- statement:
--   The definitions behind the cellular-approximation statement of the split of OpenAI's proof that a single group of type $F_\infty$ contains every finitely presented group (OpenAI, *A universal group of type F∞*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). They are ported to Lean 4.33.1 and Mathlib 0df444a, and the bundle uses only Mathlib.
--
--   - `Cellular.Skeleton C n`: Mathlib's `CWComplex.skeletonLT C n`, the union of the cells of dimension less than $n$ of a CW complex $C$.
--   - `Cellular.skeletonInclusion n`: its inclusion as a continuous map.
--   - `Cellular.PartialLift`: OpenAI's structure of a lift defined on a skeleton, which the carver links to `skeletonInclusion`.
--
--   Modules: `CellularApproximation.lean`, `CellularLifting.lean`.
--
--   The statement `OAI.UniversalFInfinity.Cellular.exists_cellular_approximation` imports only this bundle. The later bundles of the split prove the same theorem under the name `exists_cellular_approximation_bundle`, because one of their definitions needs it, so that they can be imported alongside the published statement. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/UniversalGroup at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology


namespace UniversalFInfinity.Cellular
universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

abbrev Skeleton (C : Set X) [CWComplex C] (n : ℕ) : Set X :=
  CWComplex.skeletonLT C n

structure PartialLift {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) (f : C(X,B)) (n : ℕ) where
  val : X → E
  continuousOn : ContinuousOn val (Skeleton C n)
  fac : ∀ x ∈ Skeleton C n, p (val x) = f x

end UniversalFInfinity.Cellular

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace UniversalFInfinity.Cellular

open Set Metric Topology
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]
variable {K : Type v} [MetricSpace K] [CompactSpace K]

def skeletonInclusion (n : ℕ) : C(Skeleton C n,X) := ⟨Subtype.val,continuous_subtype_val⟩

end UniversalFInfinity.Cellular

open scoped TensorProduct

end

end OAI
end


