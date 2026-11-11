-- Prove2me | Definitions.Def_Q238K038
-- name    : Q238K038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:48.610638+00:00
-- url     : https://prove2.me/theorems/3701bcb3-5887-4df7-bb79-e471f5ae0baf
-- title:
--   Definitions bundle Q238K038 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 14 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.capArgument_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.mesh_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.distance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.entryInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.input`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.add`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.rows`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Algorithms_IntegralRecoveryDemand`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryDemand.lean), [`KMedianRecovery_Algorithms_IntegralRecoveryRepeat`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryRepeat.lean), [`KMedianRecovery_Geometry_RoundingMatrix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/RoundingMatrix.lean), [`KMedianRecovery_Machines_NormalizationMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/NormalizationMachine.lean), [`KMedianRecovery_Sampling_SamplerResources`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerResources.lean), [`KMedianRecovery_Sampling_SamplerTraceMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerTraceMachine.lean), [`KMedianRecovery_Sampling_SamplerUpdate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdate.lean), [`KMedianRecovery_Sampling_SamplerUpdateParts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdateParts.lean), [`KMedianRecovery_Sampling_SamplerWeights`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerWeights.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K032`, `Q238K033`, `Q238K034` and `Q238K035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K040` and `Q238K046`; the statements `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseTrace_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseTrace_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K032
import Definitions.Def_Q238K033
import Definitions.Def_Q238K034
import Definitions.Def_Q238K035

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Client
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySamplingOracle.row BinaryIndexMap.run
variable {n : ℕ}
noncomputable def radii (x : List Bool) : List Bool := encode [c 7 (extractPrefix x),population x,near x]
end MetricKMedianRecovery.BitMachine.BinarySampler.Client

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdateParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField )
attribute [local irreducible] BinaryMenu.radius WordList.filterWith Client.row
variable {n : ℕ}
noncomputable def radius (x : List Bool) : List Bool := BinaryMenu.radius (pairBits (Client.radii (clientInput x),actionField 2 x))
noncomputable def ball (x : List Bool) : List Bool := filterWith within (pairBits
  (pairBits (Client.row (clientInput x),head (radius x)),c 3 (input x)))
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField )
attribute [local irreducible] radius
variable {n : ℕ}
noncomputable def add (x : List Bool) : List Bool := BinarySamplingState.retain (pairBits
  (c 8 (input x),BinarySamplingState.add (pairBits (discardPrefix (input x),pairBits (actionField 1 x,WordList.head (radius x))))))
noncomputable def run (x : List Bool) : List Bool :=
  if active x then if Weights.kind 0 x then [] else if Weights.kind 1 x then
    if old x then remove x else []
  else if radius x=[] then [] else if ball x=[] then [] else add x
  else []

end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList
attribute [local irreducible] WordList.mapWith
noncomputable def rows (x : List Bool) : List Bool :=
  mapWith (chunk 0) (pairBits (x,indices x))
attribute [local irreducible] indices chunk
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerTraceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Trace
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySeed.rows BinaryEllipsoidInitial.indices WordList.mapWith
noncomputable def rows (x : List Bool) : List Bool :=
  BinarySeed.rows (pairBits (encode [field 2 x,field 3 x],field 4 x))
noncomputable def input (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 3 x,rows x]
end MetricKMedianRecovery.BitMachine.BinarySampler.Trace

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations Polynomial
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def demandBits : List Bool→List Bool := UnaryResources.lengthBits ∘ demandWord
attribute [local irreducible] extra raw demandBits RawTake.run
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open WordOperations WordList Sampling.Comparison
attribute [local irreducible] extra Fair.raw Fair.demandWord BinaryMetricBest.run RawUnary.run BinarySeed.rows
  BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
noncomputable def rows (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  BinarySeed.rows (pairBits (encode [rword Q x,bword x],Fair.raw x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def distance_computes : PolyComputes distance := by
  unfold distance
  have computes := (((ctx_computes.comp (field_computes 0)).pair rowIndex_computes).pair colIndex_computes).comp MetricTable.get_computes
  simpa only [Function.comp_def] using computes
noncomputable def entryInput_computes : PolyComputes entryInput :=
  list_computes [distance,field 2 ∘ ctx,field 3 ∘ ctx] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨distance_computes⟩
    · exact ⟨ctx_computes.comp (field_computes 2)⟩
    · exact ⟨ctx_computes.comp (field_computes 3)⟩)
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_NormalizationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalization
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open IntegralAssembly (gammaRat)
noncomputable def mesh_computes : PolyComputes mesh :=
  RatOps.div (RatOps.mul (RatOps.const (gammaRat/16)) (RatOps.ofWords (field_computes 3))) (RatOps.nat count_computes)
noncomputable def capArgument_computes : PolyComputes capArgument :=
  RatOps.div (RatOps.mul (RatOps.mul (RatOps.const 20) (RatOps.nat count_computes)) (RatOps.nat count_computes))
    (RatOps.const (gammaRat/16))
end MetricKMedianRecovery.BitMachine.BinaryNormalization

end OAI
end


