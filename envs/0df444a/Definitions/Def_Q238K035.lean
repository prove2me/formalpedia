-- Prove2me | Definitions.Def_Q238K035
-- name    : Q238K035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:28:30.608319+00:00
-- url     : https://prove2.me/theorems/c06aa1eb-a256-472e-a16b-8eb91e469281
-- title:
--   Definitions bundle Q238K035 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 26 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.P.clients`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.P.facilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallbackInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.maskCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.clients`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.facilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.points`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.clientCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.clients`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilitiesInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.plainFacilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.points`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.twice`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.chosen`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.old`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.atRaw`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.candidates`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.output`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.run`, `OAI.MetricKMedianRecovery.BitMachine.NatOps.min`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Algorithms_CandidateSanitize`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/CandidateSanitize.lean), [`KMedianRecovery_Algorithms_GlobalOuter`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuter.lean), [`KMedianRecovery_Encoding_RationalStream`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/RationalStream.lean), [`KMedianRecovery_Geometry_MetricParser`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricParser.lean), [`KMedianRecovery_Geometry_RoundingArithmetic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/RoundingArithmetic.lean), [`KMedianRecovery_Machines_NormalizationMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/NormalizationMachine.lean), [`KMedianRecovery_Recovery_NormalizeInput`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean), [`KMedianRecovery_Sampling_SamplerUpdate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdate.lean), [`KMedianRecovery_Sampling_SamplerUpdateParts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdateParts.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K028`, `Q238K029`, `Q238K030` and `Q238K031` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238K038`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities_bits_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities_bits_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K028
import Definitions.Def_Q238K029
import Definitions.Def_Q238K030
import Definitions.Def_Q238K031

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream
open WordOperations
attribute [local irreducible] rational
noncomputable def run_computes : PolyComputes run :=
  ((id_computes.pair (const_computes [])).comp
    (BoundedIteration.polynomialRun_computes step_computes Polynomial.X (3*Polynomial.X+1))).comp
    (discardPrefix_computes.comp WordList.reverse_computes)
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric
open WordOperations WordList
attribute [local irreducible] nat RawTake.run RawDrop.run Stream.run RawUnary.run
noncomputable def clients (x : List Bool) : List Bool := RawTake.run (pairBits (count x,masks x))
noncomputable def facilities (x : List Bool) : List Bool := RawTake.run (pairBits (count x,afterClients x))
attribute [local irreducible] header count tailHeader budget masks clients afterClients facilities rawMatrix
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

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
noncomputable def chosen (x : List Bool) : List Bool := discardPrefix
  (BinarySamplingOracle.reference (pairBits (oracle (input x),actionField 1 x)))
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def atRaw : List Bool→List Bool := BinaryCandidateSanitize.run ∘ atRawInput
noncomputable def candidates (x : List Bool) : List Bool := mapWith atRaw (pairBits (sanitizeContext x,field 5 x))
noncomputable def run (x : List Bool) : List Bool := BinaryMetricBest.run
  (pairBits (metricContext x,pairBits (field 3 x,candidates x)))
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (xs.map (BinaryCandidateSanitize.output F S k))
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

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
variable {n : ℕ}
noncomputable def old (x : List Bool) : Bool := decide (value (chosen x)<value (c 0 (input x)))
noncomputable def remove (x : List Bool) : List Bool := BinarySamplingState.retain (pairBits
  (c 8 (input x),BinarySamplingState.remove (pairBits (discardPrefix (input x),chosen x))))

end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingArithmetic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NatOps
noncomputable def min {f g : List Bool→List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(Min.min (value (f x)) (value (g x))).bits) := by
  have hh:=(le hf hg).cond (hf.comp normalize_computes) (hg.comp normalize_computes)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [decide_eq_true_eq,Function.comp_def,normalize_eq_bits]
  split_ifs with h
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
end NatOps
end MetricKMedianRecovery.BitMachine

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
noncomputable def count_computes : PolyComputes count := (field_computes 2).comp UnaryResources.lengthBits_computes
end MetricKMedianRecovery.BitMachine.BinaryNormalization

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NormalizeInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalizeInput
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace P
noncomputable def clients : List Bool→List Bool := BinaryMaskParser.run ∘ BinaryInputParser.Metric.clients
noncomputable def facilities : List Bool→List Bool := BinaryMaskParser.run ∘ BinaryInputParser.Metric.facilities
noncomputable def points : List Bool→List Bool := RawUnary.run ∘ BinaryInputParser.Metric.clients
end P
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
noncomputable def points (x : List Bool) : List Bool := P.points (raw x)
noncomputable def clients (x : List Bool) : List Bool := P.clients (raw x)
noncomputable def clientCount (x : List Bool) : List Bool := Count.run (clients x)
noncomputable def plainFacilities (x : List Bool) : List Bool := P.facilities (raw x)
noncomputable def facilitiesInput (x : List Bool) : List Bool := pairBits (count x,plainFacilities x)
noncomputable def facilities (x : List Bool) : List Bool := BinaryTaggedSets.shift (facilitiesInput x)
noncomputable def twice (x : List Bool) : List Bool := BinaryDuplicateMatrix.twice (points x)
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace P
noncomputable abbrev clients := BinaryNormalizeInput.P.clients
noncomputable abbrev facilities := BinaryNormalizeInput.P.facilities
end P
noncomputable def fallbackInput (x : List Bool) : List Bool := encode [P.facilities x,[],(1:ℕ).bits]
attribute [local irreducible] BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget
noncomputable def maskCount : List Bool→List Bool := RawUnary.run ∘ BinaryInputParser.Metric.clients ∘ extractPrefix
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


