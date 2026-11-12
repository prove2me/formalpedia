-- Prove2me | Definitions.Def_Q238L038
-- name    : Q238L038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:34:28.356346+00:00
-- url     : https://prove2.me/theorems/4e15d802-6ec3-406d-b119-8dbadec6eeb5
-- title:
--   Definitions bundle Q238L038 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 33 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.base`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.clamp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.fcount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.norm`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.src`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.P.matrix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zeroInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.matrix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.capArgument_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.mesh_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.matrix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.mesh`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.rounded`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.distance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.entryInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Draw.index`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Draw.run`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.run`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.step`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.input`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.prefixBits`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.run`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.output`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.rows`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Algorithms_CandidateSanitize`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/CandidateSanitize.lean), [`KMedianRecovery_Algorithms_GlobalCall`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalCall.lean), [`KMedianRecovery_Algorithms_GlobalOuter`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuter.lean), [`KMedianRecovery_Encoding_MatrixRows`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/MatrixRows.lean), [`KMedianRecovery_Geometry_MetricParser`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricParser.lean), [`KMedianRecovery_Geometry_RoundingMatrix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/RoundingMatrix.lean), [`KMedianRecovery_Machines_NormalizationMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/NormalizationMachine.lean), [`KMedianRecovery_Recovery_NormalizeInput`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean), [`KMedianRecovery_Sampling_SamplerDraw`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerDraw.lean), [`KMedianRecovery_Sampling_SamplerResources`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerResources.lean), [`KMedianRecovery_Sampling_SamplerTraceMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerTraceMachine.lean), [`KMedianRecovery_Sampling_SamplingPotential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingPotential.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L032`, `Q238L033`, `Q238L034` and `Q238L035` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238L040`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.run_pack_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.run_pack_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L032
import Definitions.Def_Q238L033
import Definitions.Def_Q238L034
import Definitions.Def_Q238L035

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MatrixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows
open WordOperations WordList BinaryArithmetic
noncomputable def row (x : List Bool) : List Bool := Take.run (pairBits
  (UnaryResources.lengthBits (extractPrefix (extractPrefix x)),Drop.run (pairBits (offset x,discardPrefix (extractPrefix x)))))
attribute [local irreducible] offset Drop.run Take.run
noncomputable def run (x : List Bool) : List Bool :=
  mapWith row (pairBits (x,BinaryEllipsoidInitial.indices (extractPrefix x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows

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
attribute [local irreducible] nat RawTake.run RawDrop.run Stream.run Rows.run RawUnary.run
attribute [local irreducible] header count tailHeader budget masks clients afterClients facilities rawMatrix
noncomputable def matrix (x : List Bool) : List Bool := Rows.run (pairBits (RawUnary.run (clients x),Stream.run (rawMatrix x)))
attribute [local irreducible] matrix
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

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
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (xs.map (BinaryCandidateSanitize.output F S k))
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Draw
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def index (x : List Bool) : List Bool := BinaryDyadic.run (encode [field 2 x,weights x,(0:ℕ).bits,field 3 x])
noncomputable def run (x : List Bool) : List Bool := Lookup.run (pairBits (index x,actions x))
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Update.run Draw.run
variable {n : ℕ}

noncomputable def step (x : List Bool) : List Bool := Update.run (pairBits (input x,Draw.run (drawInput x)))
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def run (x : List Bool) : List Bool :=
  CappedFold.run step (pairBits (cap.word x,Fold.pack (field 3 x) (fixedContext x) initial))
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

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
attribute [local irreducible] BinarySeed.rows Take.run Loop.run BinaryEllipsoidInitial.indices WordList.mapWith
noncomputable def rows (x : List Bool) : List Bool :=
  BinarySeed.rows (pairBits (encode [field 2 x,field 3 x],field 4 x))
noncomputable def input (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 3 x,rows x]
noncomputable def prefixBits (x : List Bool) : List Bool :=
  Take.run (pairBits (discardPrefix x,field 3 (extractPrefix x)))
noncomputable def atPrefix (x : List Bool) : List Bool := Loop.run
  (encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),prefixBits x])
noncomputable def run (x : List Bool) : List Bool :=
  mapWith atPrefix (pairBits (input x,BinaryEllipsoidInitial.indices (field 2 x++[true])))
end MetricKMedianRecovery.BitMachine.BinarySampler.Trace

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
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.matrix BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
noncomputable def matrix (x : List Bool) : List Bool := BinaryInputParser.Metric.matrix (raw x)
noncomputable def prep (x : List Bool) : List Bool := encode [matrix x,points x,clientCount x,discardPrefix x]
noncomputable def rounded (x : List Bool) : List Bool := BinaryNormalization.run (prep x)
noncomputable def mesh (x : List Bool) : List Bool := BinaryNormalization.mesh (prep x)
noncomputable def cap (x : List Bool) : List Bool := BinaryNormalization.cap (prep x)
noncomputable def run (x : List Bool) : List Bool := encode [rounded x,twice x,clients x,facilities x,budget x,mesh x,cap x]
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalCall
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def norm : List Bool→List Bool := BinaryNormalizeInput.run ∘ normInput
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ norm
noncomputable def fcount : List Bool→List Bool := UnaryResources.lengthBits ∘ Count.run ∘ src 3
noncomputable def clamp (x : List Bool) : List Bool := (min (value (src 4 x)) (value (fcount x))).bits
noncomputable def base (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 6 x,clamp x,field 0 x,[]]
attribute [local irreducible] base RawTake.run UnaryResources.lengthBits
attribute [local irreducible] norm src clamp BinaryInputParser.Metric.count
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

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
noncomputable abbrev matrix := BinaryInputParser.Metric.matrix
end P
noncomputable def fallback : List Bool→List Bool := BinaryCompletionPad.run ∘ fallbackInput
noncomputable def zeroInput (x : List Bool) : List Bool := encode [P.matrix x,P.clients x,P.facilities x]
noncomputable def zero : List Bool→List Bool := BinaryGlobalZero.run ∘ zeroInput
attribute [local irreducible] BinaryInputParser.Metric.matrix BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget fallback
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


