-- Prove2me | Definitions.Def_Q238K030
-- name    : Q238K030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:02.199926+00:00
-- url     : https://prove2.me/theorems/c29cec0f-2518-4935-8f3c-d44f783a0e88
-- title:
--   Definitions bundle Q238K030 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 110 declarations of OpenAI's Lean: 110 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.csize`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.rest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.bword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.rightShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.clip`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.clipped`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.keep`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.size`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.bword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.rightShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.anext`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.bword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.factor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.lbits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.qnext`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.tbits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choices`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.score`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionPad.remaining`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.blue`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.dest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.filled`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.capacity`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.iterationInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.decode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.image`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.initialInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.total`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.completionCounter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.completionWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.counter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.rword` and 70 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CompletionFillMath`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Encoding_BoundedNatWord`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_FinSetDecode`, `KMedianRecovery_Encoding_UniformWord`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_LocalCandidates`, `KMedianRecovery_Geometry_LocalFuel`, `KMedianRecovery_Geometry_LocalRefineMachine`, `KMedianRecovery_Geometry_LocalSets`, `KMedianRecovery_Machines_LoopSize`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_ProjectionMachine`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Machines_SuffixMachine`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_LengthCandidates`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_RawUnary`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerUpdate`, `KMedianRecovery_Sampling_SamplerWeights`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Sampling_SeedTensor`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K024`, `Q238K025` and `Q238K026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K033`, `Q238K034` and `Q238K035`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_step_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningConstant_constant_source_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningPayment_nearest_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRawOpening_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryResolve_view_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_step_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_chosen_pair_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_old_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.total_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryScan_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238` and `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryBlueRecords_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRows_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_step_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningConstant_constant_source_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningPayment_nearest_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRawOpening_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryResolve_view_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_step_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_chosen_pair_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_old_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.total_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryScan_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238` and `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K024
import Definitions.Def_Q238K025
import Definitions.Def_Q238K026

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic WordList
namespace BinaryPhaseAdvance
open EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment

noncomputable def query_computes : PolyComputes query := (extractPrefix_computes.comp extractPrefix_computes).pair discardPrefix_computes
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFillMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionPad
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def remaining (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (field 0 x,field 1 x))
attribute [local irreducible] remaining BinaryNatSet.union
end MetricKMedianRecovery.BitMachine.BinaryCompletionPad

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawUnary
open WordOperations
noncomputable def run_computes : PolyComputes run := by
  have hh:=UnaryResources.copy_computes id_computes (const_computes [true])
  unfold run
  simpa only [id_eq,copies_singleton] using hh
end MetricKMedianRecovery.BitMachine.RawUnary

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {m n : ℕ}
noncomputable def image : List Bool→List Bool := BinaryNatSet.sort ∘ BinaryIndexMap.run
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_PopulationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
noncomputable def count (x : List Bool) : List Bool :=
  UnaryResources.lengthBits (Count.run (filterWith near x))
noncomputable def candidate (x : List Bool) : ℚ :=
  max (BinaryRational.decode (discardPrefix x))
    (BinaryRational.decode (field 0 (extractPrefix x)) /
      ((value (field 1 (extractPrefix x)):ℚ)*value (count (pairBits (discardPrefix x,field 2 (extractPrefix x))))))
noncomputable def candidates (x : List Bool) : List Bool :=
  mapWith (fun z=>BinaryRational.encode (candidate z)) (pairBits (x,field 2 x))
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UniformWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations BinaryArithmetic
noncomputable def normalizeBig_computes : PolyComputes normalizeBig := reverse_computes.comp BinaryDivision.normalize_computes
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SeedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList BinaryArithmetic
noncomputable def product : ℕ→List Bool→List Bool
  | 0,_ => (1:ℕ).bits
  | d+1,x => (value (UnaryResources.lengthBits (head x))*value (product d (tail x))).bits
noncomputable def width (d : ℕ) (x : List Bool) : List Bool := product (d+1) (tail (extractPrefix (extractPrefix x)))
attribute [local irreducible] width RawDrop.run
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalPower
open WordOperations WordList RationalHeight
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose _
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (cap.word x,Fold.pack (items x) (discardPrefix x) (BinaryRational.encode 1))
noncomputable def run (x : List Bool) : List Bool := CappedFold.run op (prepared x)
end MetricKMedianRecovery.BitMachine.BinaryRationalPower

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MenuMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMenu
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def index (x : List Bool) : List Bool := UnaryResources.lengthBits (exponent x)
noncomputable def denominator (i : ℕ) (x : List Bool) : List Bool := UnaryResources.lengthBits (field i (extractPrefix x))
attribute [local irreducible] UnaryResources.lengthBits
noncomputable def halfNumerator (x : List Bool) : List Bool := BinaryRationalPower.run
  (pairBits (exponent x++[true],BinaryRational.encode (1/2)))
noncomputable def halfNormalizer (x : List Bool) : List Bool := BinaryRationalPower.run
  (pairBits (field 2 (extractPrefix x),BinaryRational.encode (1/2)))
noncomputable def weight (x : List Bool) : ℚ :=
  if first x then 1/(3*(value (denominator 0 x):ℚ))
  else if relative x then 1/(3*((value (denominator 1 x):ℚ)+1))
  else (1/3)*(BinaryRational.decode (halfNumerator x)/(1-BinaryRational.decode (halfNormalizer x)))
noncomputable def denominatorPower (x : List Bool) : List Bool := BinaryRationalPower.run (pairBits (exponent x,
  BinaryRational.encode (1+BinaryRational.decode (field 0 (extractPrefix x)))))
noncomputable def uniformRadius (x : List Bool) : ℚ :=
  (value (index x)+1)*BinaryRational.decode (field 0 (extractPrefix x))*BinaryRational.decode (field 1 (extractPrefix x))
noncomputable def radius (x : List Bool) : List Bool :=
  if relative x then mapWith divide (pairBits (denominatorPower x,field 2 (extractPrefix x)))
  else encode [BinaryRational.encode (uniformRadius x)]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMenu

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def weight (x : List Bool) : ℚ := max 0 (BinaryRational.decode (extractPrefix (reference x)))
noncomputable def weights (x : List Bool) : List Bool := mapWith (fun y=>BinaryRational.encode (weight y)) (pairBits (x,field 1 x))
noncomputable def total (x : List Bool) : ℚ := BinaryRational.decode (RationalArray.sumWords (weights x))
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def undeleted (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (c 4 x,deleted x))
noncomputable def reference (x : List Bool) : List Bool := encode [c 0 x,c 5 x,undeleted x,leaves x]
noncomputable def oracle (x : List Bool) : List Bool := encode [c 1 x,c 2 x,reference x]
end MetricKMedianRecovery.BitMachine.BinarySampler

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Weights
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def context (x : List Bool) : List Bool := encode [oracle (stateInput x),
  BinaryRational.encode (BinarySamplingOracle.total (oracle (stateInput x))),c 9 x,discardPrefix x]
noncomputable def base (x : List Bool) : ℚ :=
  BinarySamplingOracle.weight (pairBits (c 0 x,actionField 1 x))/(2*BinaryRational.decode (c 1 x))
noncomputable def weight (x : List Bool) : ℚ :=
  if active x then if kind 0 x then 0 else if kind 1 x then base x
    else base x*BinaryMenu.weight (pairBits (c 2 x,actionField 2 x))
  else if kind 0 x then 1 else 0
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Client
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
attribute [local irreducible] BinarySamplingOracle.row BinaryIndexMap.run
variable {n : ℕ}
noncomputable def row (x : List Bool) : List Bool := BinarySamplingOracle.row (pairBits (oracle (extractPrefix x),discardPrefix x))
noncomputable def near (x : List Bool) : List Bool := BinaryNearestLeaf.run (pairBits (row x,leaves (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinarySampler.Client

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSetDecode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
noncomputable def decode (n : ℕ) (x : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>BinaryNatSet.contains (pairBits (i.val.bits,x)))
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
attribute [local irreducible] mapWith
noncomputable def score (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (RationalArray.sumWords (marginalValues g x)) /
    (value (UnaryResources.lengthBits (Count.run (elementSamples x))):ℚ))
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def keep (x : List Bool) : Bool :=
  BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def clip (x : List Bool) : List Bool :=
  filterWith keep (pairBits (field 3 x,field 0 x))
noncomputable def size : List Bool→List Bool := UnaryResources.lengthBits ∘ Count.run ∘ clip
noncomputable def run (x : List Bool) : List Bool :=
  if 0<value (size x) then
    if value (size x)≤value (field 2 x) then clip x else field 1 x
  else field 1 x
variable {n : ℕ}
noncomputable def clipped (F : Finset (Fin n)) (raw : List Bool) : Finset (Fin n) :=
  F.filter (fun i=>BinaryNatSet.contains (pairBits (i.val.bits,raw)))
noncomputable def output (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) : Finset (Fin n) :=
  if (clipped F raw).Nonempty ∧ (clipped F raw).card≤k then clipped F raw else S
end MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def choose (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  BinaryRationalBest.fromList (score g) (pairBits (extractPrefix x,bagWords x))
noncomputable def choices (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  mapWith (choose g) (pairBits (x,Indices.run (field 1 x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def nextTable (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  advance (encode [field 1 (Fold.accum x),choices g (stepScore x),field 0 (Fold.accum x)])
attribute [local irreducible] advance choices
noncomputable def step (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  if value (field 0 (Fold.accum x))<(field 2 (Find.context x)).length then
    encode [(value (field 0 (Fold.accum x))+1).bits,nextTable g x]
  else Fold.accum x
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources
open WordOperations WordList BinaryArithmetic
open Categorical.Explicit

noncomputable def bword (x : List Bool) : List Bool :=
  RepeatedAppend.copies 2 (RawUnary.run (UnaryResources.inc (UnaryResources.lengthBits (discardPrefix x))))++List.replicate 10 true
noncomputable def tbits (x : List Bool) : List Bool := NaturalArray.exponentiate (pairBits (bword x,(2:ℕ).bits))
attribute [local irreducible] bword tbits RawUnary.run NaturalArray.exponentiate
noncomputable def qnext (x : List Bool) : List Bool := UnaryResources.inc (UnaryResources.lengthBits (extractPrefix x))
noncomputable def anext (x : List Bool) : List Bool := UnaryResources.inc (UnaryResources.lengthBits (discardPrefix x))
attribute [local irreducible] qnext anext
noncomputable def factor (x : List Bool) : List Bool := (1000000000*value (tbits x)*value (qnext x)).bits
attribute [local irreducible] factor
noncomputable def lbits (x : List Bool) : List Bool := (value (factor x)*(value (anext x))^2).bits
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose _
attribute [local irreducible] cap
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRawPrep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open Categorical.Explicit
variable {q a : ℕ}
noncomputable def bword (x : List Bool) : List Bool := Resources.bword (dimensions x)
attribute [local irreducible] Resources.bword dimensions
noncomputable def rightShape (x : List Bool) : List Bool := encode [aword x,bword x]
attribute [local irreducible] BinarySeed.product
attribute [local irreducible] RawDrop.run rightShape bword
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionRealize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionRealize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n q a p r b : ℕ}
noncomputable def filled (x : List Bool) : List Bool := BinaryFinSet.image
  (pairBits (field 5 x,BinaryCompletionFill.run (fillInput x)))
attribute [local irreducible] fillInput BinaryCompletionFill.run BinaryFinSet.image
attribute [local irreducible] redValues BinaryNatSet.sort
noncomputable def blue (x : List Bool) : List Bool := BinaryNatSet.sort (field 7 x)
noncomputable def dest (x : List Bool) : List Bool := BinaryNatSet.sort (field 8 x)
attribute [local irreducible] blue dest BinaryNatSet.union
attribute [local irreducible] BinaryNatSet.diff
noncomputable def added (x : List Bool) : List Bool := BinaryNatSet.union (pairBits (filled x,dest x))
attribute [local irreducible] filled
attribute [local irreducible] added
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRandomize
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
attribute [local irreducible] Count.run BinaryBisection.logWord RawDrop.run
noncomputable def csize (x : List Bool) : List Bool := (value (UnaryResources.lengthBits (nword x))*2).bits
noncomputable def rest (x : List Bool) : List Bool := RawDrop.run (pairBits (csize (extractPrefix x),discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryBranchRandomize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RandomizedZeroBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
open BinaryCategorical
attribute [local irreducible] dimensions Resources.bword BinarySeed.product
noncomputable def bword (x : List Bool) : List Bool := Resources.bword (dimensions x)
noncomputable def rightShape (x : List Bool) : List Bool := encode [pword x,bword x]
attribute [local irreducible] rightShape BinaryBranchRandomize.csize
end MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_BoundedNatWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BoundedNatWord
open WordOperations
noncomputable def counter (P : Polynomial ℕ) : PolynomialCounter P := PolynomialCounter.choose P
attribute [local irreducible] RawUnary.run counter
end MetricKMedianRecovery.BitMachine.BoundedNatWord

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Parameters
open WordOperations WordList BinaryArithmetic Polynomial RadiusMenus Sampling Sampling.Comparison
open BinaryOpeningPayment (field )
attribute [local irreducible] bound
noncomputable def dimension (x : List Bool) : List Bool := UnaryResources.lengthBits (field 1 x)
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

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
open BinaryOpeningPayment (field )
open Weights (actionField )
variable {n : ℕ}
noncomputable def active (x : List Bool) : Bool := Weights.active (pairBits (Weights.context (extractPrefix x),[]))

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

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic RationalHeight
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose _
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

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
open BinaryOpeningPayment (field )
noncomputable def completionCounter : PolynomialCounter (C 201326592000000015*(X+3)^12) := PolynomialCounter.choose _
noncomputable def completionWord (x : List Bool) : List Bool := completionCounter.word (src 1 x)
attribute [local irreducible] extra raw
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
attribute [local irreducible] extra Fair.raw BinaryMetricBest.run RawUnary.run BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
noncomputable def counter (Q : Polynomial ℕ) : PolynomialCounter Q := PolynomialCounter.choose Q
noncomputable def rword (Q : Polynomial ℕ) (x : List Bool) : List Bool := RawUnary.run ((counter Q).word (extra x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SliceFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Slices
open WordOperations CanonicalSlices
open BinaryOpeningPayment (field )

noncomputable def item_computes : PolyComputes item := discardPrefix_computes.comp extractPrefix_computes
noncomputable def capacity : PolynomialCounter capacityPoly := PolynomialCounter.choose capacityPoly
noncomputable def result (x : List Bool) : List Bool := CappedFold.run step (pairBits (capacity.word x,initial x))
noncomputable def run : List Bool → List Bool := field 2 ∘ result
end MetricKMedianRecovery.BitMachine.WordList.Slices

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SuffixMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySuffix
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
noncomputable def pruneInput (x : List Bool) : List Bool := pairBits (extractPrefix x,Slices.run (discardPrefix x))
noncomputable def prune : List Bool → List Bool := mapWith pruneOp ∘ pruneInput
noncomputable def grow : List Bool → List Bool := reverse ∘ (mapWith growOp ∘ pruneInput)
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
noncomputable def replaces (x : List Bool) : List Bool := mapWith replaceOp (pairBits (x,Slices.run (field 4 x)))
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSets
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
noncomputable def swapWords_computes : PolyComputes swapWords := discardPrefix_computes.pair extractPrefix_computes
noncomputable def size : List Bool→List Bool := UnaryResources.lengthBits ∘ Count.run
end MetricKMedianRecovery.BitMachine.BinaryLocalSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalCandidates
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCandidates
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryLocalSets
noncomputable def sameSize (x : List Bool) : Bool := decide (value (size (extractPrefix x))=value (size (discardPrefix x)))
noncomputable def run (w : ℕ) (x : List Bool) : List Bool :=
  filterWith sameSize (pairBits (discardPrefix x,raw w x))
end MetricKMedianRecovery.BitMachine.BinaryLocalCandidates

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
noncomputable def selected (w : ℕ) (x : List Bool) : List Bool :=
  BinaryLocalBest.run rank (pairBits (x,pairBits (field 3 x,
    BinaryLocalCandidates.run w (pairBits (field 2 x,field 3 x)))))
noncomputable def step (w : ℕ) (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x,selected w x]
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
noncomputable def capacity : PolynomialCounter capPoly := PolynomialCounter.choose capPoly
noncomputable def iterationInput (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (capacity.word x,discardPrefix x))
noncomputable def run (w : ℕ) : List Bool→List Bool :=
  field 3 ∘ BoundedIteration.run (step w) ∘ iterationInput
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalFuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open WordOperations WordList BinaryArithmetic RationalLeaves Polynomial
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryLabel.sort
noncomputable def fuel : PolynomialCounter fuelPoly := PolynomialCounter.choose fuelPoly
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalRefineMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalRefine
open RationalLeaves WordOperations WordList Polynomial
noncomputable def run (x : List Bool) : List Bool :=
  BinaryLocalSearch.run 5 (pairBits (BinaryLocalAnchor.fuel.word x,x))
end MetricKMedianRecovery.BitMachine.BinaryLocalRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
noncomputable def paids (x : List Bool) : List Bool := mapWith paidOp (pairBits ([],Slices.run (field 2 x)))
noncomputable def candidates (x : List Bool) : List Bool := frees x++paids x
noncomputable def view (x : List Bool) : List Bool := Find.run accepts (pairBits (x,candidates x))
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def view : List Bool→List Bool := BinaryLength.view ∘ viewInput
noncomputable def plan : List Bool→List Bool := List.tail ∘ view
noncomputable def sensitiveInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 2 x,field 3 x,field 4 x,field 5 x,field 6 x,H x,T x,U x,plan x]
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def capacity : PolynomialCounter capacityPoly := PolynomialCounter.choose capacityPoly
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
noncomputable def grown (x : List Bool) : List Bool := BinarySuffix.grow (pairBits (pairBits (ct x,spareWord x),jf 3 x))
noncomputable def removeOut (x : List Bool) : List Bool := cons (ctSpare x) (grown x++cons (ct x++jf 3 x) [])
noncomputable def expand (x : List Bool) : List Bool := if tagIs 1 x then removeOut x else cons (cf 1 x) []
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RefineMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
noncomputable def runInput (x : List Bool) : List Bool := pairBits (extractPrefix x,Slices.run (discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
noncomputable def scanInput (x : List Bool) : List Bool := pairBits (field 0 x,Slices.run (field 2 x))
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryCoupled (stateBits outcomeBits outputBits)
noncomputable def capacity : PolynomialCounter capPoly := PolynomialCounter.choose capPoly
noncomputable def iterationInput (x : List Bool) : List Bool := pairBits (field 1 x,pairBits (capacity.word x,x))
attribute [local instance] RationalLeaves.metric
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ProjectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryProjection
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
noncomputable def run (x : List Bool) : List Bool :=
  BinaryNatSet.sort (WordList.map BinaryLabel.parentWords x)
end MetricKMedianRecovery.BitMachine.BinaryProjection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFuel
open WordOperations BinaryArithmetic RationalHeight

noncomputable def cap (K : ℚ) (C : ℕ) : PolynomialCounter
    (Polynomial.C (coefficient K C)*(Polynomial.X+1)) := PolynomialCounter.choose _
noncomputable def fuel (C : ℕ) : PolynomialCounter
    (Polynomial.C C*(Polynomial.X+1)) := PolynomialCounter.choose _

noncomputable def iterated (K : ℚ) (C : ℕ) (x : List Bool) : List Bool :=
  BoundedIteration.run (step K) (pairBits ((fuel C).word x,pairBits ((cap K C).word x,initial x)))

noncomputable def run (K : ℚ) (C : ℕ) (x : List Bool) : List Bool := true::count (iterated K C x)

end MetricKMedianRecovery.BitMachine.BinaryPhaseFuel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialAuto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialAuto
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
noncomputable def total (v : ℚ) (C : ℕ) (x : List Bool) : List Bool := true::BinaryPhaseFuel.run (1+v^2) C (threshold x)
noncomputable def initialInput (v : ℚ) (C : ℕ) (x : List Bool) : List Bool :=
  encode [context v x,size x,size x,total v C x,field 5 x,low x,field 4 x]
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialProject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialProject
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
attribute [local irreducible] BinaryProjection.run BinaryFiniteMachine.after
noncomputable def extract (x : List Bool) : List Bool :=
  BinaryProjection.run (BinaryFiniteMachine.after (pairBits ([],field 2 (discardPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryInitialProject

end OAI
end


