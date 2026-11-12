-- Prove2me | Definitions.Def_Q238L029
-- name    : Q238L029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:28:04.582468+00:00
-- url     : https://prove2.me/theorems/4ffdc9aa-17ac-435f-a226-f0dacd0f6677
-- title:
--   Definitions bundle Q238L029 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 142 declarations of OpenAI's Lean: 142 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.csize`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.rest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.bword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.rightShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.bword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.rightShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.anext`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.bword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.factor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.lbits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.qnext`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.tbits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapSet`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafBank`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafResult`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.mapFree`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.capacity`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.iterationInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.QG`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.bankInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.ctx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mappedFree`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalOpened`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.opened`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.stateEncode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.resultBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.bankFirst`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.banks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.copiedSet`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pool`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.A.pack` and 102 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Encoding_BoundedNatWord`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_UniformWord`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_LocalCandidates`, `KMedianRecovery_Geometry_LocalFuel`, `KMedianRecovery_Geometry_LocalRefineMachine`, `KMedianRecovery_Geometry_LocalSets`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_CoupledPrimitives`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_LoopSize`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_ProjectionMachine`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Machines_SuffixMachine`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_LengthCandidates`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Sampling_SeedTensor`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L022`, `Q238L023`, `Q238L024` and `Q238L025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L033`, `Q238L034` and `Q238L035`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mapped_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.total_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238r` and `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mapped_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.total_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238r` and `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L022
import Definitions.Def_Q238L023
import Definitions.Def_Q238L024
import Definitions.Def_Q238L025

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidCut
open RationalMatrix

def pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) : List Bool :=
  pairBits (n.bits,pairBits (encode H,pairBits (rowEncode a,pairBits (rowEncode c,D.bits))))
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidGrid
open RationalMatrix WordList

def pack {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : List Bool :=
  pairBits (n.bits,pairBits (D.bits,RationalMatrix.encode A))
end BinaryEllipsoidGrid
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

def stateEncode {n : ℕ} (S : State n) : List Bool := pairBits (encode S.shape,rowEncode S.center)
def pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : List Bool :=
  pairBits (n.bits,pairBits (D.bits,pairBits (BinaryRow.rowsEncode rs,stateEncode S)))
end BinaryEllipsoidAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

def pack (n T R : ℕ) (rs : List (Row n)) : List Bool :=
  pairBits (List.replicate T true,pairBits (R.bits,
    BinaryEllipsoidAdvance.pack (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ))))
end BinaryEllipsoidIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open UnaryResources NaturalArray

def pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate m true,
    pairBits (B.bits,pairBits (H.bits,BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (A r) (b r)))))))
end BinaryDecision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Rectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
def resultBits {n : ℕ} : Option (Fin n → ℚ) → List Bool
  | none=>[]
  | some v=>true::rowEncode v
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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
noncomputable def isActive (x : List Bool) : Bool := BinaryOpeningPayment.active (query x)
noncomputable def budgetItem (x : List Bool) : List Bool :=
  if isActive x then BinaryRational.encode (clippedItem x)
  else Lookup.run (pairBits (discardPrefix x,discardPrefix (extractPrefix x)))
noncomputable def budget (x : List Bool) : List Bool :=
  mapWith budgetItem (pairBits (x,BinaryOpeningEnumeration.clients (extractPrefix x)))
noncomputable def run (x : List Bool) : List Bool := pairBits (context x,budget x)
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open Classical
open WordOperations WordList BinaryOpeningPayment RationalLeaves
open BinaryLabel (orderedSort)

def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,setBits F,setBits Q,
    labels (List.ofFn loc),BinaryRational.encode v,BinaryRational.encode z,BinaryRational.encode lam]
attribute [local irreducible] BinaryLabelMatrix.run
attribute [local irreducible] matrix selected
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations WordList RationalLeaves
noncomputable def missing (x : List Bool) : Bool := !contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def allIn (x : List Bool) : Bool := decide (Find.run missing x=[])
end MetricKMedianRecovery.BitMachine.BinaryLabel
namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
noncomputable def labelsCheck (x : List Bool) : Bool :=
  if tagIs 1 x then BinaryLabel.allIn (pairBits (cf 0 x,jf 3 x)) else true
noncomputable def accepts (x : List Bool) : Bool :=
  WordEq.eq (pairBits (source x,cf 3 x)) && (WordEq.eq (pairBits (target x,cf 4 x)) &&
    (BinaryLabel.contains (pairBits (jf 4 x,cf 0 x)) &&
      labelsCheck x))

end MetricKMedianRecovery.BitMachine.BinaryJump

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
noncomputable def denominator (i : ℕ) (x : List Bool) : List Bool := UnaryResources.lengthBits (field i (extractPrefix x))
attribute [local irreducible] UnaryResources.lengthBits
noncomputable def halfNumerator (x : List Bool) : List Bool := BinaryRationalPower.run
  (pairBits (exponent x++[true],BinaryRational.encode (1/2)))
noncomputable def halfNormalizer (x : List Bool) : List Bool := BinaryRationalPower.run
  (pairBits (field 2 (extractPrefix x),BinaryRational.encode (1/2)))
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
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def run (x : List Bool) : List Bool := BinaryRationalBest.run score x
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

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
attribute [local irreducible] extra Fair.raw BinaryMetricBest.run RawUnary.run BinaryFinSet.encode BinaryMetricBest.best List.ofFn BinarySeed.raw
noncomputable def counter (Q : Polynomial ℕ) : PolynomialCounter Q := PolynomialCounter.choose Q
noncomputable def rword (Q : Polynomial ℕ) (x : List Bool) : List Bool := RawUnary.run ((counter Q).word (extra x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LengthEncode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryLabelMatrix.row
noncomputable def rootIn (x : List Bool) : Bool := BinaryLabel.contains (pairBits (pf 1 x,cf 0 x))
noncomputable def freeOut (x : List Bool) : Bool := !BinaryLabel.contains (pairBits (pf 2 x,cf 0 x))
noncomputable def row (n : ℕ) (x : List Bool) : List Bool := BinaryLabelMatrix.row (pairBits (cf 4 x,pf n x))
noncomputable def sameRow (x : List Bool) : Bool := WordEq.eq (pairBits (row 1 x,row 2 x))
noncomputable def extra (x : List Bool) : Bool := if isFree x then freeOut x && sameRow x else true
noncomputable def accepts (x : List Bool) : Bool := rootIn x &&
  (WordEq.eq (pairBits (cf 2 x,source x)) && (WordEq.eq (pairBits (cf 3 x,target x)) && extra x))
end MetricKMedianRecovery.BitMachine.BinaryLength

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

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )

noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteContext.union
  (pairBits (cf 1 x,extractPrefix (discardPrefix x)))
noncomputable def finalOpened (x : List Bool) : List Bool :=
  BinaryFiniteMachine.after (pairBits (opened x,discardPrefix (discardPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
noncomputable def replaces (x : List Bool) : List Bool := mapWith replaceOp (pairBits (x,Slices.run (field 4 x)))
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LengthQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLengthQuery
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
noncomputable def opened (x : List Bool) : List Bool :=
  BinaryFiniteContext.union (pairBits (field 3 (cf 0 x),WordList.cons (newLeaf x) []))
noncomputable def base (x : List Bool) : List Bool := BinaryFiniteContext.replaceOpen (pairBits (cf 0 x,opened x))
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SensitiveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySensitive
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalLengthView
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )

noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteContext.union (pairBits (field 3 (field 0 x),common x))
noncomputable def base (x : List Bool) : List Bool := BinaryFiniteContext.replaceOpen (pairBits (field 0 x,opened x))
noncomputable def context (x : List Bool) : List Bool := encode [base x,field 1 x,nextQ x,field 3 x,jf 1 x,field 4 x,small x,large x]
noncomputable def searchInput (x : List Bool) : List Bool := encode [field 6 x,context x,field 5 x,BinaryRational.encode 0,field 4 x]
noncomputable def atZero (x : List Bool) : List Bool := pairBits (context x,BinaryRational.encode 0)
end MetricKMedianRecovery.BitMachine.BinarySensitive

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
noncomputable def addOne (x : List Bool) : List Bool := BinaryLabel.sort (cons (extractPrefix x) (discardPrefix x))

noncomputable def without (x : List Bool) : Bool := !BinaryLabel.contains (swapWords x)
noncomputable def diff (x : List Bool) : List Bool := BinaryLabel.sort (filterWith without (swapWords x))
noncomputable def size : List Bool→List Bool := UnaryResources.lengthBits ∘ Count.run
noncomputable def insertEach : List Bool→List Bool := mapWith addOne ∘ swapWords
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
noncomputable def widths (w : ℕ) : List Bool→List Bool :=
  match w with
  | 0=>fun _=>encode [[]]
  | w+1=>fun x=>widths w x++flatMapWith insertEach (pairBits (widths w x,x))
noncomputable def sameSize (x : List Bool) : Bool := decide (value (size (extractPrefix x))=value (size (discardPrefix x)))
noncomputable def removed (w : ℕ) (x : List Bool) : List Bool :=
  mapWith diff (pairBits (discardPrefix x,widths w (extractPrefix x)))
noncomputable def raw (w : ℕ) (x : List Bool) : List Bool :=
  crossWith BinaryFiniteContext.union (pairBits (removed w x,widths w (extractPrefix x)))
noncomputable def run (w : ℕ) (x : List Bool) : List Bool :=
  filterWith sameSize (pairBits (discardPrefix x,raw w x))
end MetricKMedianRecovery.BitMachine.BinaryLocalCandidates

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCost
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
noncomputable def entry (x : List Bool) : List Bool :=
  BinaryLabel.row (pairBits (pairBits (extractPrefix (extractPrefix x),discardPrefix x),discardPrefix (extractPrefix x)))
noncomputable def near (x : List Bool) : List Bool := RationalMin.run
  (mapWith entry (pairBits (pairBits (field 0 (extractPrefix x),discardPrefix x),field 2 (extractPrefix x))))
noncomputable def run (x : List Bool) : List Bool := RationalArray.sumWords
  (mapWith near (pairBits (x,BinaryEllipsoidInitial.indices (field 1 x))))
noncomputable def rank (x : List Bool) : List Bool := (⌈BinaryRational.decode (run x)⌉₊).bits
end MetricKMedianRecovery.BitMachine.BinaryLocalCost

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
noncomputable def rank (x : List Bool) : List Bool := BinaryLocalCost.rank
  (encode [field 0 (extractPrefix x),field 1 (extractPrefix x),discardPrefix x])
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
noncomputable def lift (x : List Bool) : List Bool :=
  BinaryLabel.sort (WordList.map originalWord x)
end MetricKMedianRecovery.BitMachine.BinaryProjection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,Δ.bits,k.bits,g,raw]
attribute [local irreducible] UnaryResources.lengthBits
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CoupledEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCorrection
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def mapSet : List Bool→List Bool := BinaryLabel.sort ∘ mapRow
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def mapFree (x : List Bool) : List Bool := BinaryCorrection.mapSet (pairBits (field 2 x,field 0 x))
attribute [local irreducible] BinaryCorrection.mapHistory
end MetricKMedianRecovery.BitMachine.BinaryCoupled

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def leafBank (x : List Bool) : List Bool := BinaryFiniteContext.union (pairBits (field 0 x,cons (endLeaf 7 x) []))
noncomputable def leafResult (x : List Bool) : List Bool :=
  encode [leafBank x,leafPrefix x,pairBits (endLeaf 7 x,endLeaf 6 x),field 2 x,field 2 x,field 8 x,field 9 x]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPlanResult
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def finishInput (x : List Bool) : List Bool :=
  encode [BinaryCoupled.leafBank (leafInput x),price x,BinaryCoupled.leafPrefix (leafInput x),rf 3 x]
noncomputable def run (x : List Bool) : List Bool := if success x then
  pairBits ([],BinaryCoupled.finish (finishInput x)) else pairBits ([true],BinaryCoupled.leafResult (leafInput x))
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def copiedSet (x : List Bool) : List Bool := BinaryLabel.sort (mapWith BinaryLabel.copied x)
noncomputable def pool (x : List Bool) : List Bool := union (pairBits (field 1 x,copiedSet (pairBits (field 2 x,field 0 x))))
noncomputable def bankFirst (x : List Bool) : List Bool := pool (encode [field 0 x,field 1 x,threeQ x])
noncomputable def banks (x : List Bool) : List Bool := pool (encode [field 0 x,bankFirst x,threeQOne x])
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ScanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryScan
open WordOperations WordList RationalLeaves CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
noncomputable def opened (x : List Bool) : List Bool :=
  BinaryFiniteContext.union (pairBits (field 3 (cf 0 x),discardPrefix x))
noncomputable def base (x : List Bool) : List Bool := BinaryFiniteContext.replaceOpen (pairBits (cf 0 x,opened x))
noncomputable def contInput (x : List Bool) : List Bool := pairBits (cf 1 x,pairBits (cf 2 x,base x))
end MetricKMedianRecovery.BitMachine.BinaryScan

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StepMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
noncomputable def mappedFree (x : List Bool) : List Bool := BinaryCoupled.mapFree (field 6 x)
noncomputable def Q (x : List Bool) : List Bool := BinaryFiniteMachine.after (pairBits ([],mappedPrefix x))
noncomputable def QG (x : List Bool) : List Bool := BinaryFiniteContext.union (pairBits (Q x,G x))
noncomputable def ctx (x : List Bool) : List Bool := encode [bf 2 x,Q x,field 5 x]
noncomputable def bankInput (x : List Bool) : List Bool := encode [bf 2 x,mappedFree x,qbits x]
noncomputable def banks (x : List Bool) : List Bool := BinaryFiniteContext.banks (bankInput x)
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFuel
open WordOperations BinaryArithmetic RationalPhaseFuel RationalHeight

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
noncomputable def context (v : ℚ) (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,BinaryProjection.lift (field 2 x),[],
    map BinaryProjection.originalWord (field 3 x),BinaryRational.encode v,BinaryRational.encode 0,BinaryRational.encode 0]
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

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

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
open BinaryOpeningPayment (field )
namespace A
abbrev pack := @BinaryIntegralDispatch.pack
end A
attribute [local irreducible] UnaryResources.lengthBits
attribute [local irreducible] BinaryInputParser.Metric.count
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end


