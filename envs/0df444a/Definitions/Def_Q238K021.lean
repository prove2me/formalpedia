-- Prove2me | Definitions.Def_Q238K021
-- name    : Q238K021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:17:15.37844+00:00
-- url     : https://prove2.me/theorems/2d01807d-5f03-442a-b1e3-7a3a7b163267
-- title:
--   Definitions bundle Q238K021 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 139 declarations of OpenAI's Lean: 130 definitions, 4 inductive types or structures, 1 instance and 4 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClassFilter.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionPad.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.endLeaf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafPrefix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.outputBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.fallbackInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.nonempty`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.ctxBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.nodeBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.resultBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.accBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.counts`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.stateEncode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidGrid.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.resultBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.historyBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.A.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.integralPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.P.budget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.scales`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.bracketInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.far`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.high` and 94 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_GlobalZero`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CompletionFillMath`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_DuplicateMatrix`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_RationalLeaves`, `KMedianRecovery_Encoding_RationalStream`, `KMedianRecovery_Encoding_Reencode`, `KMedianRecovery_Encoding_UnaryParser`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_LocalCandidates`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Geometry_MetricParser`, `KMedianRecovery_Geometry_NearestLeafMachine`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_CoupledPrimitives`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_DeleteSize`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_LoopInvariant`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_NormalizationMachine`, `KMedianRecovery_Machines_ProjectionMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_ClassFilter`, `KMedianRecovery_Recovery_CoupledInitial`, `KMedianRecovery_Recovery_CoupledResolve`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_FiniteCross`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_LeafOrder`, `KMedianRecovery_Recovery_LengthCandidates`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_Pack10`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplingPotential`, `KMedianRecovery_Strictness_MetricSurplus`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K006`, `Q238K007`, `Q238K008`, `Q238K009`, `Q238K010`, `Q238K011`, `Q238K012`, `Q238K013` and `Q238K014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K026` and `Q238K027`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryDecision_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFace_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningConstant_constant_source_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningPayment_nearest_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238`, `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238`, `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238` and `OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls_nil_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFace_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238`, `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238`, `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238` and `OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K006
import Definitions.Def_Q238K007
import Definitions.Def_Q238K008
import Definitions.Def_Q238K009
import Definitions.Def_Q238K010
import Definitions.Def_Q238K011
import Definitions.Def_Q238K012
import Definitions.Def_Q238K013
import Definitions.Def_Q238K014

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Reencode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

noncomputable def PolyComputes.reencode {α β : Type} {f : α → β} {g : List Bool → List Bool}
    (h : PolyComputes g) (ea : α → List Bool) (eb : β → List Bool)
    (he : ∀ x, g (ea x) = eb (f x)) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := h.program.machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := h.time
  outputsFun x := by simpa [he x] using h.outputs (ea x)

end MetricKMedianRecovery.BitMachine

end OAI
end

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

def pack {n : ℕ} (rs : List (Row n)) (B : ℕ) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate rs.length true,
    pairBits (B.bits,BinaryRow.rowsEncode rs)))
end BinaryRationalDecision

open WordOperations
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack10
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningOracle
open WordOperations BinaryArithmetic RationalLinearFeasibility RationalOpenability
open EffectiveOpenability BinaryExactSolve

def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : List Bool :=
  BinaryRationalDecision.pack
    ((kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).map
      (fun r=>(forms distance F W v z lam eta i r).enumeratedRow (variableEnum d F)))
    ⌈(1+v^2)*z⌉₊

end MetricKMedianRecovery.BitMachine.BinaryOpeningOracle

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

def eventBits {m d : ℕ} (e : RationalPhase.Event m d) : List Bool :=
  pairBits (e.facility.val.bits,RationalMatrix.rowEncode (fun j=>e.bid[j]))
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

def Plan.common (H : List X) : Plan X → List X
  | .free _ _ => H
  | .paid C T _ => C++T

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

def rows {d : ℕ} (distance : V → Fin d → ℚ) : Label V → Fin d → ℚ :=
  fun x j=>match x with
  | .inl i => distance i j
  | .inr c => distance (root c) j+max c.2.2 0

variable [DecidableEq V]

def Before (key : ℕ) (B : Finset (Label V)) : Prop :=
  ∀ c,Sum.inr c∈B → c.1<key

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
instance labelLinearOrder {V : Type*} [LinearOrder V] : LinearOrder (Label V) :=
  inferInstanceAs (LinearOrder (V ⊕ₗ (ℕ ×ₗ (V ×ₗ ℚ))))
end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [DecidableEq V] {d : ℕ}

structure State (V : Type*) where
  B : Finset (Label V)
  P : List (List (Label V))
  correction : Correction V
  lam : ℚ
  lam' : ℚ
  T : List (List (Label V))
  U : List (List (Label V))

structure Output (V : Type*) where
  B : Finset (Label V)
  lam : ℚ
  P : List (List (Label V))

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledResolve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

abbrev Outcome (V : Type*) := Output V ⊕ State V

attribute [local instance] RationalLeaves.metric

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

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

def setBits {m : ℕ} (S : Finset (Label (Fin m))) : List Bool := labels (orderedSort S)
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels)

def historyBits {m : ℕ} (hs : List (List (Label (Fin m)))) : List Bool := encode (hs.map labels)
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )
lemma labels_append {m : ℕ} (xs ys : List (Label (Fin m))) : labels (xs++ys)=labels xs++labels ys := by
  simp only [labels,List.map_append,encode_append]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
def jumpBits {m : ℕ} : Jump (Label (Fin m)) → List Bool
  | .add i=>encode [(0:ℕ).bits,[],[],[],BinaryLabel.encode i]
  | .remove C T A i=>encode [(1:ℕ).bits,labels C,labels T,labels A,BinaryLabel.encode i]
  | .replace C T i=>encode [(2:ℕ).bits,labels C,labels T,[],BinaryLabel.encode i]
def ctxBits {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : List Bool := encode [setBits F,labels R,key.bits,labels H,labels G]

end MetricKMedianRecovery.BitMachine.BinaryJump

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
def pack (F U : Finset ℕ) (n : ℕ) : List Bool :=
  encode [BinaryNatSet.encode F,BinaryNatSet.encode U,n.bits]
end MetricKMedianRecovery.BitMachine.BinaryCompletionPad

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UnaryParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryParser
open WordOperations UnaryTake

lemma mass_next (x : List Bool) : mass (next x) ≤ mass x := by
  unfold next While.next
  split_ifs
  · unfold step
    cases hd : data x with
    | nil=>simp only [List.head?_nil,Option.getD_none,Bool.false_eq_true,ite_false, if_false,mass,counter_pack,
        data_pack,output_pack,List.tail_nil,List.length_nil,hd]; omega
    | cons b d=>cases b <;>
      simp only [List.head?_cons,Option.getD_some,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,mass,
        counter_pack,data_pack,output_pack,List.tail_cons,List.length_nil,List.length_cons,hd] <;> omega
  · exact le_rfl
lemma length_next (x : List Bool) : (next x).length ≤ max x.length (2*mass (next x)+3) := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs <;> simp only [length_pack,mass,counter_pack,data_pack,output_pack,List.length_nil] <;> omega
  · exact Nat.le_max_left _ _
lemma iterate_bounds (x : List Bool) (n : ℕ) :
    mass (next^[n] x)≤ mass x ∧ (next^[n] x).length≤ max x.length (2*mass x+3) := by
  induction n with
  | zero=>exact ⟨le_rfl,Nat.le_max_left _ _⟩
  | succ n ih=>
    rw [Function.iterate_succ_apply']
    have hm:=mass_next (next^[n] x)
    have hl:=length_next (next^[n] x)
    exact ⟨hm.trans ih.1,by omega⟩
end MetricKMedianRecovery.BitMachine.UnaryParser

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser
open WordOperations
attribute [local irreducible] UnaryParser.run UnaryTake.takeWords UnaryTake.dropWords
noncomputable def nat (x : List Bool) : List Bool :=
  pairBits (UnaryTake.takeWords (UnaryParser.run x),UnaryTake.dropWords (UnaryParser.run x))
attribute [local irreducible] nat
noncomputable def numerator (x : List Bool) : List Bool :=
  x.head?.getD false::extractPrefix (nat x.tail)
noncomputable def denominator (x : List Bool) : List Bool := nat (discardPrefix (nat x.tail))
attribute [local irreducible] numerator denominator
noncomputable def rational (x : List Bool) : List Bool :=
  pairBits (pairBits (numerator x,extractPrefix (denominator x)),discardPrefix (denominator x))
end MetricKMedianRecovery.BitMachine.BinaryInputParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream
open WordOperations
noncomputable def step (x : List Bool) : List Bool :=
  if extractPrefix x=[] then x else
    pairBits (discardPrefix (rational (extractPrefix x)),
      WordList.cons (extractPrefix (rational (extractPrefix x))) (discardPrefix x))
attribute [local irreducible] rational
noncomputable def run (x : List Bool) : List Bool :=
  WordList.reverse (discardPrefix (BoundedIteration.polynomialRun step Polynomial.X (3*Polynomial.X+1) (pairBits (x,[]))))
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
attribute [local irreducible] nat RawDrop.run Stream.run RawUnary.run
noncomputable def header (x : List Bool) : List Bool := nat x
noncomputable def count (x : List Bool) : List Bool := extractPrefix (header x)
noncomputable def tailHeader (x : List Bool) : List Bool := nat (discardPrefix (header x))
noncomputable def budget (x : List Bool) : List Bool := extractPrefix (tailHeader x)
noncomputable def masks (x : List Bool) : List Bool := discardPrefix (tailHeader x)
noncomputable def afterClients (x : List Bool) : List Bool := RawDrop.run (pairBits (count x,masks x))
noncomputable def rawMatrix (x : List Bool) : List Bool := RawDrop.run (pairBits (count x,afterClients x))
attribute [local irreducible] header count tailHeader budget masks afterClients rawMatrix
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMaskParser
open WordOperations WordList
noncomputable def member (x : List Bool) : Bool :=
  (RawDrop.run (pairBits (discardPrefix x,extractPrefix x))).head?.getD false
end MetricKMedianRecovery.BitMachine.BinaryMaskParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCopyTables
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n a : ℕ}
def pack (H : Fin a→Finset (Fin n)) : List Bool :=
  encode [List.replicate n true,encode (List.ofFn (fun i=>BinaryFinSet.encode (H i)))]
attribute [local irreducible] mapWith flatMapWith
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

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
noncomputable def op (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (extractPrefix x)*BinaryRational.decode (discardPrefix (discardPrefix x)))
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
def optBits (o : Option ℚ) : List Bool := encode (o.toList.map BinaryRational.encode)
def radii (κ pop : ℚ) (near : Option ℚ) : List Bool := encode [BinaryRational.encode κ,BinaryRational.encode pop,optBits near]
noncomputable def divide (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (discardPrefix x)/BinaryRational.decode (extractPrefix x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMenu

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestLeafMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNearestLeaf
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def distances (x : List Bool) : List Bool := mapWith (fun z=>BinaryRational.encode (distance z)) x
noncomputable def run (x : List Bool) : List Bool :=
  if empty x then [] else encode [RationalMin.run (distances x)]
end MetricKMedianRecovery.BitMachine.BinaryNearestLeaf

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInverseCDF
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open Dyadic.Canonical

attribute [local irreducible] UnaryResources.inc
attribute [local irreducible] NaturalArray.sumWords

def pack (d : ℕ) (ws : List ℕ) (tape : List Bool) : List Bool := encode [d.bits,NaturalArray.encode ws,tape]
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )

def pack (b d : ℕ) (ps : List ℚ) (raw : List Bool) : List Bool :=
  encode [List.replicate b true,RationalArray.encode ps,d.bits,raw]
noncomputable def counts (x : List Bool) : List Bool :=
  mapWith count (pairBits (BinaryRational.encode (scale (field 0 x)),field 1 x))
noncomputable def prepared (x : List Bool) : List Bool := encode [field 2 x,counts x,field 3 x]
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricArrays
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n p q : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (rows : Fin p→Fin n) (cols : Fin q→Fin n) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.table rows,BinaryFinSet.table cols]
noncomputable def column (x : List Bool) : List Bool := BinaryIndexMap.run
  (pairBits (row x,field 2 (extractPrefix x)))
attribute [local irreducible] BinaryIndexMap.run
noncomputable def run (x : List Bool) : List Bool := mapWith column (pairBits (x,field 1 x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMetricArrays

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricCost
open WordOperations WordList
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode S]
noncomputable def near (x : List Bool) : List Bool := RationalMin.run (discardPrefix x)
noncomputable def run (x : List Bool) : List Bool := RationalArray.sumWords
  (mapWith near (pairBits ([],BinaryMetricArrays.run x)))
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def score (x : List Bool) : List Bool := BinaryRational.negWords (BinaryMetricCost.run
  (encode [field 0 (extractPrefix x),field 1 (extractPrefix x),discardPrefix x]))
def context (δ : Fin n→Fin n→ℚ) (D : Finset (Fin n)) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D]
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

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
noncomputable def pack (ctx : List Bool) (part : Fin q→Fin a)
    (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool) : List Bool :=
  pairBits (encode [ctx,partBits part,List.replicate a true],Tape.raw q a (exponent a) (samples q a) bits)
attribute [local irreducible] dimensions
attribute [local irreducible] RawDrop.run
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
def pack (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (o : Fin a→Fin q) (loc : Fin q→Fin n)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n) (k : ℕ)
    (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ) (weight redBase : Fin r→ℚ)
    (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) : List Bool :=
  encode [BinaryFinSet.encode F,BinaryFinSet.encode S,BinaryFinSet.encode Q,
    BinaryFinSet.table part,BinaryFinSet.table o,BinaryFinSet.table loc,
    BinaryFinSet.table redLoc,BinaryFinSet.table blueLoc,BinaryFinSet.table blueDest,
    encode (xs.map BinaryCategorical.elemBits),BinaryCompletion.contextBits k base distance weight redBase redDistance]
attribute [local irreducible] fillInput
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryClassFilter
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
def pack (S : Finset (Fin n)) (label : Fin n→Fin m) (c : Fin m) : List Bool :=
  pairBits (pairBits (BinaryFinSet.table label,c.val.bits),BinaryFinSet.encode S)
end MetricKMedianRecovery.BitMachine.BinaryClassFilter

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList
open BinaryOpeningPayment (field )
attribute [local irreducible] zeroContext
noncomputable def choices (x : List Bool) : List Bool := cross (pairBits (range x,cross (pairBits (range x,blueRange x))))
attribute [local irreducible] mapWith
attribute [local irreducible] metricContext
end MetricKMedianRecovery.BitMachine.BinaryRecovery

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
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,
    BinaryFinSet.encode S,Δ.bits,BinaryRational.encode P,m.bits]
attribute [local irreducible] bound
noncomputable def diameter (x : List Bool) : List Bool := BinaryRational.natWords (field 5 x)
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
noncomputable def next (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (s : Option (State n)) (seed : Fin b→Bool) : Option (State n) :=
  update δ D F S Δ P κ m M E J s (Dyadic.Canonical.draw
    (fun a=>(transitionWeight δ D S Δ M E J s a:ℝ)) b (Sum.inl ()) (actions D M E J) seed)
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList
open BinaryOpeningPayment (field )
attribute [local irreducible] src extra completeRaw BinaryRational.natWords
attribute [local irreducible] mapWith
def pack {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (extra : List Bool) (seed : Fin (2*m)→Fin b→Bool) (complete : List Bool) : List Bool :=
  pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,
    pairBits (extra,pairBits (BinarySeed.raw (ds:=[2*m]) seed,complete)))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations WordList Sampling.Comparison BinaryArithmetic
attribute [local irreducible] raw extra RawDrop.run
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (g bits : List Bool) : List Bool := pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,pairBits (g,bits))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryGuesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryFinSet.encode Count.run src
noncomputable def price (x : List Bool) : List Bool := BinaryRational.natWords (extractPrefix (discardPrefix x))
noncomputable def atParams (x : List Bool) : List Bool := encode
  [source 0 x,source 1 x,source 2 x,source 3 x,source 4 x,source 5 x,price x,count x]
noncomputable def atInput (x : List Bool) : List Bool := pairBits (atParams x,pairBits
  (extra (extractPrefix x),Fair.raw (extractPrefix x)))
attribute [local irreducible] mapWith
variable {n : ℕ}
abbrev pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool) : List Bool :=
  Fair.pack δ D F S Δ 0 0 g raw
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LengthEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
def planBits {m : ℕ} : Plan (Label (Fin m)) → List Bool
  | .free i f=>encode [(0:ℕ).bits,BinaryLabel.encode i,BinaryLabel.encode f,[],[]]
  | .paid C T i=>encode [(1:ℕ).bits,BinaryLabel.encode i,[],labels C,labels T]
end MetricKMedianRecovery.BitMachine.BinaryLength

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

def ctxBits {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) : List Bool := encode [setBits F,setBits Q,k.bits]
def nodeBits {m : ℕ} (P : List (Label (Fin m)) × List (List (Label (Fin m)))) : List Bool :=
  pairBits (labels P.1,historyBits P.2)
end MetricKMedianRecovery.BitMachine.BinaryCross

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

def ctxBits {m : ℕ} (base : List Bool) (n q key : ℕ) (root : Label (Fin m)) (b : ℚ)
    (T U : List (List (Label (Fin m)))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,key.bits,BinaryLabel.encode root,BinaryRational.encode b,
    historyBits T,historyBits U]
noncomputable def newLeaf (x : List Bool) : List Bool :=
  pairBits ((value (cf 3 x)+1).bits,pairBits (BinaryLabel.parentWords (cf 4 x),discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

namespace MetricKMedianRecovery.BitMachine.BinaryLengthSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
def resultBits {m : ℕ} : CanonicalLengthSearch.Result (Label (Fin m))→List Bool
  | .success s T=>encode [(0:ℕ).bits,BinaryRational.encode s,[],historyBits T,[]]
  | .bracket l u T U=>encode [(1:ℕ).bits,BinaryRational.encode l,BinaryRational.encode u,historyBits T,historyBits U]
end MetricKMedianRecovery.BitMachine.BinaryLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SensitiveMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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
noncomputable def small (x : List Bool) : List Bool := if isFree x then field 9 x else field 8 x
noncomputable def large (x : List Bool) : List Bool := if isFree x then field 8 x else field 9 x
noncomputable def early (x : List Bool) : List Bool := encode [(0:ℕ).bits,BinaryRational.encode 0,[],small x,[]]
end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalCandidates
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCost
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
def connection {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) (j : Fin d) : ℚ :=
  RationalMin.minimum ((BinaryLabel.orderedSort S).map (fun a=>rows distance a j))
def cost {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) : ℚ := ∑ j,connection distance S j
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

namespace MetricKMedianRecovery.BitMachine.BinaryLocalBest
open WordOperations WordList BinaryArithmetic
noncomputable def run (rank : List Bool→List Bool) (x : List Bool) : List Bool :=
  CappedFold.run (choose rank) (pairBits (x,Fold.pack (discardPrefix (discardPrefix x)) (extractPrefix x)
    (extractPrefix (discardPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryLocalBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

inductive StartOutput (V : Type*) where
  | small (o : Output V)
  | normal (o : Output V)

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

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
noncomputable def originalWord (x : List Bool) : List Bool :=
  pairBits ((0:ℕ).bits,pairBits (x,BinaryRational.encode 0))
end MetricKMedianRecovery.BitMachine.BinaryProjection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricAnchor
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryMetricArrays.run
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,r.bits]
noncomputable def rectangle : List Bool→List Bool := BinaryMetricArrays.run ∘ rectInput
noncomputable def anchorInput (x : List Bool) : List Bool := encode [rectangle x,Count.run (field 2 x),
  map BinaryProjection.originalWord (field 3 x),field 4 x]
attribute [local irreducible] WordList.map
attribute [local semireducible] WordList.map
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

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
namespace R
abbrev pack := @BinaryIntegralRecovery.Guesses.pack
end R
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,Δ.bits,k.bits,g,raw]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CoupledEncode
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
def outputBits {m : ℕ} (o : Output (Fin m)) : List Bool := encode [setBits o.B,BinaryRational.encode o.lam,historyBits o.P]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [LinearOrder V] {d : ℕ}
structure Frame (V : Type*) where
  q : ℕ
  n : ℕ
  out : Outcome V

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossEdge
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

def resultBits {m : ℕ} : CanonicalMergeCrossing.Result (Label (Fin m)) → List Bool
  | .success H T=>encode [(0:ℕ).bits,nodeBits (H,T),[]]
  | .common H T U=>encode [(1:ℕ).bits,nodeBits (H,T),historyBits U]
  | .sensitive H G T U=>encode [(2:ℕ).bits,nodeBits (H,T),nodeBits (G,U)]
def pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) : List Bool :=
  pairBits (ctxBits F Q k,pairBits (nodeBits P,nodeBits R))
end MetricKMedianRecovery.BitMachine.BinaryCross

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
noncomputable def frees (x : List Bool) : List Bool := crossWith freeOp (pairBits (field 1 x,field 3 x))
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

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def makeLeaf (x : List Bool) : List Bool :=
  pairBits ((value (field 0 x)+1).bits,pairBits (parentWords (field 1 x),field 2 x))
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

def leafPack {m : ℕ} (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (lam : ℚ)
    (key : ℕ) (i : Label (Fin m)) (C : List (Label (Fin m))) (l u : ℚ) (T U : List (List (Label (Fin m)))) : List Bool :=
  encode [setBits B,historyBits P,BinaryRational.encode lam,key.bits,BinaryLabel.encode i,labels C,
    BinaryRational.encode l,BinaryRational.encode u,historyBits T,historyBits U]
noncomputable def endLeaf (j : ℕ) (x : List Bool) : List Bool := BinaryLabel.makeLeaf (encode [field 3 x,field 4 x,field j x])
noncomputable def leafPrefix (x : List Bool) : List Bool := field 1 x++cons (field 5 x++cons (endLeaf 7 x) []) []
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )

def accBits {m : ℕ} (s : Acc (Label (Fin m))) : List Bool :=
  encode [labels s.remaining,labels s.extras,historyBits s.vertices]
end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

def pack {m : ℕ} (base : List Bool) (C : List (Label (Fin m))) (ci : Label (Fin m))
    (U E : List (Label (Fin m))) : List Bool :=
  Fold.pack (labels U) (contextBits base (labels C) (BinaryLabel.encode ci)) (accBits ⟨U,E,[]⟩)

end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )

def accBits {m : ℕ} (s : Acc (Label (Fin m))) : List Bool :=
  encode [labels s.front,labels s.rest,historyBits s.vertices]
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.FirstPresent
open WordOperations
open CanonicalMergeCrossing
noncomputable def found (x : List Bool) : List Bool := Find.run present (pairBits ([],discardPrefix x))
noncomputable def run (x : List Bool) : List Bool := if found x=[] then extractPrefix x else (found x).tail.tail
end MetricKMedianRecovery.BitMachine.WordList.FirstPresent

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
def pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (nodes : List (List (Label (Fin m)) × List (List (Label (Fin m))))) : List Bool :=
  encode [ctxBits F Q k,historyBits U,encode (nodes.map nodeBits)]
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

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
def pack {m : ℕ} (base : List Bool) (key spare k n q : ℕ) (H G : List (Label (Fin m)))
    (T U : List (List (Label (Fin m)))) : List Bool :=
  encode [base,key.bits,spare.bits,k.bits,List.replicate n true,List.replicate q true,labels H,labels G,historyBits T,historyBits U]
end MetricKMedianRecovery.BitMachine.BinaryFiniteCross

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
noncomputable def fallbackInput (x : List Bool) : List Bool := encode [sf 0 x,sf 3 x,sf 1 x,(fun _=>[]) x]
noncomputable def nonempty (x : List Bool) : Bool := (!(decide (sf 5 x=[]))) && (!(decide (sf 6 x=[])))
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_InitialLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (outputBits)
def output {m : ℕ} : StartOutput (Fin m)→List Bool
  | .small o=>pairBits ([],outputBits o)
  | .normal o=>pairBits ([true],outputBits o)
noncomputable def high (x : List Bool) : List Bool := BinaryRational.encode
  (8*((field 1 (field 0 x)).length:ℚ)*BinaryRational.decode (field 6 x))
noncomputable def far (x : List Bool) : List Bool := BinaryRational.encode
  (20*((field 1 x).length:ℚ)*BinaryRational.decode (field 6 x))

noncomputable def bracketInput (x : List Bool) : List Bool := encode [(field 2) x,(ctx) x,(field 4) x,(field 5) x,(high) x]

end MetricKMedianRecovery.BitMachine.BinaryInitial

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

def step (K : ℚ) (x : List Bool) : List Bool :=
  if threshold x ≤ power x then x else
    pairBits (extractPrefix x,pairBits (BinaryRational.encode (K*power x),true::count x))

def coefficient (K : ℚ) (C : ℕ) : ℕ := 6*C*(BinaryRational.encode K).length+C+16

def initial (x : List Bool) : List Bool := pairBits (x,pairBits (BinaryRational.encode 1,[]))

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
noncomputable def low (x : List Bool) : List Bool := BinaryRational.encode (2/((size x).length:ℚ)^2)
noncomputable def threshold (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (field 4 x)+8*((field 1 x).length:ℚ)*BinaryRational.decode (field 4 x))
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_MetricSurplus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ h L : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,Δ.bits,h.bits,L.bits]
noncomputable def rectangle : List Bool→List Bool := BinaryMetricAnchor.rectangle ∘ anchorInput
noncomputable def initial (x : List Bool) : List Bool := encode [rectangle x,Count.run (field 2 x),field 3 x,field 2 x,
  BinaryRational.natWords (field 4 x),field 5 x]
noncomputable def runInput (x : List Bool) : List Bool := pairBits (initial x,total x)
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open WordOperations WordList
open BinaryOpeningPayment (field )
namespace Dsp
abbrev pack := @BinaryIntegralDispatch.pack
end Dsp
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DuplicateMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix
open WordOperations WordList
variable {n : ℕ}
noncomputable def run : List Bool→List Bool := twice ∘ map twice

end MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def distance (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (field 0 (ctx x),rowIndex x),colIndex x))
noncomputable def entryInput (x : List Bool) : List Bool := encode [distance x,field 2 (ctx x),field 3 (ctx x)]
noncomputable def entry (x : List Bool) : List Bool :=
  if value (rowIndex x)=value (colIndex x) then BinaryRational.encode 0 else BinaryRound.rational (entryInput x)
noncomputable def row (x : List Bool) : List Bool :=
  mapWith entry (pairBits (x,BinaryEllipsoidInitial.indices (field 1 (extractPrefix x))))
noncomputable def run (x : List Bool) : List Bool :=
  mapWith row (pairBits (x,BinaryEllipsoidInitial.indices (field 1 x)))
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
open BinaryOpeningPayment (field )
open IntegralAssembly (gammaRat)
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,List.replicate d true,BinaryRational.encode M]
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
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryInputParser.Metric.count BinaryInputParser.Metric.budget

noncomputable def count (x : List Bool) : List Bool := BinaryInputParser.Metric.count (raw x)
noncomputable def budget (x : List Bool) : List Bool := BinaryInputParser.Metric.budget (raw x)
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
open BinaryOpeningPayment (field )
namespace A
abbrev pack := @BinaryIntegralDispatch.pack
end A
def pack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) : List Bool :=
  encode [I.bits,BinaryRational.encode M,raw]
attribute [local irreducible] BinaryInputParser.Metric.count
noncomputable abbrev integralPack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :=
  A.pack (matrix I M) (I.clients.image BinaryTaggedSets.left) (I.facilities.image BinaryTaggedSets.right)
    (Rounding.cap I.clients.card (IntegralAssembly.gamma/16)) (min I.budget I.facilities.card) I.bits raw
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList LocalSearch
open BinaryOpeningPayment (field )
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) : List Bool :=
  BinaryMetricArrays.pack δ (SortedIndex.enum D) (SortedIndex.enum F)
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

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
open BinaryOpeningPayment (field )
namespace P
noncomputable abbrev budget := BinaryInputParser.Metric.budget
end P
noncomputable def scales : List Bool→List Bool := BinaryInputParser.Stream.run ∘ BinaryInputParser.Metric.rawMatrix
attribute [local irreducible] BinaryInputParser.Metric.budget
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


