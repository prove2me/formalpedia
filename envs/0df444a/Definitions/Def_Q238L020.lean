-- Prove2me | Definitions.Def_Q238L020
-- name    : Q238L020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:23:49.036389+00:00
-- url     : https://prove2.me/theorems/bb0d0c3a-214d-485d-b78f-6cd8edff6fb0
-- title:
--   Definitions bundle Q238L020 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 133 declarations of OpenAI's Lean: 114 definitions, 9 inductive types or structures, 2 instances and 8 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.normInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.callInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.boundK`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.lower`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.upper`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.historyBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.ctx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.codes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.less`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.src`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.surplusInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.atSeedInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalBest.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.code`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.exponent`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.first`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.kind`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.relative`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.weights`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.anchorInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.total`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.distance`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNearestLeaf.empty`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.indices`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.variableWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.kindWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPopulation.near`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalBest.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalPower.items`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.choiceBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRound.ceil`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRound.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRound.positive`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRound.rational`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.colIndex`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.ctx` and 83 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_Encode`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_Encode3`, `KMedianRecovery_Encoding_HistoryBits`, `KMedianRecovery_Encoding_Matrix`, `KMedianRecovery_Encoding_RationalBest`, `KMedianRecovery_Encoding_RationalLeaves`, `KMedianRecovery_Encoding_RationalStream`, `KMedianRecovery_Encoding_Reencode`, `KMedianRecovery_Encoding_UnaryParser`, `KMedianRecovery_Geometry_FamilyMetric`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_NearestLeafMachine`, `KMedianRecovery_Geometry_RoundingArithmetic`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_FirstSize`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_MergeResources`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Machines_StartResources`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_CanonicalParents`, `KMedianRecovery_Recovery_CommonL`, `KMedianRecovery_Recovery_Coupled`, `KMedianRecovery_Recovery_Entry`, `KMedianRecovery_Recovery_FacePoint`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_FiniteContinuation`, `KMedianRecovery_Recovery_FiniteCross`, `KMedianRecovery_Recovery_IfNat`, `KMedianRecovery_Recovery_LeafOutcome`, `KMedianRecovery_Recovery_MergeCross`, `KMedianRecovery_Recovery_MergePath`, `KMedianRecovery_Recovery_MergeRefine`, `KMedianRecovery_Recovery_NearEligible`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_Pool`, `KMedianRecovery_Recovery_RawSlices`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Recovery_Row`, `KMedianRecovery_Recovery_SingleRadiusRatio`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_StoredForms`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Sampling_PrefixData`, `KMedianRecovery_Sampling_RealizedKernel`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerTraceMachine`, `KMedianRecovery_Sampling_SamplerWeights`, `KMedianRecovery_Sampling_SamplingPotential`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Sampling_SeedTensor`, `KMedianRecovery_Strictness_Clipped`, `KMedianRecovery_Strictness_MetricSurplus`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L006`, `Q238L008`, `Q238L009`, `Q238L010` and `Q238L011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L025` and `Q238L026`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.tableRun_best_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.table_length_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238r`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec_s238r`, `OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec_s238r`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinePath_spec_s238r`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238r`, `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq_s238r`, `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238r`, `OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238r`, `OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238r`, `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238r`, `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238r`, `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238r`, `OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238r`, `OAI.MetricKMedianRecovery.RationalPhase.completion_spec_s238r` and `OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal_s238r`; the proofs of `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec_s238r`, `OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec_s238r`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinePath_spec_s238r`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238r`, `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238r`, `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238r`, `OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238r`, `OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238r`, `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238r`, `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238r`, `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238r`, `OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238r`, `OAI.MetricKMedianRecovery.RationalPhase.completion_spec_s238r`, `OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal_s238r` and `OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L006
import Definitions.Def_Q238L008
import Definitions.Def_Q238L009
import Definitions.Def_Q238L010
import Definitions.Def_Q238L011

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

def Row.Holds {n : ℕ} (r : Row n) (x : Fin n → ℚ) : Prop := r.value x ≤ r.bound
instance instDecidableHolds {n : ℕ} (r : Row n) (x : Fin n → ℚ) : Decidable (r.Holds x) := inferInstanceAs (Decidable (_ ≤ _))

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FacePoint
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def facePoint {n : ℕ} (rows : List (Row n)) (B : ℕ) : Fin n → ℚ :=
  let picked := finalFace rows B
  let C := rowMatrix picked
  let G := PositiveSolve.freezeMat (Cᵀ*C)
  let d := PositiveSolve.freezeVec (Cᵀ *ᵥ rowBounds picked)
  PositiveSolve.solve n G d

def exactSolve {n : ℕ} (rows : List (Row n)) (B : ℕ) : Option (Fin n → ℚ) :=
  if boundedRationalDecide rows B then some (facePoint rows B) else none

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic
namespace WordList.Lookup

lemma step_zero (ws : List (List Bool)) :
    step (pairBits (Nat.bits 0,encode ws))=pairBits (Nat.bits 0,encode ws) := by
  simp only [step,extractPrefix_pairBits,value_bits,ite_true, if_true]
lemma step_succ (i : ℕ) (ws : List (List Bool)) :
    step (pairBits ((i+1).bits,encode ws))=pairBits (i.bits,encode ws.tail) := by
  simp only [step,extractPrefix_pairBits,value_bits,Nat.add_eq_zero_iff,Nat.one_ne_zero,
    and_false,ite_false, if_false,Nat.add_sub_cancel,discardPrefix_pairBits]
  cases ws with
  | nil => rfl
  | cons w ws => simp only [encode,tail_cons,List.tail_cons]
lemma head_iterate (n i : ℕ) (ws : List (List Bool)) (hn : ws.length ≤ n) :
    WordList.head (discardPrefix (step^[n] (pairBits (i.bits,encode ws))))=ws[i]?.getD [] := by
  induction n generalizing i ws with
  | zero =>
    have hw : ws=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst ws
    simp only [Function.iterate_zero_apply,discardPrefix_pairBits,encode,List.getElem?_nil,Option.getD_none]
    rfl
  | succ n ih =>
    cases i with
    | zero =>
      rw [Function.iterate_fixed (step_zero ws)]
      rw [discardPrefix_pairBits]
      cases ws with
      | nil => rfl
      | cons w ws => simp only [encode,head_cons,List.getElem?_cons_zero,Option.getD_some]
    | succ i =>
      rw [Function.iterate_succ_apply,step_succ]
      have hl : ws.tail.length ≤ n := by simp only [List.length_tail]; omega
      rw [ih i ws.tail hl]
      cases ws <;> rfl
end WordList.Lookup
end
open WordOperations
namespace WordList
namespace Fold

def operation (f : List Bool → List Bool) (ctx : List Bool) (a w : List Bool) : List Bool :=
  f (pairBits (ctx,pairBits (w,a)))
end Fold
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace IntegerArray

def encode (xs : List ℤ) : List Bool := WordList.encode (xs.map Signed.encode)
end IntegerArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalArray
open RationalHeight
def encodePairs (xs : List (ℚ×ℚ)) : List Bool :=
  WordList.encode (xs.map (fun p=>pairBits (BinaryRational.encode p.1,BinaryRational.encode p.2)))
end RationalArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NaturalArray
open WordList
def encode (xs : List ℕ) : List Bool := WordList.encode (xs.map Nat.bits)
end NaturalArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryOpeningActivity
open WordList

def indices {m : ℕ} (fs : List (Fin m)) : List Bool :=
  WordList.encode (fs.map (fun f=>f.val.bits))
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningConstant
open WordList RationalLinearFeasibility RationalOpenability

def kindWord {m d : ℕ} {F W : Finset (Fin m)} : Kind (Fin d) W F → List Bool
  | .lower j=>encode [(0:ℕ).bits,j.val.bits]
  | .upper j=>encode [(1:ℕ).bits,j.val.bits]
  | .cap j f=>encode [(2:ℕ).bits,j.val.bits,f.val.val.bits]
  | .far j=>encode [(3:ℕ).bits,j.val.bits]
  | .payment=>encode [(4:ℕ).bits]
  | .slackZero f a j=>encode [(5:ℕ).bits,j.val.bits,f.val.val.bits,a.val.bits]
  | .slackTerm f a j=>encode [(6:ℕ).bits,j.val.bits,f.val.val.bits,a.val.bits]
  | .dual f a=>encode [(7:ℕ).bits,a.val.bits,f.val.val.bits]

end BinaryOpeningConstant
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_IfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningCoefficient
open WordList RationalLinearFeasibility RationalOpenability

def variableWord {m d : ℕ} {F : Finset (Fin m)} : Variables (Fin d) F → List Bool
  | .inl j=>encode [(0:ℕ).bits,j.val.bits]
  | .inr (f,a,j)=>encode [(1:ℕ).bits,f.val.val.bits,a.val.bits,j.val.bits]
end BinaryOpeningCoefficient
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Matrix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid.Stored
open Matrix RationalLinearFeasibility
open scoped BigOperators

def point {n : ℕ} (picked : List (Row n)) : Fin n → ℚ :=
  let C := matrix (rowMatrix picked)
  let G := matrix (Cᵀ*C)
  let d := vector (Cᵀ *ᵥ rowBounds picked)
  BirdRational.solve G d

def facePoint {n : ℕ} (rows : List (Row n)) (B : ℕ) : Fin n → ℚ :=
  point (finalFace rows B)

def exactSolve {n : ℕ} (rows : List (Row n)) (B : ℕ) : Option (Fin n → ℚ) :=
  if boundedRationalDecide rows B then some (facePoint rows B) else none

end MetricKMedianRecovery.Ellipsoid.Stored

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
open scoped BigOperators
variable {V R : Type*} [Fintype V] {n : ℕ}

def storedForms (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ) :
    Option (V → ℚ) :=
  (Ellipsoid.Stored.exactSolve (rows.map (fun r => (f r).enumeratedRow e)) B).map
    (fun y v => y (e.symm v))

end MetricKMedianRecovery.RationalLinearFeasibility

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability OpenabilityLinearization

def storedOpening {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : Option (Variables (Fin d) F → ℚ) :=
  storedForms (variableEnum d F)
    (kindRows (List.ofFn (fun j : Fin d => j)) (subtypeList W) (subtypeList F))
    (forms distance F W v z lam eta i) ⌈(1+v^2)*z⌉₊

end MetricKMedianRecovery.EffectiveOpenability

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer OpenabilityLinearization

def first {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) : List (Fin m) → Option (Event m d)
  | [] => none
  | i::todo =>
    if i∈F ∧ i∉W then
      match storedOpening distance F W v z lam 0 i with
      | none => first distance F W v z lam todo
      | some x => some ⟨i,Vector.ofFn (fun j => x (.inl j))⟩
    else first distance F W v z lam todo

def finish {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) : ℕ → State m d → State m d × List (Event m d)
  | 0,s => (s,[])
  | fuel+1,s =>
    match first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m => i)) with
    | none => (s,[])
    | some e =>
      let r := finish distance F v lam fuel (update distance v s e)
      (r.1,e::r.2)

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_Clipped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer

def run {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) : ℕ → State m d → State m d × List (Instruction m d)
  | 0,s => (s,[])
  | q+1,s =>
      let r := finish distance F v lam F.card s
      let u := advance distance v r.1
      let t := run distance F v lam q u
      (t.1,r.2.map Instruction.opening ++ Instruction.advance::t.2)

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Entry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Valid (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X) : Prop :=
  Prefix loc F B v z lam eta Q H ∧ Maximal loc F (Q ∪ H.toFinset) v z lam

end PhaseSequence
end MetricKMedianRecovery
namespace MetricKMedianRecovery.PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive History (loc : D → X) (F B : Finset X) (v lam eta : ℝ) :
    ℕ → Finset X → List (List X) → Prop
  | nil (q Q) : History loc F B v lam eta q Q []
  | cons {q Q H T} (head : PhaseSequence.Valid loc F B Q v ((1+v^2)^q) lam eta H)
      (tail : History loc F B v lam eta (q+1) (Q ∪ H.toFinset) T) :
      History loc F B v lam eta q Q (H::T)

end MetricKMedianRecovery.PhaseHistoryTransfer
namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Attains (loc : D → X) (F B Q : Finset X) (v lam : ℝ) (q n c : ℕ) : Prop :=
  ∃ T : List (List X), T.length = n ∧ History loc F B v lam 0 q Q T ∧
    Regular F T ∧ ((after Q T) ∩ F).card = c

end MetricKMedianRecovery.PhaseMergeCompletion
namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion OrdinaryProducer

def historyRun {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) : ℕ → State m d → State m d × List (List (Fin m))
  | 0,s => (s,[])
  | n+1,s =>
    let r := finish distance F v lam F.card s
    let u := advance distance v r.1
    let t := historyRun distance F v lam n u
    (t.1,(r.2.map Event.facility)::t.2)

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_HistoryBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryHistoryRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase
def historyBits {m : ℕ} (hs : List (List (Fin m))) : List Bool :=
  encode (hs.map BinaryOpeningActivity.indices)
end MetricKMedianRecovery.BitMachine.BinaryHistoryRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergePath
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Good (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam eta : ℝ)
    (H : List X) : Prop :=
  Valid loc F (pool F B copy) Q v z lam eta H ∧ (H.toFinset \ F).card ≤ 1

inductive Walk (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam eta : ℝ) :
    ℕ → List X → List X → Prop
  | nil {H} (hgood : Good loc F B Q copy v z lam eta H) :
      Walk loc F B Q copy v z lam eta 0 H H
  | cons {n H G J} (hgood : Good loc F B Q copy v z lam eta H)
      (hstep : Step loc F B Q copy v z lam H G)
      (tail : Walk loc F B Q copy v z lam eta n G J) :
      Walk loc F B Q copy v z lam eta (n+1) H J

end MetricKMedianRecovery.PhaseMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion OrdinaryProducer

def completion {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v z lam : ℚ) (Q : Finset (Fin m)) : List (Fin m) :=
  (finish distance F v lam F.card ⟨Q,z,Vector.replicate d 0⟩).2.map Event.facility

end MetricKMedianRecovery.RationalPhase

namespace MetricKMedianRecovery.CanonicalMergePath
open PhaseSequence PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def CorrectCompletion (loc : D → X) (F : Finset X) (v z lam : ℝ)
    (complete : Finset X → List X) : Prop :=
  ∀ B Q, Q ⊆ F ∪ B → Valid loc F B Q v z lam 0 (complete Q) ∧
    (∀ i ∈ complete Q, i ∈ F)

inductive Path (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam eta : ℝ) :
    List X → List (List X) → List X → Prop
  | nil {H} (h : Good loc F B Q copy v z lam eta H) : Path loc F B Q copy v z lam eta H [] H
  | cons {H G T J} (h : Good loc F B Q copy v z lam eta H)
      (e : Step loc F B Q copy v z lam H G)
      (t : Path loc F B Q copy v z lam eta G T J) :
      Path loc F B Q copy v z lam eta H (G::T) J

end MetricKMedianRecovery.CanonicalMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeRefine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeRefinement

section
open PhaseSequence PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Good (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X) : Prop :=
  Valid loc F B Q v z lam eta H ∧ (H.toFinset \ F).card ≤ 2

inductive Chain (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) :
    ℕ → List X → List X → Prop
  | nil {H} (hgood : Good loc F B Q v z lam eta H) : Chain loc F B Q v z lam eta 0 H H
  | cons {n H G J} (hgood : Good loc F B Q v z lam eta H)
      (hstep : Adjacent loc F B Q H G) (tail : Chain loc F B Q v z lam eta n G J) :
      Chain loc F B Q v z lam eta (n+1) H J

end

open PhaseSequence PhaseMergePath

end MetricKMedianRecovery.PhaseMergeRefinement

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseSequence PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive EPath (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) :
    List X → List (List X) → List X → Prop
  | nil {H} (h : PhaseMergeRefinement.Good loc F B Q v z lam eta H) :
      EPath loc F B Q v z lam eta H [] H
  | cons {H G T J} (h : PhaseMergeRefinement.Good loc F B Q v z lam eta H)
      (e : Adjacent loc F B Q H G) (t : EPath loc F B Q v z lam eta G T J) :
      EPath loc F B Q v z lam eta H (G::T) J

end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Runs (loc : D → X) (F B Q : Finset X) (v lam : ℝ) (q n : ℕ)
    (T : List (List X)) : Prop :=
  T.length = n ∧ History loc F B v lam 0 q Q T ∧ Regular F T

lemma Runs.attains {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (h : Runs loc F B Q v lam q n T) :
    Attains loc F B Q v lam q n ((after Q T) ∩ F).card := ⟨T,h.1,h.2.1,h.2.2,rfl⟩

def continuation {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q n : ℕ) (Q : Finset (Fin m)) : List (List (Fin m)) :=
  (RationalPhase.historyRun distance F v lam n ⟨Q,(1+v^2)^q,Vector.replicate d 0⟩).2

def Result.Correct (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q n k : ℕ) :
    Result X → Prop
  | .success H T => Good loc F B Q v ((1+v^2)^q) lam eta H ∧
      Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T ∧ finalCount F Q H T = k
  | .common H T U => Good loc F B Q v ((1+v^2)^q) lam eta H ∧
      Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T ∧
      Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n U ∧
      Sandwich k (finalCount F Q H T) (finalCount F Q H U)
  | .sensitive H G T U => Good loc F B Q v ((1+v^2)^q) lam eta H ∧
      Good loc F B Q v ((1+v^2)^q) lam eta G ∧ LengthEdit loc F B H G ∧
      Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T ∧
      Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n U ∧
      Sandwich k (finalCount F Q H T) (finalCount F Q G U)

end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_FamilyMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FreshCopyEndpoints
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

@[instance_reducible]
noncomputable def familyMetric (i : X) : PseudoMetricSpace (X ⊕ ℝ) :=
  LeafMetric.attachedMetric (fun _ : ℝ => i) (fun s => max s 0) (fun _ => le_max_right _ _)

end MetricKMedianRecovery.FreshCopyEndpoints

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_PrefixData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeInvariant
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
universe uD uX uY
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

structure PrefixData (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
    (q : ℕ) (P : List (List X)) : Prop where
  length_eq : P.length = q
  history : History loc F B v lam eta 0 ∅ P
  free_bound : ∀ H ∈ P, (H.toFinset \ F).card ≤ 3
  row : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (after ∅ P) i ≤ lam

end MetricKMedianRecovery.PhaseMergeInvariant

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Coupled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

structure Coupled (loc : D → X) (F : Finset X) (v eta lo hi : ℝ) (q n k : ℕ) where
  B : Finset X
  P : List (List X)
  r : X → X
  lam : ℝ
  lam' : ℝ
  eps : ℝ
  a : ℕ
  b : ℕ
  disjoint : Disjoint F B
  low : lo ≤ lam
  high : lam' ≤ hi
  price : lam ≤ lam'
  eps_nonneg : 0 ≤ eps
  error : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta
  inj : Function.Injective r
  fixed : ∀ i ∈ F, r i = i
  shrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x
  loss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps
  old_prefix : PrefixData loc F B v lam eta q P
  new_prefix : PrefixData loc F (B.image r) v lam' eta q (P.map (List.map r))
  sandwich : Sandwich k a b
  new_tail : Attains loc F (B.image r) (after ∅ (P.map (List.map r))) v lam' q n a
  old_tail : Attains loc F B (after ∅ P) v lam q n b

end MetricKMedianRecovery.PhaseCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelContinuation
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

def complete (loc : Fin d → X) (distance : X → Fin d → ℚ) (F : Finset X) (v z lam : ℚ)
    (Q : Finset X) : List X :=
  (RationalPhase.completion (rows loc F Q distance) (select loc F Q F) v z lam
    (select loc F Q Q)).map (embed loc F Q)

def continuation (loc : Fin d → X) (distance : X → Fin d → ℚ) (F : Finset X) (v lam : ℚ)
    (q n : ℕ) (Q : Finset X) : List (List X) :=
  (CanonicalMergeCrossing.continuation (rows loc F Q distance) (select loc F Q F) v lam q n
    (select loc F Q Q)).map (List.map (embed loc F Q))

end MetricKMedianRecovery.FiniteLabelContinuation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing PhaseCountCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

def run (loc : Fin d → X) (distance : X → Fin d → ℚ) (F Q : Finset X)
    (v lam : ℚ) (q n k : ℕ) (copy spare : X → X) (H G : List X)
    (T U : List (List X)) : Result X :=
  let complete := FiniteLabelContinuation.complete loc distance F v ((1+v^2)^q) lam
  let S := CanonicalMergeRefinement.regularChain F (F.sort (·≤·)) complete Q copy spare H G
  scan F Q k (FiniteLabelContinuation.continuation loc distance F v lam (q+1) n) U H T S

end MetricKMedianRecovery.FiniteLabelCrossing

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

def accepts (distance : X → Fin d → ℚ) (F : Finset X) (H G : List X) : Plan X → Prop
  | .free i f => i∈F ∧ f∉F ∧ G=H++[f] ∧ ∀ j,distance i j=distance f j
  | .paid C T i => i∈F ∧ H=C++i::T ∧ G=C++T

instance instDecidableAccepts (distance : X → Fin d → ℚ) (F : Finset X) (H G : List X) (J : Plan X) :
    Decidable (accepts distance F H G J) := by cases J <;> dsimp only [accepts] <;> infer_instance

def view (distance : X → Fin d → ℚ) (F : Finset X) (R H G : List X) : Option (Plan X) :=
  (candidates R H G).find? (fun J=>decide (accepts distance F H G J))

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MergeResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open RationalHeight
variable {V : Type*} [DecidableEq V]

def HeightBound (h : ℕ) : Label V → Prop
  | .inl _ => True
  | .inr c => Height c.2.2 h

structure BankBound (F : Finset V) (h key size : ℕ) (B : Finset (Label V)) : Prop where
  rooted : ∀ x∈B,parent x∈F
  height : ∀ x∈B,HeightBound h x
  before : Before key B
  card : B.card ≤ size

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryTake
open WordOperations
def dropWords (x : List Bool) : List Bool := (discardPrefix x).drop (extractPrefix x).length
end MetricKMedianRecovery.BitMachine.UnaryTake

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UnaryParser
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryParser
open WordOperations UnaryTake

def step (x : List Bool) : List Bool :=
  if (data x).head?.getD false then pack true (true::counter x) (data x).tail []
  else pack false (counter x) (data x).tail []
def next := While.next step
def loop (x : List Bool) : List Bool := next^[x.length] x
noncomputable def run (x : List Bool) : List Bool :=
  let y:=loop (pack true [] x [])
  pairBits (counter y,data y)
end MetricKMedianRecovery.BitMachine.UnaryParser

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
abbrev codes (rs : List ℚ) : List Bool := WordList.encode (rs.map BinaryRational.encode)
def pack (rs acc : List ℚ) : List Bool := pairBits (raw rs,codes acc)
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def plus (x : List Bool) : List Bool := (value (extractPrefix x)+value (discardPrefix x)).bits
noncomputable def minus (x : List Bool) : List Bool := (value (discardPrefix x)-value (extractPrefix x)).bits
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

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
def near (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix x)≤BinaryRational.decode (extractPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FirstSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma geometric_menu_available (kappa D r : ℝ) (hk : 0 < kappa)
    (hr : 0 < r) (hlow : r ≤ D) (hupp : D ≤ 10*r) :
    ∃ e ≤ geometricCap kappa hk,
      r ≤ D/(1+kappa)^e ∧ D/(1+kappa)^e ≤ (1+kappa)*r := by
  have hb : 1 < 1+kappa := by linarith
  have hratio : 1 ≤ D/r := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hlow)
  obtain ⟨e, he₀, he₁⟩ := exists_nat_pow_near hratio hb
  have hpow : 0 < (1+kappa)^e := pow_pos (by linarith) _
  have heE : e ≤ geometricCap kappa hk := by
    by_contra hh
    have hegt : geometricCap kappa hk < e := lt_of_not_ge hh
    have hn := pow_lt_pow_right₀ hb hegt
    have hcap := geometricCap_spec kappa hk
    have hratio' : D/r ≤ 10 := (div_le_iff₀ hr).mpr hupp
    linarith
  refine ⟨e, heE, ?_, ?_⟩
  · apply (le_div_iff₀ hpow).mpr
    have hh := (le_div_iff₀ hr).mp he₀
    nlinarith
  · apply (div_le_iff₀ hpow).mpr
    have hh := (div_lt_iff₀ hr).mp he₁
    rw [pow_succ] at hh
    nlinarith

end MetricKMedianRecovery.RadiusMenus

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
def shape (ds : List ℕ) : List Bool := encode (ds.map (fun n=>List.replicate n true))
noncomputable def parsed : {ds : List ℕ}→{b : ℕ}→Tensor ds b→List Bool
  | [],b,s=>(Categorical.uniformBits b s).val.bits
  | _::_,_,s=>encode (List.ofFn (fun i=>parsed (s i)))
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
noncomputable def items (x : List Bool) : List Bool := repeatWords (pairBits (extractPrefix x,[]))
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
def code (kind j : ℕ) : List Bool := pairBits (kind.bits,List.replicate j true)
noncomputable def kind (x : List Bool) : ℕ := value (extractPrefix (discardPrefix x))
noncomputable def exponent (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
noncomputable def relative (x : List Bool) : Bool := decide (kind x=1)
noncomputable def first (x : List Bool) : Bool := decide (kind x=0)
def weights (M E J : ℕ) : List Bool := encode [List.replicate M true,List.replicate E true,List.replicate J true]
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
noncomputable def distance (x : List Bool) : ℚ :=
  BinaryRational.decode (Lookup.run (pairBits (extractPrefix (discardPrefix x),extractPrefix x)))+
    BinaryRational.decode (discardPrefix (discardPrefix x))
noncomputable def empty (x : List Bool) : Bool := decide (discardPrefix x=[])
end MetricKMedianRecovery.BitMachine.BinaryNearestLeaf

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def add (x : List Bool) : List Bool :=
  pairBits (extractPrefix (extractPrefix x),discardPrefix (extractPrefix x)++WordList.encode [discardPrefix x])
end MetricKMedianRecovery.BitMachine.BinarySamplingState

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
noncomputable def deleted (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinarySampler

namespace MetricKMedianRecovery.Dyadic.Canonical
open FiniteSampling
variable {A : Type*}
variable [Fintype A] [DecidableEq A]
lemma draw_average (p : A→ℝ) (hp : ∀ a,0≤p a) (ht : ∑ a,p a=1)
    (b : ℕ) (d : A) (as : List A) (ha : as.Perm (Finset.univ.toList)) (f : A→ℝ) :
    average (fun bits=>f (draw p b d as bits))=∑ a,weight p b d a*f a := by
  classical
  rw [average,Fintype.expect_eq_sum_div_card]
  have he := Fintype.sum_equiv (Categorical.uniformBits b)
    (fun bits=>f (draw p b d as bits)) (fun v=>f (select d (list p b as) v.val)) (fun _=>rfl)
  rw [he,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  rw [←Finset.sum_range (fun v=>f (select d (list p b as) v))]
  have hle : ((list p b as).map Prod.snd).sum≤2^b := by
    rw [list_sum _ _ _ ha]; exact rawCount_sum_le p hp ht b
  rw [select_sum d (list p b as) (2^b) hle f,list_sum _ _ _ ha]
  have hs : ((list p b as).map (fun aw=>(aw.2:ℝ)*f aw.1)).sum=∑ a,(rawCount p b a:ℝ)*f a := by
    simp only [list,List.map_map,Function.comp_def]
    rw [(ha.map (fun a=>(rawCount p b a:ℝ)*f a)).sum_eq]
    exact Finset.sum_map_toList _ _
  rw [hs]
  simp only [weight,count,Nat.cast_add,add_div,add_mul,Finset.sum_add_distrib]
  rw [Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    ring
  · simp only [Nat.cast_ite,Nat.cast_zero,ite_div,zero_div,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
    rw [Nat.cast_sub (rawCount_sum_le p hp ht b),Nat.cast_pow,Nat.cast_ofNat]
    ring
end MetricKMedianRecovery.Dyadic.Canonical

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

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SingleRadiusRatio
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}

lemma single_radius_ratio (C : Comparison D S O) (hD : D.Nonempty)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (w : V) (hw : w ∈ D)
    (hr : 10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w (C.assign w)) :
    dist w (C.assign w)/Population.radius D hD (comparisonCost D C.assign) C.bad.card w ≤
      (10/9 : ℝ)*C.bad.card := by
  let q := Population.radius D hD (comparisonCost D C.assign) C.bad.card w
  have hq : 0 < q := Population.radius_pos D hD _ _ w hP hm
  have hcharge : ∀ p ∈ Population.ball D w q, (9/10 : ℝ)*dist w (C.assign w) ≤ dist p (C.assign p) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hh := C.comparison_triangle w p hw hp'.1
    linarith [hp'.2]
  have hh := Population.disjoint_population_budget D ({()} : Finset Unit)
    (fun _ => Population.ball D w q) (fun _ => q) (fun _ => dist w (C.assign w))
    (fun p => dist p (C.assign p)) (comparisonCost D C.assign) C.bad.card hP hm
    (fun _ _ => dist_nonneg) rfl (fun _ _ => Finset.filter_subset _ _) (by simp)
    (fun _ _ => hq) (fun _ _ => dist_nonneg)
    (fun _ _ => Population.radius_feasible D hD _ _ w hP hm) (fun _ _ => hcharge)
  simpa only [Finset.sum_singleton] using hh

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearEligible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus

lemma correct_entry_exists (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (hk : 0 < kappa) (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (w : V) (hw : w ∈ D) :
    ∃ e : Entry (firstSize kappa) (geometricCap kappa hk) (thirdSize kappa C.bad.card),
    ∃ R : ℝ,
      menuRadius D hD (comparisonCost D C.assign) kappa C.bad.card
        (firstSize kappa) (geometricCap kappa hk) (thirdSize kappa C.bad.card) s w e = some R ∧
      0 < R ∧ dist w (C.assign w) ≤ R ∧
      R ≤ (1+kappa)*dist w (C.assign w)+
        kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w ∧
      (∀ j, e = .inr (.inr j) →
        10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w (C.assign w) ∧
        (∀ z ∈ s.leaves, 10*dist w (C.assign w) < dist w z.1+z.2) ∧
        j.val+1 = Nat.ceil (dist w (C.assign w)/
          (kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w))) := by
  let q := Population.radius D hD (comparisonCost D C.assign) C.bad.card w
  let r := dist w (C.assign w)
  have hq : 0 < q := Population.radius_pos D hD _ _ w hP hm
  by_cases hsmall : r ≤ 10*q
  · have ha := first_menu_available kappa q r hk hq dist_nonneg hsmall
    let j : Fin (firstSize kappa) := ⟨upwardIndex kappa q r-1, by omega⟩
    have hj : j.val+1 = upwardIndex kappa q r := by dsimp [j]; omega
    refine ⟨.inl j, additiveRadius kappa q (upwardIndex kappa q r), ?_,
      additiveRadius_pos kappa q _ hk hq (by omega), ha.2.2.1, ha.2.2.2, ?_⟩
    · simp only [menuRadius, additiveRadius, ← Nat.cast_add_one, hj, q]
    · intro j' he
      contradiction
  · have hr : 0 < r := lt_trans (mul_pos (by norm_num) hq) (lt_of_not_ge hsmall)
    by_cases hleaf : ∃ d, nearestLeaf s w = some d ∧ d ≤ 10*r
    · obtain ⟨d,hd,hdub⟩ := hleaf
      obtain ⟨e,he,hlo,hhi⟩ := geometric_menu_available kappa d r hk hr
        (C.correct_nearestLeaf_lower hD kappa s hs w hw d hd) hdub
      refine ⟨.inr (.inl ⟨e,by omega⟩),d/(1+kappa)^e,?_,hr.trans_le hlo,hlo,?_,?_⟩
      · simp only [menuRadius, hd, Option.map_some]
      · have h0 : 0 ≤ kappa*q := mul_nonneg hk.le hq.le
        linarith
      · intro j heq
        cases Sum.inr.inj heq
    · have hb := C.single_radius_ratio hD hP hm w hw (lt_of_not_ge hsmall)
      have ha := third_menu_available kappa q r C.bad.card hk hq hr hb
      let j : Fin (thirdSize kappa C.bad.card) := ⟨Nat.ceil (r/(kappa*q))-1,by omega⟩
      have hj : j.val+1 = Nat.ceil (r/(kappa*q)) := by dsimp [j]; omega
      refine ⟨.inr (.inr j),additiveRadius kappa q (Nat.ceil (r/(kappa*q))),?_,
        additiveRadius_pos kappa q _ hk hq (by omega),ha.2.2.1,ha.2.2.2,?_⟩
      · simp only [menuRadius, additiveRadius, ← Nat.cast_add_one, hj, q, r]
      · intro j' heq
        have he : j = j' := Sum.inr.inj (Sum.inr.inj heq)
        subst j'
        refine ⟨lt_of_not_ge hsmall,?_,hj⟩
        intro z hz
        obtain ⟨d,hd,hle⟩ := nearestLeaf_of_mem s w z hz
        have hdgt : 10*r < d := lt_of_not_ge (fun h => hleaf ⟨d,hd,h⟩)
        exact hdgt.trans_le hle

open scoped Classical

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RealizedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided.Realized
open FiniteSampling
variable {S A Ω : Type*} [Fintype A] [Fintype Ω]

noncomputable def canonical [DecidableEq A] (p : Kernel S A) (b : ℕ) (d : A)
    (as : List A) (h : as.Perm Finset.univ.toList) : Draw (Ω:=Fin b→Bool) (FixedDyadic.kernel p b d) where
  run s := Dyadic.Canonical.draw (p.weight s) b d as
  law s g := Dyadic.Canonical.draw_average (p.weight s) (p.nonneg s) (p.total s) b d as h g
end MetricKMedianRecovery.Guided.Realized

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
def entryCode (M E J : ℕ) : Entry M E J→List Bool
  | .inl i=>BinaryMenu.code 0 i.val
  | .inr (.inl i)=>BinaryMenu.code 1 i.val
  | .inr (.inr i)=>BinaryMenu.code 2 i.val
def actionCode (D : Finset (Fin n)) (M E J : ℕ) : Action D M E J→List Bool
  | .inl _=>WordList.encode [(0:ℕ).bits,[],[]]
  | .inr (.inl w)=>WordList.encode [(1:ℕ).bits,w.val.val.bits,[]]
  | .inr (.inr (w,e))=>WordList.encode [(2:ℕ).bits,w.val.val.bits,entryCode M E J e]
end MetricKMedianRecovery.RationalSampling

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
noncomputable def actionField (i : ℕ) (x : List Bool) : List Bool := field i (discardPrefix x)
noncomputable def kind (k : ℕ) (x : List Bool) : Bool := decide (value (actionField 0 x)=k)
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalBest
open WordOperations WordList BinaryArithmetic
def pack (ctx seed : List Bool) (ws : List (List Bool)) : List Bool := pairBits (ctx,pairBits (seed,encode ws))
end MetricKMedianRecovery.BitMachine.BinaryRationalBest

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
open BinaryOpeningPayment (field )
noncomputable def metricContext (x : List Bool) : List Bool := encode [field 0 x,field 1 x]
noncomputable def sanitizeContext (x : List Bool) : List Bool := encode [field 2 x,field 3 x,field 4 x]
noncomputable def atRawInput (x : List Bool) : List Bool := encode [field 0 (extractPrefix x),field 1 (extractPrefix x),
  field 2 (extractPrefix x),discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L A : Type*} [LinearOrder L]
def nextTable (C : Finset L→Candidate (List A)) (U : Finset L) (T : Table L A) : Table L A :=
  (states U).map (fun W=>(W,select ((enumBlocks W).map (fun V=>merge (C V) (lookup (W\V) T)))))
def tables (C : Finset L→Candidate (List A)) (U : Finset L) : ℕ→Table L A
  | 0=>initialTable U
  | t+1=>nextTable C U (tables C U t)
def tableStep (C : Finset L→Candidate (List A)) (U : Finset L) (s : Table L A×Candidate (List A)) :
    Table L A×Candidate (List A) :=
  let T:=nextTable C U s.1
  (T,choose s.2 (lookup U T))
def tableRun (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) : Table L A×Candidate (List A) :=
  (tableStep C U)^[c] (initialTable U,none)
def tableBest (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) : Candidate (List A) :=
  if U=∅ then some (0,[]) else (tableRun C U c).2
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_GridMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGrid
open WordOperations WordList BinaryArithmetic DyadicGrid
open BinaryOpeningPayment (field )
def count (query : List Bool→List Bool) (ctx : List Bool) (s : ℚ) : ℕ :=
  value (query (pairBits (field 0 ctx,BinaryRational.encode s)))
def boundK (ctx : List Bool) : ℕ := value (field 1 ctx)
def lower (ctx : List Bool) : ℚ := BinaryRational.decode (field 2 ctx)
def upper (ctx : List Bool) : ℚ := BinaryRational.decode (field 3 ctx)
end MetricKMedianRecovery.BitMachine.BinaryGrid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
def choiceBits (q c b : ℕ) : List Bool := pairBits (q.bits,pairBits (c.bits,b.bits))
attribute [local irreducible] BinaryEllipsoidInitial.indices
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOutcome
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseFreshAllocation
open PhaseSequence PhaseMergePath PhaseMergeCompletion PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

@[instance_reducible]
noncomputable def enlargedMetric : PseudoMetricSpace (X ⊕ (X × Bool)) :=
  LeafMetric.attachedMetric Prod.fst (fun _ => 0) (fun _ => le_rfl)

end MetricKMedianRecovery.PhaseFreshAllocation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling FiniteSampling IntegralCandidates

noncomputable def countBound (L : ℕ) : ℕ :=
  max (2*L) ⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊

end MetricKMedianRecovery.IntegralAssembly

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
open BinaryOpeningPayment (field )
variable {n : ℕ}

def context (cfg : List Bool) (b : ℕ) : List Bool := pairBits (cfg,List.replicate b true)
noncomputable def input (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),discardPrefix (discardPrefix x))
noncomputable def drawInput (x : List Bool) : List Bool := encode [extractPrefix (extractPrefix x),discardPrefix (discardPrefix x),
  discardPrefix (extractPrefix x),extractPrefix (discardPrefix x)]
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
open WordOperations WordList BinaryArithmetic RationalHeight
open BinaryOpeningPayment (field )
variable {n : ℕ}
def runPack (cfg : List Bool) (m b : ℕ) (seeds : List (Fin b→Bool)) : List Bool :=
  encode [cfg,List.replicate m true,List.replicate b true,encode (seeds.map List.ofFn)]
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

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
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryEllipsoidInitial.indices WordList.mapWith
def pack {t b : ℕ} (cfg : List Bool) (m : ℕ) (seed : Fin t→Fin b→Bool) : List Bool :=
  encode [cfg,List.replicate m true,List.replicate t true,List.replicate b true,BinarySeed.raw (ds:=[t]) seed]
end MetricKMedianRecovery.BitMachine.BinarySampler.Trace

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
attribute [local irreducible] RawUnary.run BinaryMetricBest.best List.ofFn BinarySeed.raw
noncomputable def atSeedInput (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),
  pairBits (discardPrefix (extractPrefix x),discardPrefix x))
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

def itemsBits {X : Type*} (enc : X → List Bool) (xs : List X) : List Bool := encode (xs.map enc)
def cutBits {X : Type*} (enc : X → List Bool) (p : List X × X × List X) : List Bool :=
  encode [itemsBits enc p.1,enc p.2.1,itemsBits enc p.2.2]
def outBits {X : Type*} (enc : X → List Bool) (ps : List (List X × X × List X)) : List Bool := encode (ps.map (cutBits enc))
def accBits {X : Type*} (enc : X → List Bool) (s : Acc X) : List Bool :=
  encode [itemsBits enc s.front,itemsBits enc s.rest,outBits enc s.out]

structure Bounds {X : Type*} (enc : X → List Bool) (N n : ℕ) (s : Acc X) : Prop where
  front : (itemsBits enc s.front).length≤n*(2*N+2)
  rest : (itemsBits enc s.rest).length≤N
  count : s.out.length≤n
  each : ∀ p∈s.out,(cutBits enc p).length≤2*(n*(2*N+2)+N+N)+6
end MetricKMedianRecovery.BitMachine.WordList.Slices

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
def pack (ctx seed : List Bool) (ws : List (List Bool)) : List Bool := pairBits (ctx,pairBits (seed,encode ws))
end MetricKMedianRecovery.BitMachine.BinaryLocalBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CanonicalParents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}
def Rooted (F : Finset V) (B : Finset (Label V)) : Prop := ∀ x∈B,parent x∈F
end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.RationalLeaves
open PhaseSequence
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]
attribute [local instance] RationalLeaves.metric

def project (Q : Finset (Label V)) : Finset V := Q.image parent
end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRound
open WordList BinaryOpeningPayment

def pack (q u : ℚ) (cap : ℕ) : List Bool := encode [BinaryRational.encode q,BinaryRational.encode u,cap.bits]
noncomputable def ceil (x : List Bool) : List Bool :=
  (⌈BinaryRational.decode (field 0 x)/BinaryRational.decode (field 1 x)⌉₊).bits
noncomputable def positive (x : List Bool) : List Bool := (min (value (field 2 x)) (max 1 (value (ceil x)))).bits
noncomputable def rational (x : List Bool) : List Bool := BinaryRational.encode (value (positive x):ℚ)
end BinaryRound
end MetricKMedianRecovery.BitMachine

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
open BinaryOpeningPayment (field )
def contCtx (base : List Bool) (n q : ℕ) : List Bool := encode [base,List.replicate n true,List.replicate q true]
end MetricKMedianRecovery.BitMachine.BinaryScan

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StartResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialQuery
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )

def ctx (base : List Bool) (total : ℕ) : List Bool := pairBits (List.replicate total true,base)
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

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
noncomputable def anchorInput (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x,field 3 x,field 5 x]
noncomputable def total (x : List Bool) : List Bool := (BinaryArithmetic.value (field 5 x)+BinaryArithmetic.value (field 6 x)).bits
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
variable {n : ℕ}
noncomputable def src (j : ℕ) : List Bool→ List Bool := field j ∘ extractPrefix
noncomputable def less (x : List Bool) : List Bool := (BinaryArithmetic.value (src 5 x)-BinaryArithmetic.value (discardPrefix x)).bits
noncomputable def surplusInput (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,less x,discardPrefix x]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

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
def ctx : List Bool→List Bool := extractPrefix ∘ extractPrefix
def rowIndex : List Bool→List Bool := discardPrefix ∘ extractPrefix
def colIndex : List Bool→List Bool := discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

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
noncomputable def raw (x : List Bool) : List Bool := extractPrefix x
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
noncomputable def normInput (x : List Bool) : List Bool := pairBits (field 0 x,field 1 x)
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
open BinaryOpeningPayment (field )
noncomputable def callInput (x : List Bool) : List Bool :=
  encode [extractPrefix (extractPrefix x),discardPrefix x,discardPrefix (extractPrefix x)]
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


