-- Prove2me | Definitions.Def_Q238K014
-- name    : Q238K014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:07.095534+00:00
-- url     : https://prove2.me/theorems/9a92e2d7-6544-4fbe-bd73-16ccc21afc1f
-- title:
--   Definitions bundle Q238K014 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 140 declarations of OpenAI's Lean: 115 definitions, 9 inductive types or structures, 4 instances and 12 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalBest.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.code`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.weights`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.variableWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.kindWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sourceSummand`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalBest.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.bottomIndices`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.choiceBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRound.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.context`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.runPack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.contCtx`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.parsed`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.shape`, `OAI.MetricKMedianRecovery.BitMachine.IntegerArray.encode`, `OAI.MetricKMedianRecovery.BitMachine.RationalArray.encodePairs`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Fold.operation`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.Bounds`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.accBits`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.cutBits`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.itemsBits`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.outBits`, `OAI.MetricKMedianRecovery.BlueDP.atoms`, `OAI.MetricKMedianRecovery.BlueDP.initialTable`, `OAI.MetricKMedianRecovery.BlueDP.lookup`, `OAI.MetricKMedianRecovery.BlueDP.score0`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Correction.Bounded`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Correction.Keys`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.LowCertificate`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.NormalCertificate`, `OAI.MetricKMedianRecovery.CanonicalDelete.Bounds`, `OAI.MetricKMedianRecovery.CanonicalDelete.step`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.Result.Bounded`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.Result.Spec`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.run`, `OAI.MetricKMedianRecovery.CanonicalLengthView.candidates`, `OAI.MetricKMedianRecovery.CanonicalMatch.step`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Result.Correct` and 84 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_CategoricalRule`, `KMedianRecovery_Encoding_Encode`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_LabelRange`, `KMedianRecovery_Encoding_Matrix`, `KMedianRecovery_Encoding_RationalBest`, `KMedianRecovery_Encoding_RationalBottomIndices`, `KMedianRecovery_Encoding_RationalInflatedShape`, `KMedianRecovery_Encoding_UniformBits`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_RoundingArithmetic`, `KMedianRecovery_Machines_CorrectionSize`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_MergeResources`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_BoundRow`, `KMedianRecovery_Recovery_CoordinateRow`, `KMedianRecovery_Recovery_Coupled`, `KMedianRecovery_Recovery_DataHeight`, `KMedianRecovery_Recovery_Entry`, `KMedianRecovery_Recovery_EnumeratedRow`, `KMedianRecovery_Recovery_FiniteCross`, `KMedianRecovery_Recovery_IfNat`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_InitialState`, `KMedianRecovery_Recovery_KindRows`, `KMedianRecovery_Recovery_LengthHeight`, `KMedianRecovery_Recovery_LengthSearch`, `KMedianRecovery_Recovery_MergeCross`, `KMedianRecovery_Recovery_MergePath`, `KMedianRecovery_Recovery_MergeRefine`, `KMedianRecovery_Recovery_Pool`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Recovery_ReverseRow`, `KMedianRecovery_Recovery_Row`, `KMedianRecovery_Recovery_SetFunction`, `KMedianRecovery_Recovery_State`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_StoredForms`, `KMedianRecovery_Recovery_Table`, `KMedianRecovery_Recovery_TableValue`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Sampling_PrefixData`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerTraceMachine`, `KMedianRecovery_Sampling_SamplingPotential`, `KMedianRecovery_Sampling_SeedTensor`, `KMedianRecovery_Strictness_Clipped`, `KMedianRecovery_Strictness_ClippedBid`, `KMedianRecovery_Strictness_Dual`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K001`, `Q238K002`, `Q238K003` and `Q238K004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K021` and `Q238K022`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238`, `OAI_MetricKMedianRecovery_BitMachine_WordList_Set_run_encode_s238`, `OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec_s238`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinePath_spec_s238`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238`, `OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238`, `OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.advance_pos_lower_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238`, `OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238`, `OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238`, `OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238` and `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238`, `OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238`, `OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.advance_pos_lower_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238`, `OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238`, `OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238`, `OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238` and `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K001
import Definitions.Def_Q238K002
import Definitions.Def_Q238K003
import Definitions.Def_Q238K004

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

def Row.value {n : ℕ} (r : Row n) (x : Fin n → ℚ) : ℚ := ∑ i, r.coeff i * x i

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open BinaryArithmetic
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
open BinaryArithmetic
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
open BinaryArithmetic
namespace RationalArray
open RationalHeight
def encodePairs (xs : List (ℚ×ℚ)) : List Bool :=
  WordList.encode (xs.map (fun p=>pairBits (BinaryRational.encode p.1,BinaryRational.encode p.2)))
end RationalArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EnumeratedRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
variable {V R : Type*} [Fintype V] {n : ℕ}

def Form.enumeratedRow (e : Fin n ≃ V) (f : Form V) : Row n :=
  ⟨fun i => f.coeff (e i),-f.constant⟩

end MetricKMedianRecovery.RationalLinearFeasibility

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability
variable {D X : Type*} [Fintype D] [DecidableEq D] [DecidableEq X]

def slack (F : Type*) [DecidableEq F] (f : F) (a j : D) : Form (Variables D F) := Form.coord (.inr (f,a,j))

def forms (d : X → D → ℚ) (F W : Finset X) (v z lam eta : ℚ) (i : X) :
    Kind D W F → Form (Variables D F)
  | .lower j => if active d v z W j then (Form.const z).sub (bid F j) else Form.const 0
  | .upper j => if active d v z W j then (bid F j).sub (Form.const ((1+v^2)*z)) else Form.const 0
  | .cap j f => if active d v z W j then (bid F j).sub (Form.const ((1-3*v)*d f j)) else Form.const 0
  | .far j => if active d v z W j ∧ v*z<d i j then (bid F j).sub (Form.const z) else Form.const 0
  | .payment => (Form.const (lam-(Fintype.card D:ℚ)*eta)).sub (payment d F W v z i)
  | .slackZero f a j => if active d v z W a then (Form.const 0).sub (slack F f a j) else Form.const 0
  | .slackTerm f a j => if active d v z W a then (dual d F W v z f a j).sub (slack F f a j) else Form.const 0
  | .dual f a => if active d v z W a then (Form.sum (fun j => slack F f a j)).sub (Form.const lam) else Form.const 0

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_KindRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability

section
open RationalOpenability
variable {D W F : Type*}

def kindRows (ds : List D) (ws : List W) (fs : List F) : List (Kind D W F) :=
  ds.map .lower ++ ds.map .upper ++
    ds.flatMap (fun j => ws.map (Kind.cap j)) ++ ds.map .far ++ [.payment] ++
    fs.flatMap (fun f => ds.flatMap (fun a => ds.map (Kind.slackZero f a))) ++
    fs.flatMap (fun f => ds.flatMap (fun a => ds.map (Kind.slackTerm f a))) ++
    fs.flatMap (fun f => ds.map (Kind.dual f))

def variableEnum (d : ℕ) {m : ℕ} (F : Finset (Fin m)) :
    Fin (d+F.card*(d*d)) ≃ Variables (Fin d) F :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _)
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (F.orderIsoOfFin rfl).toEquiv
      finProdFinEquiv.symm)))

end

open RationalOpenability

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalInflatedShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def rationalStepCenter (H : Matrix V V ℚ) (a c : V → ℚ) : V → ℚ :=
  c-(1/(((Fintype.card V:ℚ)+1)*rationalRootUpper (32*Fintype.card V) (rationalQuad H a))) • (H *ᵥ a)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

def badRow {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) : Option (Row n) :=
  rows.find? (fun r => decide (r.bound < r.value c))

def advance {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) : State n :=
  match badRow rows S.center with
  | none => S
  | some r => if r.coeff=0 then S else
      ⟨rationalStepShape D S.shape r.coeff,rationalStepCenter S.shape r.coeff S.center⟩

def iterate {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) : ℕ → State n
  | 0 => S
  | t+1 => advance D rows (iterate D rows S t)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

def weakSolve {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) : Option (Fin n → ℚ) :=
  let T := iterationBudget n p s
  let c := (iterate (gridDenominator n T) rows (initialState n R) T).center
  if badRow rows c=none then some c else none

def relaxedRow {n : ℕ} (eps : ℚ) (r : Row n) : Row n := ⟨r.coeff,r.bound+eps⟩

def relaxedRows {n : ℕ} (eps : ℚ) (rows : List (Row n)) : List (Row n) := rows.map (relaxedRow eps)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def boundedRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : List (Row n) :=
  List.ofFn (fun r => integerRow (A r) (b r)) ++
  List.ofFn (fun i => integerRow (boundedMatrix A (.inr (true,i))) B) ++
  List.ofFn (fun i => integerRow (boundedMatrix A (.inr (false,i))) B)

def integerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : Bool :=
  (weakSolve (relaxedRows (gapEpsilon m n H) (boundedRows A b B))
    ((n:ℚ)*(B+1)) (precisionLog m n H) (radiusLog n B)).isSome

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DataHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate RationalLinearFeasibility
open scoped BigOperators

def boundedIntegerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : Bool :=
  integerDecide (padMatrix A) b B (dataHeight (padMatrix A) b B)

end MetricKMedianRecovery.Ellipsoid

namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate RationalLinearFeasibility
open scoped BigOperators

def rowEntries {n : ℕ} (q : Row n) : Option (Fin n) → ℚ := Option.elim' q.bound q.coeff

def clearedMatrix {n : ℕ} (rows : List (Row n)) : Matrix (Fin rows.length) (Fin n) ℤ :=
  fun r j => rowNumerator (rowEntries rows[r]) (some j)

def clearedBounds {n : ℕ} (rows : List (Row n)) : Fin rows.length → ℤ :=
  fun r => rowNumerator (rowEntries rows[r]) none

def boundedRationalDecide {n : ℕ} (rows : List (Row n)) (B : ℕ) : Bool :=
  boundedIntegerDecide (clearedMatrix rows) (clearedBounds rows) B

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ReverseRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def reverseRow {n : ℕ} (q : Row n) : Row n := ⟨fun j => -q.coeff j,-q.bound⟩

def faceRows {n : ℕ} (rows picked : List (Row n)) : List (Row n) :=
  rows ++ picked ++ picked.map reverseRow

def selectFace {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    List (Row n) → List (Row n) → List (Row n)
  | [], picked => picked
  | q::todo, picked =>
    if boundedRationalDecide (faceRows rows (q::picked)) B then
      selectFace rows B todo (q::picked)
    else selectFace rows B todo picked

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoordinateRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def coordinateRow {n : ℕ} (i : Fin n) (c b : ℚ) : Row n :=
  ⟨fun j => if j=i then c else 0,b⟩

def boxRows (n B : ℕ) : List (Row n) :=
  List.ofFn (fun i => coordinateRow i 1 B) ++ List.ofFn (fun i => coordinateRow i (-1) B)

def withBox {n : ℕ} (rows : List (Row n)) (B : ℕ) := rows++boxRows n B

def finalFace {n : ℕ} (rows : List (Row n)) (B : ℕ) : List (Row n) :=
  selectFace (withBox rows B) B (withBox rows B) []

def rowMatrix {n : ℕ} (rows : List (Row n)) : Matrix (Fin rows.length) (Fin n) ℚ :=
  fun i j => rows[i].coeff j

def rowBounds {n : ℕ} (rows : List (Row n)) : Fin rows.length → ℚ :=
  fun i => rows[i].bound

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

def sourceSummand {m d : ℕ} (distance : Fin m → Fin d → ℚ) (W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (j : Fin d) : ℚ :=
  if EffectiveOpenability.active distance v z W j then
    if distance i j≤v*z then -((1-3*v)*distance i j)
    else max (z-(1-3*v)*distance i j) 0
  else max ((1-3*v)*RationalOpenability.nearest distance W j-(1-3*v)*distance i j) 0
end BinaryOpeningPayment
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
open BinaryArithmetic
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
open BinaryArithmetic
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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A : Type*}
def score0 : Candidate (List A)→ℚ := fun x=>x.map Prod.fst |>.getD 0
def atoms : Candidate (List A)→List A := fun x=>x.map Prod.snd |>.getD []
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid.Stored
open Matrix RationalLinearFeasibility
open scoped BigOperators

def state {n : ℕ} (S : State n) : State n := ⟨matrix S.shape,vector S.center⟩
@[simp] lemma state_eq {n : ℕ} (S : State n) : state S=S := by
  cases S
  simp only [state,matrix_eq,vector_eq]

def iterate {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) : ℕ → State n
  | 0 => state S
  | t+1 => state (advance D rows (iterate D rows S t))

@[simp] lemma iterate_eq {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) (t : ℕ) :
    iterate D rows S t=Ellipsoid.iterate D rows S t := by
  induction t with
  | zero => simp only [iterate,Ellipsoid.iterate,state_eq]
  | succ t ih => simp only [iterate,Ellipsoid.iterate,state_eq,ih]

def weakSolve {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) : Option (Fin n → ℚ) :=
  let T := iterationBudget n p s
  let c := (iterate (gridDenominator n T) rows (initialState n R) T).center
  if badRow rows c=none then some c else none
@[simp] lemma weakSolve_eq {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) :
    weakSolve rows R p s=Ellipsoid.weakSolve rows R p s := by
  simp only [weakSolve,Ellipsoid.weakSolve,iterate_eq]

def integerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : Bool :=
  (weakSolve (relaxedRows (gapEpsilon m n H) (boundedRows A b B))
    ((n:ℚ)*(B+1)) (precisionLog m n H) (radiusLog n B)).isSome
@[simp] lemma integerDecide_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    integerDecide A b B H=Ellipsoid.integerDecide A b B H := by
  simp only [integerDecide,Ellipsoid.integerDecide,weakSolve_eq]

def boundedIntegerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : Bool :=
  integerDecide (padMatrix A) b B (dataHeight (padMatrix A) b B)
@[simp] lemma boundedIntegerDecide_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    boundedIntegerDecide A b B=Ellipsoid.boundedIntegerDecide A b B := by
  simp only [boundedIntegerDecide,Ellipsoid.boundedIntegerDecide,integerDecide_eq]

def boundedRationalDecide {n : ℕ} (rows : List (Row n)) (B : ℕ) : Bool :=
  boundedIntegerDecide (clearedMatrix rows) (clearedBounds rows) B
@[simp] lemma boundedRationalDecide_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    boundedRationalDecide rows B=Ellipsoid.boundedRationalDecide rows B := by
  simp only [boundedRationalDecide,Ellipsoid.boundedRationalDecide,boundedIntegerDecide_eq]

def selectFace {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    List (Row n) → List (Row n) → List (Row n)
  | [],picked => picked
  | q::todo,picked =>
    if boundedRationalDecide (faceRows rows (q::picked)) B then
      selectFace rows B todo (q::picked)
    else selectFace rows B todo picked
@[simp] lemma selectFace_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) (todo picked : List (Row n)) :
    selectFace rows B todo picked=Ellipsoid.selectFace rows B todo picked := by
  induction todo generalizing picked with
  | nil => rfl
  | cons q todo ih => simp only [selectFace,Ellipsoid.selectFace,boundedRationalDecide_eq,ih]

def finalFace {n : ℕ} (rows : List (Row n)) (B : ℕ) : List (Row n) :=
  selectFace (withBox rows B) B (withBox rows B) []
@[simp] lemma finalFace_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    finalFace rows B=Ellipsoid.finalFace rows B := selectFace_eq _ _ _ _

end MetricKMedianRecovery.Ellipsoid.Stored

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability

def update {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) (e : Event m d) : State m d :=
  ⟨insert e.facility s.opened,s.phase,
    Vector.ofFn (fun j => if active distance v s.phase s.opened j then e.bid[j] else s.budget[j])⟩

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
open EffectiveOpenability

def clipped {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (W : Finset (Fin m)) (j : Fin d) : ℚ :=
  if W.Nonempty then min z ((1-3*v)*RationalOpenability.nearest distance W j) else z

def advance {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) : State m d :=
  ⟨s.opened,(1+v^2)*s.phase,Vector.ofFn (fun j =>
    if active distance v s.phase s.opened j then
      clipped distance v ((1+v^2)*s.phase) s.opened j else s.budget[j])⟩

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

def Entry (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (i : X) : Prop :=
  i ∉ Q ∧ (i ∈ B ∨ (i ∈ F ∧ ∃ W : Finset X, Q ⊆ W ∧ W ⊆ F ∪ B ∧
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i))

inductive Prefix (loc : D → X) (F B : Finset X) (v z lam eta : ℝ) :
    Finset X → List X → Prop
  | nil (Q) : Prefix loc F B v z lam eta Q []
  | cons {Q : Finset X} {i : X} {H : List X}
      (hi : Entry loc F B Q v z lam eta i)
      (htail : Prefix loc F B v z lam eta (insert i Q) H) :
      Prefix loc F B v z lam eta Q (i::H)

def Maximal (loc : D → X) (F Q : Finset X) (v z lam : ℝ) : Prop :=
  ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i

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

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ClippedBid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace ClippingTransfer
variable {D X : Type*} [PseudoMetricSpace X]

noncomputable def clippedBid (loc : D → X) (t : ℝ) (W : Finset X)
    (tau : D → ℝ) (j : D) : ℝ := min (tau j) (t*nearestDistance (loc j) W)

end ClippingTransfer
end MetricKMedianRecovery

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

inductive Step (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam : ℝ) :
    List X → List X → Prop
  | add (H : List X) (i : X) (hi : i ∈ F) : Step loc F B Q copy v z lam H (H++[copy i])
  | remove (C T A : List X) (i : X) (hi : i ∈ F)
      (hA : Prefix loc F (pool F B copy) v z lam 0 (Q ∪ (C++T).toFinset) A)
      (hreg : ∀ x ∈ A, x ∈ F) :
      Step loc F B Q copy v z lam (C++i::T) ((C++T)++A)
  | replace (C T : List X) (i : X) (hi : i ∈ F)
      (hnot : i ∉ Q ∪ (C++T).toFinset) :
      Step loc F B Q copy v z lam (C++copy i::T) (C++i::T)

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

end

open PhaseSequence PhaseMergePath

end MetricKMedianRecovery.PhaseMergeRefinement

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseSequence PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Jump.source (copy : X → X) (H : List X) : Jump X → List X
  | .add _ => H
  | .remove C T _ i => C++i::T
  | .replace C T i => C++copy i::T

def Jump.target (copy : X → X) (H : List X) : Jump X → List X
  | .add i => H++[copy i]
  | .remove C T A _ => (C++T)++A
  | .replace C T i => C++i::T

def Jump.labels (F : Finset X) : Jump X → Prop
  | .add i => i∈F
  | .remove _ _ A i => i∈F ∧ ∀ a∈A,a∈F
  | .replace _ _ i => i∈F

instance instDecidableLabels (F : Finset X) (J : Jump X) : Decidable (J.labels F) := by
  cases J <;> dsimp only [Jump.labels] <;> infer_instance

def candidates (R : List X) (H G : List X) : List (Jump X) :=
  (R.map Jump.add) ++
  ((cuts H).map (fun p => Jump.remove p.1 p.2.2 (G.drop (H.length-1)) p.2.1)) ++
  ((cuts G).map (fun p => Jump.replace p.1 p.2.2 p.2.1))

def accepts (F : Finset X) (copy : X → X) (H G : List X) (J : Jump X) : Prop :=
  J.source copy H=H ∧ J.target copy H=G ∧ J.labels F

instance instDecidableAccepts (F : Finset X) (copy : X → X) (H G : List X) (J : Jump X) :
    Decidable (accepts F copy H G J) := by unfold accepts; infer_instance

def view (F : Finset X) (R : List X) (copy : X → X) (H G : List X) : Option (Jump X) :=
  (candidates R H G).find? (fun J => decide (accepts F copy H G J))

inductive EPath (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) :
    List X → List (List X) → List X → Prop
  | nil {H} (h : PhaseMergeRefinement.Good loc F B Q v z lam eta H) :
      EPath loc F B Q v z lam eta H [] H
  | cons {H G T J} (h : PhaseMergeRefinement.Good loc F B Q v z lam eta H)
      (e : Adjacent loc F B Q H G) (t : EPath loc F B Q v z lam eta G T J) :
      EPath loc F B Q v z lam eta H (G::T) J

def Jump.expand (spare : X → X) (G : List X) : Jump X → List (List X)
  | .add _ => [G]
  | .remove C T A i => removeVertices C T A (spare i)
  | .replace _ _ _ => [G]

def refinePath (F : Finset X) (R : List X) (copy spare : X → X) :
    List X → List (List X) → List (List X)
  | _,[] => []
  | H,G::T =>
    match view F R copy H G with
    | none => G::refinePath F R copy spare G T
    | some J => J.expand spare G ++ refinePath F R copy spare G T

def regularChain (F : Finset X) (R : List X) (complete : Finset X → List X)
    (Q : Finset X) (copy spare : X → X) (H G : List X) : List (List X) :=
  refinePath F R copy spare H (CanonicalMergePath.regularPath complete Q copy G H)

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

def directed (F Q : Finset X) (k : ℕ) (H G : List X) (T U : List (List X)) : Result X :=
  if H.length=G.length then
    if finalCount F Q G T=k then .success G T else .common G T U
  else .sensitive H G T U

def edge (F Q : Finset X) (k : ℕ) (H G : List X) (T U : List (List X)) : Result X :=
  if forward F Q H G then directed F Q k H G T U else directed F Q k G H U T

def scan (F Q : Finset X) (k : ℕ) (complete : Finset X → List (List X))
    (U : List (List X)) : List X → List (List X) → List (List X) → Result X
  | H,T,[] => .common H T U
  | H,T,J::S =>
    let V := complete (Q ∪ J.toFinset)
    if finalCount F Q J V = k then .success J V
    else if Sandwich k (finalCount F Q H T) (finalCount F Q J V) then edge F Q k H J T V
    else scan F Q k complete U J V S

end MetricKMedianRecovery.CanonicalMergeCrossing

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

def candidates (R H G : List X) : List (Plan X) :=
  (R.flatMap (fun i=>G.map (Plan.free i))) ++ ((cuts H).map (fun p=>Plan.paid p.1 p.2.2 p.2.1))

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing CanonicalMergeCrossing
variable {X : Type*} [DecidableEq X]

def run (F Q : Finset X) (leaf : ℚ  →  X) (complete : ℚ  →  List (List X))
    (T U : List (List X)) (b : ℚ) (k N : ℕ) : Result X :=
  let f := count F Q leaf complete T U b
  let J := range f k N b
  if f J.1=k then .success J.1 (chosen complete T U b J.1)
  else if f J.2=k then .success J.2 (chosen complete T U b J.2)
  else .bracket J.1 J.2 (chosen complete T U b J.1) (chosen complete T U b J.2)

def Result.Spec (F Q : Finset X) (leaf : ℚ  →  X) (R : ℚ  →  List (List X)  →  Prop)
    (b : ℚ) (k N : ℕ) : Result X  →  Prop
  | .success s T => 0 ≤ s  ∧  s ≤ b  ∧  R s T  ∧  ((after (insert (leaf s) Q) T) ∩ F).card=k
  | .bracket l u T U => 0 ≤ l  ∧  l ≤ u  ∧  u ≤ b  ∧  u-l ≤ 1/(2:ℚ)^N  ∧  R l T  ∧  R u U  ∧
      Sandwich k ((after (insert (leaf l) Q) T) ∩ F).card ((after (insert (leaf u) Q) U) ∩ F).card

end MetricKMedianRecovery.CanonicalLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MergeResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

def Correction.Bounded (h : ℕ) : Correction V → Prop
  | .identity => True
  | .shorten _ _ l u => Height l h ∧ Height u h

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L A : Type*} [LinearOrder L]
def lookup (U : Finset L) : Table L A → Candidate (List A)
  | []=>none
  | (V,x)::xs=>if U=V then x else lookup U xs
def initialTable (U : Finset L) : Table L A := (states U).map (fun V=>(V,if V=∅ then some (0,[]) else none))
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SetFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def evaluate : Batch E → SetFunction E → SetFunction E
  | [], g => g
  | (w, _) :: tail, g => evaluate tail (operator w g)

noncomputable def direction : Batch E → SetFunction E → SetFunction E
  | [], _ => fun _ => 0
  | (w, e) :: tail, g => fun S => evaluate tail (marginal g e) S + direction tail (operator w g) S

def BoundedMarginals (g : SetFunction E) (M : ℝ) : Prop :=
  ∀ e S, 0 ≤ marginal g e S ∧ marginal g e S ≤ M

def Diminishing (g : SetFunction E) : Prop :=
  ∀ U V, U ⊆ V → ∀ e, marginal g e V ≤ marginal g e U

noncomputable def allMarginals : Batch E → SetFunction E → SetFunction E
  | [], _ => fun _ => 0
  | (_, e) :: tail, g => fun S => marginal g e S + allMarginals tail g S

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Table
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

open FiniteSampling
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [Nonempty Ω]

noncomputable def batch {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E) : Batch E :=
  List.ofFn (fun j => (tableWeights (r j), c j))

noncomputable def derivative {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) : ℝ :=
  evaluate (batch (Function.update r j (fun _ => none)) c) (marginal g e) S

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_TableValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

noncomputable def tableValue {E Ω : Type*} [DecidableEq E] [Fintype Ω]
    {a : ℕ} (g : SetFunction E) (r : Fin a → Table Ω E) : ℝ :=
  average (fun seed : Fin a → Ω => g (draw a r seed ∅))

section GreedyStep
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

def GreedyInvariant (part : E → Fin a) (s : GreedyState E a T) : Prop :=
  (∀ j ω e, s.2 j ω = some e → part e = j) ∧
    (∀ j ω, s.1 ≤ ω.val → s.2 j ω = none)

end GreedyStep
end MetricKMedianRecovery.Categorical

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section StepBound
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ} [NeZero T]

def estimationBad (part : E → Fin a) (g : SetFunction E) (M tau : ℝ)
    (s : GreedyState E a T) (seed : OracleSeed E a T L) : Prop :=
  ∃ e, tau*M/a < |scores part g s.2 seed e - average (marginalSample part g s.2 e)|

end StepBound
end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UniformBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

instance binaryOracleIndexFintype {E : Type*} [Fintype E] {a b L : ℕ} :
    Fintype (BinaryOracleIndex E a b L) :=
  inferInstanceAs (Fintype (((Fin (2^b) × E × Fin L × Fin a) ⊕ Fin a) × Fin b))

instance binaryOracleIndexDecidableEq {E : Type*} [DecidableEq E] {a b L : ℕ} :
    DecidableEq (BinaryOracleIndex E a b L) :=
  inferInstanceAs (DecidableEq (((Fin (2^b) × E × Fin L × Fin a) ⊕ Fin a) × Fin b))

end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Selected
open FiniteSampling
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

noncomputable def greedyOutput (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T)) : Finset E :=
  draw a (greedyRun part rule g seed.1).2 seed.2 ∅

noncomputable def binaryGreedyOutput {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (bits : BinaryOracleIndex E a b L → Bool) : Finset E :=
  greedyOutput part rule g (binarySeedEquiv E a b L bits)

end MetricKMedianRecovery.Categorical.Selected

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelRange
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.ColorLabel

noncomputable def colorMass (c : Fin 3) : ℝ :=
  ∑ x : Fin 4, if color x = c then (1/4 : ℝ) else 0

end MetricKMedianRecovery.ColorLabel

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
open WordList BinaryArithmetic
def pack (ctx seed : List Bool) (ws : List (List Bool)) : List Bool := pairBits (ctx,pairBits (seed,encode ws))
end MetricKMedianRecovery.BitMachine.BinaryRationalBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBottomIndices
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordList BinaryArithmetic
def bottomIndices {r : ℕ} (v : Fin r→ℚ) (k : ℕ) : List ℕ :=
  (((Finset.univ.image (ranking v)).sort (·≤·)).take k).map (fun p=>(ofLex p).2)
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

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
open CanonicalSlices
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
open WordList BinaryArithmetic
def pack (ctx seed : List Bool) (ws : List (List Bool)) : List Bool := pairBits (ctx,pairBits (seed,encode ws))
end MetricKMedianRecovery.BitMachine.BinaryLocalBest

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
open BinaryArithmetic
namespace BinaryRound
open WordList BinaryOpeningPayment

def pack (q u : ℚ) (cap : ℕ) : List Bool := encode [BinaryRational.encode q,BinaryRational.encode u,cap.bits]
end BinaryRound
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CorrectionSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}
def Correction.Keys (q : ℕ) : Correction V→Prop
  | .identity=>True
  | .shorten key _ _ _=>key<3*q
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalDelete
open PhaseSequence CanonicalMergePath
variable {X : Type*} [DecidableEq X]

def step (complete : Finset X → List X) (Q : Finset X) (C : List X) (ci : X)
    (s : Acc X) (_ : X) : Acc X :=
  let U:=s.remaining.tail
  let E:=s.extras++complete (Q∪(C++U++ci::s.extras).toFinset)
  ⟨U,E,s.vertices++[C++U++ci::E]⟩

structure Bounds (P : X → Prop) (N n : ℕ) (s : Acc X) : Prop where
  remaining : s.remaining.length≤N
  extras : s.extras.length≤N+n*N
  vertices : s.vertices.length≤N+n
  vertex : ∀ H∈s.vertices,H.length≤3*N+1+n*N
  rem_mem : ∀ x∈s.remaining,P x
  ext_mem : ∀ x∈s.extras,P x
  vert_mem : ∀ H∈s.vertices,∀ x∈H,P x

end MetricKMedianRecovery.CanonicalDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMatch
open CanonicalMergePath PhaseSequence PhaseMergePath
variable {X D : Type*} [DecidableEq X]

def step (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (s : Acc X) (i : X) : Acc X :=
  let a:=advancePrefix complete Q copy s.front s.rest i
  ⟨s.front++[i],a.1,s.vertices++a.2⟩
end MetricKMedianRecovery.CanonicalMatch

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
open WordList BinaryArithmetic
def shape (ds : List ℕ) : List Bool := encode (ds.map (fun n=>List.replicate n true))
noncomputable def parsed : {ds : List ℕ}→{b : ℕ}→Tensor ds b→List Bool
  | [],b,s=>(Categorical.uniformBits b s).val.bits
  | _::_,_,s=>encode (List.ofFn (fun i=>parsed (s i)))
end MetricKMedianRecovery.BitMachine.BinarySeed

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
def code (kind j : ℕ) : List Bool := pairBits (kind.bits,List.replicate j true)
def weights (M E J : ℕ) : List Bool := encode [List.replicate M true,List.replicate E true,List.replicate J true]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMenu

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
variable {X Y : Type*}
variable [DecidableEq X]
def refinedEdge (F : Finset X) (R : List X) (copy spare : X → X) (H G : List X) : List (List X) :=
  match view F R copy H G with
  | none=>[G]
  | some J=>J.expand spare G
end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeCrossing
variable {A B : Type*}

variable {X : Type*} [DecidableEq X]
def transition (F Q : Finset X) (k : ℕ) (P R : List X × List (List X)) : Option (Result X) :=
  if finalCount F Q R.1 R.2=k then some (.success R.1 R.2)
  else if PhaseCountCrossing.Sandwich k (finalCount F Q P.1 P.2) (finalCount F Q R.1 R.2) then
    some (edge F Q k P.1 R.1 P.2 R.2)
  else none
end MetricKMedianRecovery.CanonicalMergeCrossing

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
open WordList RationalLeaves CanonicalMergeCrossing
open BinaryOpeningPayment (field )
def contCtx (base : List Bool) (n q : ℕ) : List Bool := encode [base,List.replicate n true,List.replicate q true]
end MetricKMedianRecovery.BitMachine.BinaryScan

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_Dual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseOriginalLedger
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant
  HistoryPhaseBound
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Dual (loc : D → X) (F : Finset X) (v lam : ℝ) (alpha : D → ℝ) : Prop :=
  (∀ j, 0 < alpha j) ∧
  (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
  (∀ (C : Finset D), C.Nonempty → ∀ i ∈ F, ∀ b : ℝ, 0 < b →
    0 < (∑ j ∈ C, dist i (loc j)) → lam ≤ b*(∑ j ∈ C, dist i (loc j)) →
    v^2 ≤ strictnessGap b/(6*(b+2)) →
    (∑ j ∈ C, alpha j) ≤ lam+(2-strictnessGap b/2)*(∑ j ∈ C, dist i (loc j)))

end MetricKMedianRecovery.PhaseOriginalLedger

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open RationalHeight
variable {X : Type*} [DecidableEq X]

def Result.Bounded (h : ℕ) : Result X → Prop
  | .success s _ => Height s h
  | .bracket l u _ _ => Height l h ∧ Height u h

end MetricKMedianRecovery.CanonicalLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialProject
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseOriginalLedger HistoryPhaseBound
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {d : ℕ}
def LowCertificate (loc : Fin d→V) (F S : Finset V) (v lo : ℝ) (k : ℕ) : Prop :=
  S⊆F ∧ S.Nonempty ∧ S.card≤k ∧ ∃ (Q : ℝ) (alpha : Fin d→ℝ),
    0≤Q ∧ (∑ j,nearestDistance (loc j) S)≤Q ∧ Dual loc F v lo alpha ∧
      (1-3*v)*Q≤∑ j,alpha j
def NormalCertificate (loc : Fin d→V) (F S : Finset V) (v lo hi eta : ℝ) (total k : ℕ) : Prop :=
  S⊆F ∧ S.Nonempty ∧ S.card≤k+3*total ∧ ∃ (lam Q : ℝ) (alpha : Fin d→ℝ),
    lo≤lam ∧ lam≤hi ∧ 0≤Q ∧ (∑ j,nearestDistance (loc j) S)≤Q ∧ Dual loc F v lam alpha ∧
      (1-3*v)*Q+(k:ℝ)*(lam-(d:ℝ)*eta)≤∑ j,alpha j
end MetricKMedianRecovery.CanonicalCoupledMerge

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
def choiceBits (q c b : ℕ) : List Bool := pairBits (q.bits,pairBits (c.bits,b.bits))
attribute [local irreducible] BinaryEllipsoidInitial.indices
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryRecovery

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}

def context (cfg : List Bool) (b : ℕ) : List Bool := pairBits (cfg,List.replicate b true)
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
open WordList BinaryArithmetic RationalHeight
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
open WordList
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryEllipsoidInitial.indices WordList.mapWith
def pack {t b : ℕ} (cfg : List Bool) (m : ℕ) (seed : Fin t→Fin b→Bool) : List Bool :=
  encode [cfg,List.replicate m true,List.replicate t true,List.replicate b true,BinarySeed.raw (ds:=[t]) seed]
end MetricKMedianRecovery.BitMachine.BinarySampler.Trace

end OAI
end


