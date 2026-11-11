-- Prove2me | Definitions.Def_Q238K010
-- name    : Q238K010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:13:39.870208+00:00
-- url     : https://prove2.me/theorems/2005c7eb-e526-4181-a0e0-266bf32de25c
-- title:
--   Definitions bundle Q238K010 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 159 declarations of OpenAI's Lean: 152 definitions and 7 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryAdvance.deletionInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAdvance.firstVertex`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAdvance.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.fuel`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.input`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.logWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.predWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.width`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.widthCeil`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.itemCall`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.labelsEnc`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.atomEnc`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.ctx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.ctxPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.whole`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.encode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.score`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.select`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.invalid`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.payloadOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.scoreOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.scores`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.atomEnc`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.op`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.price`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.record`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.records`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.response`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.sourceL`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.sourceR`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.sourceRow`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.targetL`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.targetY`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLookup.encode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLookup.matchKey` and 112 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueBlocksMachine`, `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_BlueItem`, `KMedianRecovery_Branching_BlueLookup`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BlueNextTable`, `KMedianRecovery_Branching_BlueProgram`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_BlueTableSize`, `KMedianRecovery_Branching_BranchBalls`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchPhysical`, `KMedianRecovery_Branching_CopyAge`, `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_LabelLookup`, `KMedianRecovery_Encoding_LabelMember`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_RationalLeaves`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Encoding_WordSubsets`, `KMedianRecovery_Geometry_NearestLeafMachine`, `KMedianRecovery_Machines_BisectionMachine`, `KMedianRecovery_Machines_CappedFold`, `KMedianRecovery_Machines_DeleteSize`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_ClassFilter`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_PhasesBounded`, `KMedianRecovery_Recovery_SortMath`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SamplingReference`, `KMedianRecovery_Sampling_SamplingStateMachine`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K001` and `Q238K002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K017`, `Q238K018`, `Q238K019`, `Q238K020`, `Q238K021` and `Q238K022`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K001
import Definitions.Def_Q238K002

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace UnaryResources
lemma inc_iter (j : ℕ) : inc^[j] (0:ℕ).bits=j.bits := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih]; simp only [inc,value_bits]
end UnaryResources
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
def encode (xs : List ℚ) : List Bool := WordList.encode (xs.map BinaryRational.encode)
end RationalArray
namespace RationalMatrix
open WordList

def rowEncode {n : ℕ} (v : Fin n → ℚ) : List Bool := RationalArray.encode (List.ofFn v)
def encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : List Bool :=
  WordList.encode (List.ofFn (fun i=>rowEncode (A i)))
end RationalMatrix
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

open BinaryArithmetic RationalLinearFeasibility
namespace BinaryRow
open RationalMatrix

def encode {n : ℕ} (r : Row n) : List Bool := pairBits (rowEncode r.coeff,BinaryRational.encode r.bound)
def rowsEncode {n : ℕ} (rows : List (Row n)) : List Bool := WordList.encode (rows.map encode)
end BinaryRow
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

namespace BinaryBoundedDecision
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

def pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate m true,
    pairBits (B.bits,BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (A r) (b r))))))
end BinaryBoundedDecision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CappedFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.CappedFold
noncomputable def run (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  Fold.accum (BoundedIteration.run (Fold.step f)
    (pairBits (Count.run (Fold.items (discardPrefix x)),
      pairBits (RepeatedAppend.copies 4 x,discardPrefix x))))
end MetricKMedianRecovery.BitMachine.WordList.CappedFold

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueChoice
open WordList BinaryArithmetic
variable {A : Type*}
def encode (enc : A→List Bool) : BlueDP.Candidate A→List Bool
  | none=>[]
  | some (q,a)=>WordList.encode [pairBits (BinaryRational.encode q,enc a)]
noncomputable def score (x : List Bool) : List Bool := extractPrefix (head x)
noncomputable def run (x : List Bool) : List Bool :=
  if extractPrefix x=[] then discardPrefix x else
  if discardPrefix x=[] then extractPrefix x else
  if BinaryRational.decode (score (extractPrefix x))≤BinaryRational.decode (score (discardPrefix x))
    then extractPrefix x else discardPrefix x

noncomputable def step (x : List Bool) : List Bool := run (pairBits (Fold.accum x,Find.item x))
noncomputable def select (x : List Bool) : List Bool := CappedFold.run step (pairBits (x,Fold.pack x [] []))

end MetricKMedianRecovery.BitMachine.BinaryBlueChoice

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueMerge
open WordList
variable {A : Type*}
def listEnc (enc : A→List Bool) (xs : List A) : List Bool := WordList.encode (xs.map enc)
noncomputable def payload (x : List Bool) : List Bool := discardPrefix (head x)
noncomputable def sum (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (BinaryBlueChoice.score (extractPrefix x))+
    BinaryRational.decode (BinaryBlueChoice.score (discardPrefix x)))
noncomputable def output (x : List Bool) : List Bool := WordList.encode
  [pairBits (sum x,payload (extractPrefix x)++payload (discardPrefix x))]
noncomputable def run (x : List Bool) : List Bool :=
  if extractPrefix x=[] then [] else if discardPrefix x=[] then [] else output x
end MetricKMedianRecovery.BitMachine.BinaryBlueMerge

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCollect
open WordList
variable {A : Type*}
noncomputable def invalid (x : List Bool) : Bool := decide (discardPrefix x=[])
noncomputable def scoreOp (x : List Bool) : List Bool := BinaryBlueChoice.score (discardPrefix x)
noncomputable def scores (x : List Bool) : List Bool := mapWith scoreOp (pairBits ([],x))
attribute [local irreducible] mapWith
noncomputable def payloadOp (x : List Bool) : List Bool := BinaryBlueMerge.payload (discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PhasesBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LeafMetric
variable {V C : Type*} [PseudoMetricSpace V]

lemma leafDist_comm (root : C → V) (u : C → ℝ) (x y : V ⊕ C) :
    leafDist root u x y = leafDist root u y x := by
  by_cases h : x = y
  · subst y; rfl
  · simp only [leafDist,ite_eq_right h,ite_eq_right (Ne.symm h)]
    rw [dist_comm]
    ring
lemma leafDist_triangle (root : C → V) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (x y z : V ⊕ C) :
    leafDist root u x z ≤ leafDist root u x y + leafDist root u y z := by
  by_cases hxz : x = z
  · subst z
    rw [leafDist_self]
    exact add_nonneg (leafDist_nonneg root u hu _ _) (leafDist_nonneg root u hu _ _)
  by_cases hxy : x = y
  · subst y
    rw [leafDist_self,zero_add]
  by_cases hyz : y = z
  · subst z
    rw [leafDist_self,add_zero]
  simp only [leafDist,ite_eq_right hxz,ite_eq_right hxy,ite_eq_right hyz]
  have h := dist_triangle (parent root x) (parent root y) (parent root z)
  have hh := height_nonneg u hu y
  linarith

@[instance_reducible]
noncomputable def attachedMetric (root : C → V) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) :
    PseudoMetricSpace (V ⊕ C) where
  dist := leafDist root u
  dist_self := leafDist_self root u
  dist_comm := leafDist_comm root u
  dist_triangle := leafDist_triangle root u hu

end MetricKMedianRecovery.LeafMetric

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

@[instance_reducible] noncomputable def metric : PseudoMetricSpace (Label V) :=
  LeafMetric.attachedMetric root height (fun c=>by
    dsimp only [height]
    exact_mod_cast (le_max_right c.2.2 0))

attribute [local instance] metric

def parent : Label V → V := Sum.elim id root

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyAge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [DecidableEq V]

def level : Label V → ℕ
  | .inl _ => 0
  | .inr c => c.1+1

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SortMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
namespace WordList.Sort

def reverseTest (p : List Bool → Bool) (x : List Bool) : Bool :=
  p (pairBits (discardPrefix x,extractPrefix x))
end WordList.Sort
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [LinearOrder V]
def rationalHeight : Label V → ℚ
  | .inl _=>0
  | .inr c=>c.2.2

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open BinaryArithmetic RationalLeaves

def encode {m : ℕ} (x : Label (Fin m)) : List Bool :=
  pairBits ((level x).bits,pairBits ((parent x).val.bits,BinaryRational.encode (rationalHeight x)))
def levelWords : List Bool → List Bool := extractPrefix
def parentWords : List Bool → List Bool := extractPrefix ∘ discardPrefix
def heightWords : List Bool → List Bool := discardPrefix ∘ discardPrefix

@[simp] lemma levelWords_encode {m : ℕ} (x : Label (Fin m)) : levelWords (encode x)=(level x).bits := by
  simp only [levelWords,encode,extractPrefix_pairBits]
@[simp] lemma parentWords_encode {m : ℕ} (x : Label (Fin m)) : parentWords (encode x)=(parent x).val.bits := by
  simp only [parentWords,encode,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
@[simp] lemma heightWords_encode {m : ℕ} (x : Label (Fin m)) : heightWords (encode x)=BinaryRational.encode (rationalHeight x) := by
  simp only [heightWords,encode,Function.comp_apply,discardPrefix_pairBits]

def lt (x : List Bool) : Bool :=
  decide (value (levelWords (extractPrefix x))<value (levelWords (discardPrefix x))) ||
    (decide (value (levelWords (extractPrefix x))=value (levelWords (discardPrefix x))) &&
      (decide (value (parentWords (extractPrefix x))<value (parentWords (discardPrefix x))) ||
        (decide (value (parentWords (extractPrefix x))=value (parentWords (discardPrefix x))) &&
          decide (BinaryRational.decode (heightWords (extractPrefix x))<BinaryRational.decode (heightWords (discardPrefix x))))))

def table : List Bool → List Bool := extractPrefix ∘ extractPrefix
def label : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelMatrix
open WordList RationalLeaves
attribute [local irreducible] mapWith

def table : List Bool → List Bool := extractPrefix ∘ extractPrefix ∘ extractPrefix
def item : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryLabelMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelMember
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open BinaryArithmetic WordList RationalLeaves

def eq (x : List Bool) : Bool :=
  decide (value (levelWords (extractPrefix x))=value (levelWords (discardPrefix x))) &&
    (decide (value (parentWords (extractPrefix x))=value (parentWords (discardPrefix x))) &&
      decide (BinaryRational.decode (heightWords (extractPrefix x))=BinaryRational.decode (heightWords (discardPrefix x))))

end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelSelect
open Classical
open BinaryArithmetic WordList RationalLeaves

def alphabet : List Bool → List Bool := extractPrefix ∘ extractPrefix
def target : List Bool → List Bool := discardPrefix ∘ extractPrefix
def index : List Bool → List Bool := discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryLabelSelect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelLookup
open WordList RationalLeaves
noncomputable def item (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix x))
noncomputable def run : List Bool → List Bool := mapWith item
end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

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
open WordList BinaryOpeningPayment RationalLeaves

def labels {m : ℕ} (xs : List (Label (Fin m))) : List Bool := encode (xs.map BinaryLabel.encode)
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

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordList RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def replaceOpen (x : List Bool) : List Bool :=
  encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),discardPrefix x,
    field 4 (extractPrefix x),field 5 (extractPrefix x),field 6 (extractPrefix x),field 7 (extractPrefix x)]
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

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace WordEq
lemma value_length_injective {xs ys : List Bool} (hl : xs.length=ys.length) (hv : value xs=value ys) : xs=ys := by
  induction xs generalizing ys with
  | nil=>exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | cons b xs ih=>
    cases ys with
    | nil=>simp only [List.length_cons,List.length_nil] at hl; omega
    | cons c ys=>
      have ht : xs.length=ys.length := by simpa only [List.length_cons,Nat.add_left_inj] using hl
      have hbc : b=c := by
        cases b <;> cases c <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at hv ⊢ <;> omega
      subst c
      congr 1
      apply ih ht
      simp only [value] at hv
      omega
noncomputable def eq (x : List Bool) : Bool := decide (extractPrefix x=discardPrefix x)
end WordEq
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordList BinaryArithmetic

def lt (x : List Bool) : Bool :=
  decide (BinaryRational.decode (extractPrefix (extractPrefix x))<BinaryRational.decode (extractPrefix (discardPrefix x))) ||
  (decide (BinaryRational.decode (extractPrefix (extractPrefix x))=BinaryRational.decode (extractPrefix (discardPrefix x))) &&
    decide (value (discardPrefix (extractPrefix x))<value (discardPrefix (discardPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordList BinaryArithmetic
abbrev pack (xs : List ℕ) := WordList.encode (xs.map Nat.bits)
abbrev encode (S : Finset ℕ) := pack (S.sort (·≤·))
def lt (x : List Bool) : Bool := decide (value (extractPrefix x)<value (discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryNatSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordList
variable {n : ℕ}
def encode (S : Finset (Fin n)) : List Bool := BinaryNatSet.encode (values S)
end MetricKMedianRecovery.BitMachine.BinaryFinSet

namespace MetricKMedianRecovery.BitMachine.BinaryIndexMap
open WordList
noncomputable def item (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix x))
noncomputable def run : List Bool→List Bool := mapWith item
end MetricKMedianRecovery.BitMachine.BinaryIndexMap

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
open WordList
variable {m n : ℕ}
def table (f : Fin m→Fin n) : List Bool := WordList.encode (List.ofFn (fun i=>(f i).val.bits))
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingReference
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
def leafBits (v : Fin n) (r : ℚ) : List Bool := pairBits (v.val.bits,BinaryRational.encode r)
noncomputable def original (x : List Bool) : List Bool :=
  pairBits (Lookup.run (pairBits (discardPrefix x,extractPrefix x)),discardPrefix x)
noncomputable def originals (x : List Bool) : List Bool := mapWith original (pairBits (field 4 x,field 2 x))
noncomputable def leaf (x : List Bool) : List Bool :=
  pairBits (BinaryRational.encode
    (BinaryRational.decode (Lookup.run (pairBits (extractPrefix (discardPrefix (discardPrefix x)),discardPrefix (extractPrefix x))))+
      BinaryRational.decode (discardPrefix (discardPrefix (discardPrefix x)))),
    (value (extractPrefix (extractPrefix x))+value (extractPrefix (discardPrefix x))+1).bits)
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

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
open WordList BinaryArithmetic
variable {n : ℕ}
def leavesBits (zs : List (Fin n×ℚ)) : List Bool := encode (zs.map (fun z=>BinarySamplingReference.leafBits z.1 z.2))
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
open WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field )
variable {n : ℕ}
def encode (s : RationalSampling.State n) : List Bool := pairBits (BinaryFinSet.encode s.deleted,BinaryNearestLeaf.leavesBits s.leaves)

def context (Δ : ℚ) (S : Finset (Fin n)) (s : RationalSampling.State n) : List Bool :=
  WordList.encode [n.bits,BinaryRational.encode Δ,BinaryFinSet.encode (S\s.deleted),BinaryNearestLeaf.leavesBits s.leaves]
noncomputable def referenceInput (x : List Bool) : List Bool := extractPrefix x++WordList.encode [discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinarySamplingState

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinarySamplingState.context Δ S s]
noncomputable def row (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,field 0 (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueItem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueItem
open WordList
variable {L R : Type*} [LinearOrder R] [LinearOrder L] {n : ℕ}
def atomEnc (el : L→List Bool) (er : R→List Bool) (a : BlueDP.Atom L R (Fin n)) : List Bool :=
  pairBits (el a.1,pairBits (er a.2.1,a.2.2.val.bits))
def record (el : L→List Bool) (er : R→List Bool) (label : R→L) (q : R→Fin n→ℚ) (r : R) : List Bool :=
  pairBits (er r,pairBits (el (label r),RationalArray.encode (List.ofFn (q r))))
def records (el : L→List Bool) (er : R→List Bool) (B : Finset R) (label : R→L) (q : R→Fin n→ℚ) : List Bool :=
  WordList.encode ((B.sort (·≤·)).map (record el er label q))
def targetL (x : List Bool) : List Bool := extractPrefix (extractPrefix x)
def targetY (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
def sourceR (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
def sourceL (x : List Bool) : List Bool := extractPrefix (discardPrefix (discardPrefix x))
def sourceRow (x : List Bool) : List Bool := discardPrefix (discardPrefix (discardPrefix x))
noncomputable def price (x : List Bool) : List Bool := Lookup.run (pairBits (targetY x,sourceRow x))
noncomputable def response (x : List Bool) : List Bool := WordList.encode [pairBits (price x,
  WordList.encode [pairBits (targetL x,pairBits (sourceR x,targetY x))])]
noncomputable def op (x : List Bool) : List Bool := if WordEq.eq (pairBits (sourceL x,targetL x)) then response x else []
noncomputable def run (x : List Bool) : List Bool := BinaryBlueChoice.select (mapWith op x)
end MetricKMedianRecovery.BitMachine.BinaryBlueItem

namespace MetricKMedianRecovery.BitMachine.BinaryBlueRecords
open WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (B : Finset (Fin n)) (label : Fin n→Fin m) : List Bool :=
  encode [BinarySamplingOracle.pack δ D S Δ s,BinaryFinSet.encode B,BinaryFinSet.table label]
noncomputable def oracleInput (x : List Bool) : List Bool := pairBits (field 0 (extractPrefix x),discardPrefix x)
noncomputable def row (x : List Bool) : List Bool := BinarySamplingOracle.row (oracleInput x)
noncomputable def tag (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,field 2 (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryBlueRecords

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueBlocksMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueBlocks
open WordList
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
def labelsEnc (el : L→List Bool) (U : Finset L) : List Bool := WordList.encode ((U.sort (·≤·)).map el)
noncomputable def itemCall (x : List Bool) : List Bool := BinaryBlueItem.run
  (pairBits (pairBits (discardPrefix x,discardPrefix (extractPrefix x)),extractPrefix (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryBlueBlocks

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Subsets
variable {A : Type*}
noncomputable def addLast (x : List Bool) : List Bool := discardPrefix x++encode [extractPrefix x]
noncomputable def added (x : List Bool) : List Bool := mapWith addLast (pairBits (Find.item x,Fold.accum x))
noncomputable def op (x : List Bool) : List Bool := Fold.accum x++added x
end MetricKMedianRecovery.BitMachine.WordList.Subsets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordList
variable {n : ℕ}
noncomputable def nonemptyKey (x : List Bool) : Bool := !decide (discardPrefix x=[])
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLookup
open WordList
variable {L A : Type*} [LinearOrder L]
def encode (key : Finset L→List Bool) (enc : A→List Bool) (T : BlueDP.Table L A) : List Bool :=
  WordList.encode (T.map (fun z=>pairBits (key z.1,BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc) z.2)))
noncomputable def matchKey (x : List Bool) : Bool := WordEq.eq (pairBits (extractPrefix x,extractPrefix (discardPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryBlueLookup

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
abbrev atomEnc (er : R→List Bool) := BinaryBlueItem.atomEnc (fun i : Fin m=>i.val.bits) er (n:=n)
def ctxPack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) : List Bool :=
  encode [BinaryBlueItem.records (fun i=>i.val.bits) er B label q,BinaryFinSet.encode F,
    encode ((BlueDP.states U).map BinaryFinSet.encode),BinaryBlueLookup.encode BinaryFinSet.encode (atomEnc er) T]
noncomputable def ctx (x : List Bool) : List Bool := extractPrefix (extractPrefix x)
noncomputable def whole (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueNextTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueTable
open WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def initRow (x : List Bool) : List Bool := pairBits (discardPrefix x,
  if discardPrefix x=[] then BinaryBlueChoice.encode id (some (0,[])) else [])
noncomputable def initial (x : List Bool) : List Bool := mapWith initRow (pairBits ([],x))
end MetricKMedianRecovery.BitMachine.BinaryBlueTable

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTableSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLoop
open WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
def pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) : List Bool :=
  encode [BinaryBlueItem.records (fun i=>i.val.bits) er B label q,BinaryFinSet.encode F,
    encode ((BlueDP.states U).map BinaryFinSet.encode),BinaryFinSet.encode U,List.replicate c true]
def statePack (er : R→List Bool) (cfg : List Bool)
    (s : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))×BlueDP.Candidate (List (BlueDP.Atom (Fin m) R (Fin n)))) : List Bool :=
  pairBits (cfg,pairBits (BinaryBlueLookup.encode BinaryFinSet.encode (BinaryBlueCell.atomEnc er) s.1,
    BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc er)) s.2))
noncomputable def oldTable (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def oldBest (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
noncomputable def nextCtx (x : List Bool) : List Bool := encode
  [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),oldTable x]
noncomputable def initial (x : List Bool) : List Bool := pairBits (x,pairBits (BinaryBlueTable.initial (field 2 x),[]))
end MetricKMedianRecovery.BitMachine.BinaryBlueLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueProgram
open WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
def pack (extra : List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→Fin m) (q : R→Fin n→ℚ) (U : Finset (Fin m)) (c : ℕ) : List Bool :=
  encode [BinaryBlueItem.records (fun i=>i.val.bits) er B label q,BinaryFinSet.encode F,
    BinaryFinSet.encode U,List.replicate c true,extra]
end MetricKMedianRecovery.BitMachine.BinaryBlueProgram

namespace MetricKMedianRecovery.BitMachine.BinaryBlueOutput
open WordList
open BinaryOpeningPayment (field )
variable {m n r : ℕ}
noncomputable def matching (x : List Bool) : Bool :=
  WordEq.eq (pairBits (extractPrefix (discardPrefix x),extractPrefix x))
abbrev atomEnc := BinaryBlueCell.atomEnc (fun i : Fin r=>i.val.bits) (m:=m) (n:=n)

noncomputable def query (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
noncomputable def prepared (x : List Bool) : List Bool := pairBits (BinaryBlueMerge.payload (extractPrefix x),discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryBlueOutput

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n a : ℕ}
noncomputable def ball (x : List Bool) : List Bool := Lookup.run
  (pairBits (discardPrefix x,field 1 (extractPrefix x)))
noncomputable def columns (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (field 0 (extractPrefix x))
attribute [local irreducible] mapWith
noncomputable def indices (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (Count.run (field 1 x))
noncomputable def partRow (x : List Bool) : List Bool := mapWith extractPrefix (pairBits (discardPrefix x,columns x))
noncomputable def origin (x : List Bool) : List Bool :=
  (((field 0 (extractPrefix x)).length)*value (discardPrefix x)+value (head (ball x))).bits

noncomputable def origins (x : List Bool) : List Bool := mapWith origin (pairBits (x,indices x))
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def within (x : List Bool) : Bool := decide
  (BinaryRational.decode (Lookup.run (pairBits (discardPrefix x,extractPrefix (extractPrefix x))))≤
    BinaryRational.decode (discardPrefix (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchBalls
open WordList
open BinaryOpeningPayment (field )
variable {n a : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (F : Finset (Fin n)) (w : Fin a→Fin n) (R : Fin a→ℚ) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode F,encode (List.ofFn (fun i=>BinarySamplingReference.leafBits (w i) (R i)))]
noncomputable def row (x : List Bool) : List Bool := Lookup.run (pairBits
  (extractPrefix (discardPrefix x),field 0 (extractPrefix x)))
noncomputable def input (x : List Bool) : List Bool := pairBits
  (pairBits (row x,discardPrefix (discardPrefix x)),field 1 (extractPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryBranchBalls

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
open WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def tag (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix (extractPrefix x)))
noncomputable def matching (x : List Bool) : Bool := WordEq.eq (pairBits (tag x,discardPrefix (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryClassFilter

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def ballInput (x : List Bool) : List Bool := encode [field 0 x,field 2 x,discardPrefix (field 5 x)]
attribute [local irreducible] ballInput
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRows
open WordList
open BinaryOpeningPayment (field )
variable {n q r : ℕ}
noncomputable def oracleInput (j : ℕ) (x : List Bool) : List Bool := pairBits (field j (extractPrefix x),discardPrefix x)
noncomputable def row (x : List Bool) : List Bool := BinarySamplingOracle.row (oracleInput 0 x)
noncomputable def distances (x : List Bool) : List Bool := BinaryIndexMap.run (pairBits (row x,field 2 (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryBranchRows

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchCheck
open WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def badBall (x : List Bool) : Bool := decide (discardPrefix x=[])
noncomputable def badRadius (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix (discardPrefix x))<0)
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

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
open WordList BinaryArithmetic DyadicGrid
open BinaryOpeningPayment (field )
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
def gf (n : ℕ) : List Bool → List Bool := field n ∘ discardPrefix
def num : List Bool → List Bool := extractPrefix ∘ discardPrefix
def den : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def pointWords (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (cf 2 x)+(BinaryRational.decode (cf 3 x)-BinaryRational.decode (cf 2 x))*
    (value (num x):ℚ)/(value (den x):ℚ))
noncomputable def doubled (n : ℕ) (x : List Bool) : List Bool := (2*value (gf n x)).bits
noncomputable def summed (x : List Bool) : List Bool := (value (gf 0 x)+value (gf 1 x)).bits
noncomputable def midpoint (x : List Bool) : List Bool := pointWords (pairBits (extractPrefix x,pairBits (summed x,doubled 2 x)))
noncomputable def queryInput (x : List Bool) : List Bool := pairBits (cf 0 x,midpoint x)
noncomputable def chooseLeft (query : List Bool→List Bool) (x : List Bool) : Bool :=
  decide (value (cf 1 x)≤value (query (queryInput x)))
noncomputable def upLeft (x : List Bool) : List Bool := encode [summed x,doubled 1 x,doubled 2 x]
noncomputable def upRight (x : List Bool) : List Bool := encode [doubled 0 x,summed x,doubled 2 x]
noncomputable def step (query : List Bool→List Bool) (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,if chooseLeft query x then upLeft x else upRight x)
def stateBits (ctx : List Bool) (g : State) : List Bool := pairBits (ctx,encode [g.1.bits,g.2.1.bits,g.2.2.bits])
noncomputable def initial (x : List Bool) : List Bool := stateBits (discardPrefix x) start
noncomputable def endpoint (n : ℕ) (x : List Bool) : List Bool := pointWords (pairBits (extractPrefix x,pairBits (gf n x,gf 2 x)))
noncomputable def finish (x : List Bool) : List Bool := pairBits (endpoint 0 x,endpoint 1 x)
end MetricKMedianRecovery.BitMachine.BinaryGrid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_BisectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBisection
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def predWords (x : List Bool) : List Bool := (value x-1).bits
noncomputable def logWord (x : List Bool) : List Bool := RepeatedAppend.copies (predWords x).length [true]
noncomputable def width (x : List Bool) : ℚ := BinaryRational.decode (field 4 x)-BinaryRational.decode (field 3 x)
noncomputable def widthCeil (x : List Bool) : List Bool := (Nat.ceil (width x)).bits
noncomputable def fuel (x : List Bool) : List Bool := field 0 x++logWord (widthCeil x)
noncomputable def context (x : List Bool) : List Bool := encode [field 1 x,field 2 x,field 3 x,field 4 x]
noncomputable def input (x : List Bool) : List Bool := pairBits (fuel x,context x)
def pack (N : ℕ) (ctx : List Bool) (k : ℕ) (a b : ℚ) : List Bool :=
  encode [List.replicate N true,ctx,k.bits,BinaryRational.encode a,BinaryRational.encode b]
end MetricKMedianRecovery.BitMachine.BinaryBisection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryAdvance
open WordList RationalLeaves
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field )

def pack {m : ℕ} (base : List Bool) (C U : List (Label (Fin m))) (i ci : Label (Fin m)) : List Bool :=
  encode [base,labels C,labels U,BinaryLabel.encode i,BinaryLabel.encode ci]
noncomputable def deletionInput (x : List Bool) : List Bool :=
  Fold.pack (field 2 x) (encode [field 0 x,field 1 x,field 4 x]) (encode [field 2 x,[],[]])
noncomputable def firstVertex (x : List Bool) : List Bool := field 1 x++field 2 x++WordList.cons (field 4 x) []
end MetricKMedianRecovery.BitMachine.BinaryAdvance

end OAI
end


