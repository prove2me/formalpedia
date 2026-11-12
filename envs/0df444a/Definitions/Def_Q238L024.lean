-- Prove2me | Definitions.Def_Q238L024
-- name    : Q238L024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:06.266884+00:00
-- url     : https://prove2.me/theorems/3c88776f-374b-4b70-8e28-b5d0ff2ea212
-- title:
--   Definitions bundle Q238L024 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 148 declarations of OpenAI's Lean: 147 definitions and 1 theorem. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identity`, `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.atCall`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.atCenter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.block`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.bad`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.contents`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.result`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLookup.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.nextCtx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.statePack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.destination`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.matching`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.pick`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.source`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.op`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.scaled`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.weight`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchBalls.ball`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchBalls.balls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchBalls.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchBalls.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badRadii`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts` and 107 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Branching_BlueBlocksMachine`, `KMedianRecovery_Branching_BlueItem`, `KMedianRecovery_Branching_BlueLookup`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BlueProgram`, `KMedianRecovery_Branching_BlueTableSize`, `KMedianRecovery_Branching_BranchBalls`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchPhysical`, `KMedianRecovery_Branching_BranchWeights`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_LabelMember`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_RationalBest`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Geometry_NearestLeafMachine`, `KMedianRecovery_Machines_CappedFold`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_ClassFilter`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_ListSetExtra`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_SortMath`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Sampling_SamplingReference`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L013`, `Q238L014`, `Q238L015`, `Q238L017` and `Q238L018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L028`, `Q238L029`, `Q238L030` and `Q238L031`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls_nil_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238r` and `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls_nil_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238r` and `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L013
import Definitions.Def_Q238L014
import Definitions.Def_Q238L015
import Definitions.Def_Q238L017
import Definitions.Def_Q238L018

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DivNatWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed

def divNatWords (x : List Bool) : List Bool :=
  if value (discardPrefix x)=0 then encode 0
  else if sign (extractPrefix x) then
    if mag (extractPrefix x)%value (discardPrefix x)=0 then
      pack true (mag (extractPrefix x)/value (discardPrefix x)).bits
    else pack true (mag (extractPrefix x)/value (discardPrefix x)+1).bits
  else pack false (mag (extractPrefix x)/value (discardPrefix x)).bits

end Signed
namespace BinaryRational

def floorWords : List Bool → List Bool := Signed.divNatWords

def ceilWords : List Bool → List Bool := (fun x=>Signed.encode (-Signed.decode x)) ∘ floorWords ∘ negWords

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake
namespace BoundedIteration

lemma run_eq (f : List Bool → List Bool) (c d s : List Bool)
    (h : ∀ j, j ≤ c.length → (f^[j] s).length ≤ d.length) :
    run f (pairBits (c,pairBits (d,s)))=f^[c.length] s := by
  rw [run_pair]; exact clamp_iterate_eq f d.length c.length s h

end BoundedIteration
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GetRow2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

noncomputable def diagInput_computes : PolyComputes diagInput := id_computes.pair discardPrefix_computes

end RationalMatrix
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

noncomputable def shape_computes : PolyComputes shape := discardPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes

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
namespace BinaryRow
open RationalMatrix

def encode {n : ℕ} (r : Row n) : List Bool := pairBits (rowEncode r.coeff,BinaryRational.encode r.bound)
def rowsEncode {n : ℕ} (rows : List (Row n)) : List Bool := WordList.encode (rows.map encode)
end BinaryRow
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def rest₃_computes : PolyComputes rest₃ := rest₂_computes.comp discardPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₃_computes.comp discardPrefix_computes
end BinaryWeakSolve
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
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

def pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate m true,
    pairBits (B.bits,BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (A r) (b r))))))
end BinaryBoundedDecision

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

section
open WordOperations BinaryArithmetic Matrix
namespace Rectangular
open WordList RationalMatrix

def encode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : List Bool :=
  WordList.encode (List.ofFn (fun i=>rowEncode (A i)))
end Rectangular
end

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
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
namespace MetricTable
open WordList

noncomputable def col_computes : PolyComputes col := discardPrefix_computes
end MetricTable
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FilterItem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def filterWith (p : List Bool → Bool) : List Bool → List Bool := flatMapWith (filterItem p)
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_StateBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase
open BinaryOpeningPayment

noncomputable def newBudget_computes : PolyComputes newBudget := discardPrefix_computes.comp discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

end OAI
end

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

noncomputable def nearest (x : List Bool) : ℚ :=
  BinaryRational.decode (BinaryOpeningNearest.run (BinaryOpeningPayment.activityInput (query x)))
noncomputable def clippedItem (x : List Bool) : ℚ :=
  if sf 1 (extractPrefix x)=[] then phase (extractPrefix x)
  else min (phase (extractPrefix x)) ((1-3*paramV (extractPrefix x))*nearest x)
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

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
open WordOperations
namespace WordList.Sort

noncomputable def insert (p : List Bool → Bool) (x : List Bool) : List Bool :=
  filterWith (reverseTest p) x ++ cons (extractPrefix x) (filterWith p x)

variable {α : Type*} [LinearOrder α]

noncomputable def op (p : List Bool → Bool) (x : List Bool) : List Bool :=
  insert p (pairBits (Find.item x,Fold.accum x))

noncomputable def run (p : List Bool → Bool) (x : List Bool) : List Bool :=
  Fold.run (op p) (3*Polynomial.X+3) (Fold.pack x [] [])
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

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves

noncomputable def heightWords_computes : PolyComputes heightWords := discardPrefix_computes.comp discardPrefix_computes

noncomputable def sort : List Bool → List Bool := WordList.Sort.run lt
noncomputable def col_computes : PolyComputes col := discardPrefix_computes
noncomputable def rawRow (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (table x,parentWords (label x)),col x))
attribute [local irreducible] MetricTable.get
noncomputable def row (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (rawRow x)+max (BinaryRational.decode (heightWords (label x))) 0)
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelMatrix
open WordOperations WordList RationalLeaves
attribute [local irreducible] mapWith

noncomputable def col_computes : PolyComputes col := discardPrefix_computes
noncomputable def entry (x : List Bool) : List Bool :=
  BinaryLabel.row (pairBits (pairBits (table x,item x),col x))

noncomputable def row (x : List Bool) : List Bool :=
  mapWith entry (pairBits (x,BinaryEllipsoidInitial.indices (discardPrefix (extractPrefix x))))

noncomputable def run : List Bool → List Bool := mapWith row
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
open WordOperations BinaryArithmetic WordList RationalLeaves

noncomputable def contains (x : List Bool) : Bool := decide (Find.run eq x≠[])

end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelSelect
open Classical
open WordOperations BinaryArithmetic WordList RationalLeaves EffectiveOpenability

noncomputable def index_computes : PolyComputes index := discardPrefix_computes
noncomputable def test (x : List Bool) : Bool :=
  BinaryLabel.contains (pairBits (Lookup.run (pairBits (index x,alphabet x)),target x))

noncomputable def run (x : List Bool) : List Bool :=
  filterWith test (pairBits (x,Indices.run (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryLabelSelect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinishPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseCount
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment
attribute [local irreducible] WordList.map WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run
noncomputable def zeroBudget : List Bool → List Bool :=
  WordList.map (fun _=>BinaryRational.encode 0) ∘ BinaryOpeningEnumeration.clients
noncomputable def start (x : List Bool) : List Bool :=
  pairBits (contextAt x,zeroBudget (extractPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

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

noncomputable def alphabet (x : List Bool) : List Bool :=
  BinaryLabel.sort (field 2 x++field 3 x++field 4 x)

noncomputable def selected (k : ℕ) (x : List Bool) : List Bool :=
  BinaryLabelSelect.run (pairBits (alphabet x,field k x))

noncomputable def matrix (x : List Bool) : List Bool :=
  BinaryLabelMatrix.run (pairBits (pairBits (field 0 x,field 1 x),alphabet x))
attribute [local irreducible] BinaryLabelMatrix.run

noncomputable def run (x : List Bool) : List Bool := encode
  [matrix x,selected 3 x,field 5 x,field 6 x,field 7 x,BinaryRational.encode 0,[],field 1 x,selected 2 x]
attribute [local irreducible] matrix selected
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

noncomputable def initial (x : List Bool) : List Bool := BinaryPhaseCount.start
  (pairBits (BinaryFiniteContext.run x,field 6 x))
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )

noncomputable def union (x : List Bool) : List Bool := BinaryLabel.sort (extractPrefix x++discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves PhaseSequence
open BinaryFiniteContext (labels )
noncomputable def after (x : List Bool) : List Bool :=
  BinaryLabel.sort (extractPrefix x++Flatten.run (discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

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
open WordOperations WordList BinaryArithmetic

noncomputable def sort : List Bool→List Bool := Sort.run lt
noncomputable def ranked (x : List Bool) : List Bool :=
  mapWith (fun y=>pairBits (discardPrefix (discardPrefix y),extractPrefix (discardPrefix y)))
    (pairBits ([],Zip.run (pairBits (Indices.run x,x))))
attribute [local irreducible] sort ranked
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordOperations WordList BinaryArithmetic
noncomputable def sort : List Bool→List Bool := Sort.run lt
noncomputable def union (x : List Bool) : List Bool := sort (extractPrefix x++discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryNatSet

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
attribute [local irreducible] mapWith flatMapWith
noncomputable def parts (x : List Bool) : List Bool := flatMapWith partRow (pairBits (x,indices x))
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CappedFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
noncomputable def RepeatedAppend.fixed_computes (n : ℕ) : PolyComputes (RepeatedAppend.copies n) := by
  induction n with
  | zero => exact const_computes []
  | succ n ih => exact ih.append id_computes
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalMinKey
open WordOperations WordList
noncomputable def run (x : List Bool) : List Bool := head (BinaryRationalSort.sort x)
end MetricKMedianRecovery.BitMachine.BinaryRationalMinKey

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
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
def leafBits (v : Fin n) (r : ℚ) : List Bool := pairBits (v.val.bits,BinaryRational.encode r)
noncomputable def leaves (x : List Bool) : List Bool := mapWith leaf
  (pairBits (pairBits (field 0 x,field 4 x),Zip.run (pairBits (Indices.run (field 3 x),field 3 x))))
noncomputable def entries (x : List Bool) : List Bool := originals x++cons (pairBits (field 1 x,field 0 x)) (leaves x)
noncomputable def run (x : List Bool) : List Bool := BinaryRationalMinKey.run (entries x)
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
open WordOperations WordList BinaryArithmetic
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
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field )
variable {n : ℕ}
def encode (s : RationalSampling.State n) : List Bool := pairBits (BinaryFinSet.encode s.deleted,BinaryNearestLeaf.leavesBits s.leaves)

def context (Δ : ℚ) (S : Finset (Fin n)) (s : RationalSampling.State n) : List Bool :=
  WordList.encode [n.bits,BinaryRational.encode Δ,BinaryFinSet.encode (S\s.deleted),BinaryNearestLeaf.leavesBits s.leaves]
noncomputable def reference (x : List Bool) : List Bool := BinarySamplingReference.run (referenceInput x)
end MetricKMedianRecovery.BitMachine.BinarySamplingState

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinarySamplingState.context Δ S s]
noncomputable def reference (x : List Bool) : List Bool := BinarySamplingState.reference (pairBits (field 2 (extractPrefix x),row x))
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

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
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n a : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (F : Finset (Fin n)) (w : Fin a→Fin n) (R : Fin a→ℚ) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode F,encode (List.ofFn (fun i=>BinarySamplingReference.leafBits (w i) (R i)))]
noncomputable def ball : List Bool→List Bool := filterWith BinarySampler.Update.within ∘ input
noncomputable def balls (x : List Bool) : List Bool := mapWith ball (pairBits (x,field 2 x))
noncomputable def run (x : List Bool) : List Bool := encode [Count.run (field 0 x),balls x]
end MetricKMedianRecovery.BitMachine.BinaryBranchBalls

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {E : Type*} {a T : ℕ}
noncomputable def drawItems (x : List Bool) : List Bool := Zip.run (pairBits (Indices.run (field 1 x),field 1 x))
noncomputable def draw (x : List Bool) : List Bool := flatMapWith drawPick (pairBits (x,drawItems x))
noncomputable def advanceItem (x : List Bool) : List Bool :=
  Set.run (Set.pack (Lookup.run (pairBits (discardPrefix x,field 0 (extractPrefix x))))
    (field 2 (extractPrefix x)) (encode [Lookup.run (pairBits (discardPrefix x,field 1 (extractPrefix x)))]))
attribute [local irreducible] Set.run mapWith
noncomputable def advance (x : List Bool) : List Bool :=
  mapWith advanceItem (pairBits (x,Indices.run (field 1 x)))
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
noncomputable def marginalDraw (x : List Bool) : List Bool :=
  draw (encode [field 1 (extractPrefix (extractPrefix x)),discardPrefix x,elementPart (extractPrefix x)])
noncomputable def marginal (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (g (pairBits (field 0 (extractPrefix (extractPrefix x)),
      cons (discardPrefix (extractPrefix x)) (marginalDraw x))))-
    BinaryRational.decode (g (pairBits (field 0 (extractPrefix (extractPrefix x)),marginalDraw x))))
noncomputable def marginalValues (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  mapWith (marginal g) (pairBits (x,elementSamples x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )

attribute [local irreducible] mapWith
noncomputable def cap (x : List Bool) : List Bool :=
  RationalMin.run (cons (field 0 (discardPrefix x)) (offers x))
attribute [local irreducible] RationalMin.run
noncomputable def weightedCap (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (extractPrefix (discardPrefix x))*
    BinaryRational.decode (cap (pairBits (extractPrefix x,discardPrefix (discardPrefix x)))))
end MetricKMedianRecovery.BitMachine.BinaryCompletion

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
noncomputable def run (score : List Bool→List Bool) (x : List Bool) : List Bool :=
  CappedFold.run (choose score) (pairBits (x,Fold.pack (discardPrefix (discardPrefix x)) (extractPrefix x)
    (extractPrefix (discardPrefix x))))
noncomputable def fromList (score : List Bool→List Bool) (x : List Bool) : List Bool :=
  run score (pairBits (extractPrefix x,pairBits (head (discardPrefix x),tail (discardPrefix x))))
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

namespace MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
def pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) : List Bool :=
  encode [BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits,raw]
end MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCollect
open WordOperations WordList
variable {A : Type*}
noncomputable def bad (x : List Bool) : List Bool := Find.run invalid (pairBits ([],x))
attribute [local irreducible] mapWith
noncomputable def contents (x : List Bool) : List Bool := flatMapWith payloadOp (pairBits ([],x))
noncomputable def result (x : List Bool) : List Bool := WordList.encode [pairBits (RationalArray.sumWords (scores x),contents x)]
noncomputable def run (x : List Bool) : List Bool := if bad x=[] then result x else []
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def identity (x : List Bool) : List Bool := discardPrefix (BinarySamplingOracle.reference x)
noncomputable def identities (x : List Bool) : List Bool := mapWith identity (pairBits (x,field 1 x))
noncomputable def count (x : List Bool) : List Bool := Count.run (filterWith WordEq.eq x)
noncomputable def run (x : List Bool) : List Bool := BinaryRational.encode ((count x).length:ℚ)
end MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueItem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueRecords
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (B : Finset (Fin n)) (label : Fin n→Fin m) : List Bool :=
  encode [BinarySamplingOracle.pack δ D S Δ s,BinaryFinSet.encode B,BinaryFinSet.table label]
noncomputable def row (x : List Bool) : List Bool := BinarySamplingOracle.row (oracleInput x)
noncomputable def weight (x : List Bool) : List Bool := BinaryAssignmentWeight.run (pairBits
  (discardPrefix x,BinaryAssignmentWeight.identities (field 0 (extractPrefix x))))
noncomputable def scaled (x : List Bool) : List Bool := RationalMatrix.vectorScale (pairBits (weight x,row x))
noncomputable def op (x : List Bool) : List Bool := pairBits (discardPrefix x,pairBits (tag x,scaled x))
noncomputable def run (x : List Bool) : List Bool := mapWith op (pairBits (x,field 1 x))
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
open WordOperations WordList
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
noncomputable def atCenter (x : List Bool) : List Bool := BinaryBlueCollect.run (mapWith itemCall x)
noncomputable def atCall (x : List Bool) : List Bool := atCenter
  (pairBits (pairBits (extractPrefix (extractPrefix x),discardPrefix x),discardPrefix (extractPrefix x)))
noncomputable def run (x : List Bool) : List Bool := BinaryBlueChoice.select (mapWith atCall x)
end MetricKMedianRecovery.BitMachine.BinaryBlueBlocks

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
open WordOperations WordList
variable {L A : Type*} [LinearOrder L]
noncomputable def run (x : List Bool) : List Bool := discardPrefix (List.tail (Find.run matchKey x))
end MetricKMedianRecovery.BitMachine.BinaryBlueLookup

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def block (x : List Bool) : List Bool := BinaryBlueBlocks.run
  (pairBits (pairBits (field 0 (ctx x),discardPrefix x),field 1 (ctx x)))
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

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
open WordOperations WordList
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
noncomputable def nextCtx (x : List Bool) : List Bool := encode
  [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),oldTable x]
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
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
def pack (extra : List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→Fin m) (q : R→Fin n→ℚ) (U : Finset (Fin m)) (c : ℕ) : List Bool :=
  encode [BinaryBlueItem.records (fun i=>i.val.bits) er B label q,BinaryFinSet.encode F,
    BinaryFinSet.encode U,List.replicate c true,extra]
end MetricKMedianRecovery.BitMachine.BinaryBlueProgram

namespace MetricKMedianRecovery.BitMachine.BinaryBlueOutput
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {m n r : ℕ}
noncomputable def matching (x : List Bool) : Bool :=
  WordEq.eq (pairBits (extractPrefix (discardPrefix x),extractPrefix x))
noncomputable def pick (x : List Bool) : List Bool := head (filterWith matching x)
noncomputable def source (x : List Bool) : List Bool := extractPrefix (discardPrefix (pick (query x)))
noncomputable def destination (x : List Bool) : List Bool := discardPrefix (discardPrefix (pick (query x)))
noncomputable def prepared (x : List Bool) : List Bool := pairBits (BinaryBlueMerge.payload (extractPrefix x),discardPrefix x)
noncomputable def run (x : List Bool) : List Bool := encode [mapWith source (prepared x),mapWith destination (prepared x)]
end MetricKMedianRecovery.BitMachine.BinaryBlueOutput

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
noncomputable def matching (x : List Bool) : Bool := WordEq.eq (pairBits (tag x,discardPrefix (extractPrefix x)))
noncomputable def run : List Bool→List Bool := filterWith matching
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
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,
    BinaryRational.encode Δ,BinarySamplingState.encode s,BinaryFinSet.table colors,BinaryFinSet.table label,
    BinaryFinSet.table (id : Fin m→Fin m),k.bits,List.replicate c true,extra]
attribute [local irreducible] ballInput
noncomputable def copyData (x : List Bool) : List Bool := BinaryBranchBalls.run (ballInput x)
attribute [local irreducible] copyData
noncomputable def parts (x : List Bool) : List Bool := BinaryCopyTables.parts (copyData x)
attribute [local irreducible] parts
noncomputable def origins (x : List Bool) : List Bool := BinaryCopyTables.origins (copyData x)
attribute [local irreducible] origins
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

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
noncomputable def bagWords (x : List Bool) : List Bool :=
  filterWith bagTest (pairBits (x,Indices.run (field 3 (extractPrefix x))))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRawPrep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a : ℕ}
noncomputable def options (x : List Bool) : List Bool :=
  filterWith test (pairBits (encode [field 0 (extractPrefix x),discardPrefix x],field 2 (extractPrefix x)))
noncomputable def pick (x : List Bool) : List Bool :=
  if options x=[] then Lookup.run (pairBits (discardPrefix x,field 1 (extractPrefix x))) else WordList.head (options x)
attribute [local irreducible] options

noncomputable def run (x : List Bool) : List Bool := mapWith pick (pairBits (x,Indices.run (field 1 x)))
end MetricKMedianRecovery.BitMachine.BinaryCompletionFill

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q p r : ℕ}
noncomputable def clientValues (x : List Bool) : List Bool :=
  mapWith cap (pairBits (discardPrefix x,field 1 (extractPrefix x)))
noncomputable def redValues (x : List Bool) : List Bool :=
  mapWith weightedCap (pairBits (discardPrefix x,field 2 (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryCompletion

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRows
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n q r : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S G : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (loc : Fin q→Fin n) (red : Fin r→Fin n) (k : ℕ) : List Bool :=
  encode [BinarySamplingOracle.pack δ D S Δ s,BinarySamplingOracle.pack δ D G Δ ⟨∅,s.leaves⟩,
    BinaryFinSet.table loc,BinaryFinSet.table red,k.bits]
noncomputable def row (x : List Bool) : List Bool := BinarySamplingOracle.row (oracleInput 0 x)
noncomputable def distances (x : List Bool) : List Bool := BinaryIndexMap.run (pairBits (row x,field 2 (extractPrefix x)))
noncomputable def base (j : ℕ) (x : List Bool) : List Bool := extractPrefix (BinarySamplingOracle.reference (oracleInput j x))
noncomputable def capRow (j : ℕ) (x : List Bool) : List Bool := encode [base j x,distances x]
noncomputable def weight (x : List Bool) : List Bool := BinaryAssignmentWeight.run (pairBits
  (discardPrefix x,BinaryAssignmentWeight.identities (field 0 (extractPrefix x))))
noncomputable def redRow (x : List Bool) : List Bool := pairBits (weight x,capRow 1 x)
noncomputable def clients (x : List Bool) : List Bool := mapWith (capRow 0) (pairBits (x,field 1 (field 0 x)))
noncomputable def reds (x : List Bool) : List Bool := mapWith redRow (pairBits (x,field 3 x))
noncomputable def run (x : List Bool) : List Bool := encode [field 4 x,clients x,reds x]
end MetricKMedianRecovery.BitMachine.BinaryBranchRows

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
noncomputable def redValues (x : List Bool) : List Bool := BinaryCompletion.redValues (pairBits (field 10 x,field 9 x))
attribute [local irreducible] redValues BinaryNatSet.sort
noncomputable def blue (x : List Bool) : List Bool := BinaryNatSet.sort (field 7 x)
noncomputable def dest (x : List Bool) : List Bool := BinaryNatSet.sort (field 8 x)
attribute [local irreducible] blue dest BinaryNatSet.union
noncomputable def added (x : List Bool) : List Bool := BinaryNatSet.union (pairBits (filled x,dest x))
attribute [local irreducible] filled
attribute [local irreducible] added
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ListSetExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Set
open WordOperations BinaryArithmetic
noncomputable def pack_computes {xs j v : List Bool→List Bool}
    (hx : PolyComputes xs) (hj : PolyComputes j) (hv : PolyComputes v) :
    PolyComputes (fun x=>pack (xs x) (j x) (v x)) := hx.pair (hj.pair hv)
end MetricKMedianRecovery.BitMachine.WordList.Set

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
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def badBalls (x : List Bool) : List Bool := filterWith badBall (pairBits ([],field 1 (copyData x)))
noncomputable def badRadii (x : List Bool) : List Bool := filterWith badRadius (pairBits ([],discardPrefix (field 5 x)))
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

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
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field )

noncomputable def openSet (x : List Bool) : List Bool :=
  BinaryFiniteContext.union (pairBits (field 3 (cf 0 x),retained x))
noncomputable def extended (x : List Bool) : List Bool :=
  BinaryFiniteContext.replaceOpen (pairBits (cf 0 x,openSet x))
end MetricKMedianRecovery.BitMachine.BinaryDelete

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
noncomputable def den_computes : PolyComputes den := discardPrefix_computes.comp discardPrefix_computes
noncomputable def initial_computes : PolyComputes initial := discardPrefix_computes.pair (const_computes (encode ([0,1,1].map Nat.bits)))
end MetricKMedianRecovery.BitMachine.BinaryGrid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves BinaryArithmetic
noncomputable def containsItem (x : List Bool) : Bool := BinaryLabel.contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def inter (x : List Bool) : List Bool :=
  BinaryLabel.sort (filterWith containsItem (pairBits (discardPrefix x,extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

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
open BinaryFiniteContext (labels )
variable {m d : ℕ}
def pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (M : ℚ) (k : ℕ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,BinaryFinSet.encode F,
    encode (List.ofFn (fun j=>(loc j).val.bits)),BinaryRational.encode M,k.bits]
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SurplusPostprocess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
variable {m : ℕ}
def pack (δ : Fin m→Fin m→ℕ) (F D : Finset (Fin m)) (M h L : ℕ) : List Bool :=
  pairBits (BinaryInitialAuto.pack (fun i j=>(δ (SortedIndex.enum D j) i:ℚ))
    (SortedIndex.enum D) F (M:ℚ) h,(h+L).bits)
end MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus

end OAI
end


