-- Prove2me | Definitions.Def_Q238L028
-- name    : Q238L028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:28:21.264061+00:00
-- url     : https://prove2.me/theorems/fd62e35e-758d-45de-9ff0-7418fc5f2c92
-- title:
--   Definitions bundle Q238L028 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 148 declarations of OpenAI's Lean: 140 definitions and 8 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.block`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.entry`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.menus`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.predWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.old`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.invalid_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.loop`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.newBest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.newTable`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.prepare`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.states`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueStates.blocks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueStates.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.lhs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.outside`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.rhs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.classOf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.greenContext`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.greenOracle`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.oracle`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.remaining`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.blueInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.records`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.runCap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.score`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.entries_computes` and 100 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueLookup`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BlueNextTable`, `KMedianRecovery_Branching_BlueProgram`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_BlueTableSize`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchPhysical`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_LabelMember`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_NatWords`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Encoding_WordSubsets`, `KMedianRecovery_Machines_ActionMachine`, `KMedianRecovery_Machines_BisectionMachine`, `KMedianRecovery_Machines_DeleteSize`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Machines_LoopInput2`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_DecisionOps`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_Next`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack4`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_RawSlices`, `KMedianRecovery_Recovery_SortMath`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L022`, `Q238L023` and `Q238L024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L032`, `Q238L033`, `Q238L034` and `Q238L035`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowWord_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L022
import Definitions.Def_Q238L023
import Definitions.Def_Q238L024

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DigitBit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction WordOperations

noncomputable def setupWords_computes : PolyComputes setupWords :=
  pack_computes true (extractPrefix_computes.comp reverse_computes) discardPrefix_computes
    (const_computes []) (const_computes [])

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryGCD
open BinaryArithmetic BinarySubtraction WordOperations

noncomputable def second_computes : PolyComputes second := tail_computes.comp discardPrefix_computes

end BinaryGCD
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeftNum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

noncomputable def leftDen_computes : PolyComputes leftDen := extractPrefix_computes.comp denominator_computes
lemma invWords_encode (x : ℚ) : invWords (encode x)=encode x⁻¹ := by
  simp only [invWords,Function.comp_apply,reduce_correct,rawInv,numerator_encode,denominator_encode,
    Signed.encode_mag,Signed.sign_encode,value_bits,
    Signed.pack_bits,decode_pair]
  by_cases hz : x.num=0
  · have hx : x=0 := Rat.num_eq_zero.mp hz
    subst x
    simp only [Rat.num_zero,Int.natAbs_zero,Rat.mkRat_zero,inv_zero]
  · rw [signed_sign x.num x.den hz]
    exact congrArg encode (by simpa only [Rat.num_inv,Rat.den_inv,hz,ite_false, if_false] using Rat.mkRat_self x⁻¹)

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryResources
lemma cap_length (x : List Bool) : (cap.word x).length=2*x.length+2 := by
  rw [cap.word_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
lemma lengthBits_eq (x : List Bool) : lengthBits x=x.length.bits := by
  unfold lengthBits
  rw [BoundedIteration.run_eq,inc_iter]
  intro j hj
  rw [inc_iter,cap_length]
  exact (WordList.Indices.bits_length_le j).trans (by omega)

noncomputable def triple_computes : PolyComputes triple := by
  change PolyComputes (fun x=>(3*value x).bits)
  have hh := NatOps.mul (const_computes (3:ℕ).bits) id_computes
  simpa only [triple,Function.comp_def,id_eq,value_bits] using hh
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
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

noncomputable def swapWords_computes : PolyComputes swapWords :=
  discardPrefix_computes.pair extractPrefix_computes
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

noncomputable def contextMatrix_computes : PolyComputes contextMatrix := extractPrefix_computes.comp extractPrefix_computes
noncomputable def contextIndex_computes : PolyComputes contextIndex := extractPrefix_computes.comp discardPrefix_computes
noncomputable def tailDiagInput_computes : PolyComputes tailDiagInput := contextMatrix_computes.pair discardPrefix_computes

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

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

lemma divNatWords_spec (x : List Bool) : divNatWords x=
    encode (decode (extractPrefix x)/(value (discardPrefix x):ℤ)) := by
  change _=encode (signed (sign (extractPrefix x)) (mag (extractPrefix x))/_)
  rw [signed_ediv_nat]
  unfold divNatWords
  split_ifs <;> simp only [pack_bits]

end Signed
namespace BinaryRational

lemma floorWords_encode (x : ℚ) : floorWords (encode x)=Signed.encode (⌊x⌋:ℤ) := by
  simp only [floorWords,Signed.divNatWords_spec,encode,extractPrefix_pairBits,discardPrefix_pairBits,
    Signed.encode_decode,value_bits,Rat.floor_def']
lemma ceilWords_encode (x : ℚ) : ceilWords (encode x)=Signed.encode (⌈x⌉:ℤ) := by
  simp only [ceilWords,Function.comp_apply,negWords_encode,floorWords_encode,Signed.encode_decode,
    Int.floor_neg,neg_neg]

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Next
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinarySqrt

noncomputable def low_computes : PolyComputes low := discardPrefix_computes.comp extractPrefix_computes
end BinarySqrt
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NumAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryEllipsoidRoot

noncomputable def numAbs_computes : PolyComputes numAbs :=
  (extractPrefix_computes.comp extractPrefix_computes).comp tail_computes
noncomputable def den_computes : PolyComputes den := extractPrefix_computes.comp discardPrefix_computes
noncomputable def radicand_computes : PolyComputes radicand := by
  have hh := NatOps.mul (NatOps.mul numAbs_computes den_computes)
    (NatOps.mul precision_computes precision_computes)
  change PolyComputes (fun x => (value (numAbs x)*value (den x)*(value (precision x)*value (precision x))).bits)
  simpa only [value_bits] using hh
noncomputable def denom_computes : PolyComputes denom := NatOps.mul den_computes precision_computes
lemma run_encode (q : ℚ) (D : ℕ) : run (pairBits (BinaryRational.encode q,D.bits))=
    BinaryRational.encode (Ellipsoid.rationalRootUpper D q) := by
  simp only [run,Function.comp_apply,rawWords,upper,denom,radicand,numAbs,den,precision,
    BinaryRational.encode,extractPrefix_pairBits,discardPrefix_pairBits,Signed.encode,
    List.tail_cons,value_bits,BinarySqrt.run_bits]
  rw [BinaryRational.reduce_correct]
  change BinaryRational.encode (BinaryRational.decode (pairBits
    (Signed.encode (((Nat.sqrt (q.num.natAbs*q.den*(D*D))+1):ℕ):ℤ),
      (q.den*D).bits)))=BinaryRational.encode _
  rw [BinaryRational.decode_pair,Rat.mkRat_eq_div]
  congr 1
  simp only [Ellipsoid.rationalRootUpper,Ellipsoid.sqrtUpperFraction,pow_two,Int.cast_natCast]

end BinaryEllipsoidRoot
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryRational

lemma subWords_pair (a b : ℚ) : subWords (pairBits (encode a,encode b))=encode (a-b) := by
  simp only [subWords,Function.comp_apply,subInput,extractPrefix_pairBits,discardPrefix_pairBits,
    negWords_encode,addWords_pair,sub_eq_add_neg]
end BinaryRational
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

noncomputable def dim_computes : PolyComputes dim := extractPrefix_computes
noncomputable def shape_computes : PolyComputes shape := rest_computes.comp extractPrefix_computes
noncomputable def direction_computes : PolyComputes direction := rest₂_computes.comp extractPrefix_computes
noncomputable def center_computes : PolyComputes center := rest₃_computes.comp extractPrefix_computes
noncomputable def precision_computes : PolyComputes precision := rest₃_computes.comp discardPrefix_computes
noncomputable def haInput_computes : PolyComputes haInput := shape_computes.pair direction_computes
noncomputable def rootPrecision_computes : PolyComputes (fun x=>(rootPrecision x).bits) := by
  have hh := NatOps.mul (const_computes (Nat.bits 32)) dim_computes
  change PolyComputes (fun x=>(32*value (dim x)).bits)
  simpa only [value_bits] using hh
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

noncomputable def dim_computes : PolyComputes dim := extractPrefix_computes
noncomputable def precision_computes : PolyComputes precision := discardPrefix_computes.comp extractPrefix_computes
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def row_computes : PolyComputes row := extractPrefix_computes.comp discardPrefix_computes
noncomputable def entryInput_computes : PolyComputes entryInput :=
  ((ctx_computes.comp shape_computes).pair row_computes).pair col_computes
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

noncomputable def dim_computes : PolyComputes dim := extractPrefix_computes
noncomputable def precision_computes : PolyComputes precision := discardPrefix_computes.comp extractPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₂_computes.comp extractPrefix_computes
noncomputable def shape_computes : PolyComputes shape := stored_computes.comp extractPrefix_computes
end BinaryEllipsoidAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList
noncomputable def loopInput_computes : PolyComputes loopInput :=
  extractPrefix_computes.pair (discardPrefix_computes.comp discardPrefix_computes)
end RationalMatrix
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

noncomputable def prepared_computes : PolyComputes prepared :=
  extractPrefix_computes.pair (boundCounter.computes.pair (discardPrefix_computes.comp discardPrefix_computes))
end BinaryEllipsoidIteration
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

noncomputable def nword_computes : PolyComputes nword := extractPrefix_computes
noncomputable def pword_computes : PolyComputes pword := rest₁_computes.comp extractPrefix_computes
noncomputable def sword_computes : PolyComputes sword := rest₂_computes.comp extractPrefix_computes
noncomputable def radius_computes : PolyComputes radius := rest₃_computes.comp extractPrefix_computes
noncomputable def twice_computes : PolyComputes twice := nword_computes.append nword_computes
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

namespace BinaryClearRow
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid PolytopeCertificate
open WordList RationalMatrix

noncomputable def entries_computes : PolyComputes entries := cons_computes discardPrefix_computes extractPrefix_computes
noncomputable def denOp_computes : PolyComputes denOp := discardPrefix_computes.comp BinaryRational.denominator_computes
end BinaryClearRow
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

noncomputable def second_computes : PolyComputes second := rest₁_computes.comp extractPrefix_computes
end BinaryRationalDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList.Set

noncomputable def target_computes : PolyComputes target :=
  (extractPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def replacement_computes : PolyComputes replacement :=
  (extractPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def oldInput_computes : PolyComputes oldInput :=
  discardPrefix_computes.pair (extractPrefix_computes.comp extractPrefix_computes)
end WordList.Set
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

noncomputable def cramerOpInput_computes : PolyComputes cramerOpInput :=
  (extractPrefix_computes.comp extractPrefix_computes).pair
    (discardPrefix_computes.pair (extractPrefix_computes.comp discardPrefix_computes))
end RationalMatrix
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

noncomputable def context_computes : PolyComputes context := extractPrefix_computes.comp extractPrefix_computes
noncomputable def row_computes : PolyComputes row := extractPrefix_computes.comp discardPrefix_computes
end MetricTable
namespace BinaryOpeningActivity
open WordList

noncomputable def table_computes : PolyComputes table :=
  (extractPrefix_computes.comp extractPrefix_computes).comp extractPrefix_computes
noncomputable def client_computes : PolyComputes client :=
  (extractPrefix_computes.comp extractPrefix_computes).comp discardPrefix_computes
noncomputable def paramV_computes : PolyComputes paramV :=
  (extractPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def paramZ_computes : PolyComputes paramZ :=
  (extractPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def list_computes (fs : List (List Bool → List Bool)) (hs : ∀ f∈fs, PolyComputes f) :
    PolyComputes (fun x=>encode (fs.map (fun f=>f x))) := by
  induction fs with
  | nil=>exact const_computes []
  | cons f fs ih=>exact cons_computes (hs f (List.mem_cons_self ..)) (ih (fun g hg=>hs g (List.mem_cons_of_mem _ hg)))
end WordList
namespace BinaryOpeningEnumeration
open WordList EffectiveOpenability RationalOpenability BinaryOpeningPayment
noncomputable def unaryTag_computes (tag : ℕ) : PolyComputes (unaryTag tag) :=
  cons_computes (const_computes tag.bits) (cons_computes id_computes (const_computes []))
noncomputable def pairTag_computes (tag : ℕ) : PolyComputes (pairTag tag) :=
  cons_computes (const_computes tag.bits)
    (cons_computes extractPrefix_computes (cons_computes discardPrefix_computes (const_computes [])))
noncomputable def tripleTag_computes (tag : ℕ) : PolyComputes (tripleTag tag) :=
  cons_computes (const_computes tag.bits)
    (cons_computes (discardPrefix_computes.comp discardPrefix_computes)
      (cons_computes extractPrefix_computes (cons_computes (discardPrefix_computes.comp extractPrefix_computes) (const_computes []))))
noncomputable def dualTag_computes : PolyComputes dualTag :=
  cons_computes (const_computes (7:ℕ).bits)
    (cons_computes discardPrefix_computes (cons_computes extractPrefix_computes (const_computes [])))
noncomputable def variableTag_computes : PolyComputes variableTag :=
  cons_computes (const_computes (1:ℕ).bits)
    (cons_computes extractPrefix_computes (cons_computes (discardPrefix_computes.comp extractPrefix_computes)
      (cons_computes (discardPrefix_computes.comp discardPrefix_computes) (const_computes []))))
end BinaryOpeningEnumeration
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

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCollect
open WordOperations WordList
variable {A : Type*}
noncomputable def invalid_computes : PolyComputes (fun x=>[invalid x]) := discardPrefix_computes.comp isEmpty_computes
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_NatWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
noncomputable def natWords_computes : PolyComputes natWords :=
  sign_computes.cond (const_computes []) (tail_computes.comp normalize_computes)
end Signed
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
noncomputable def filterItem_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (filterItem p) := by
  have h := hp.cond (cons_computes discardPrefix_computes (const_computes [])) (const_computes [])
  change PolyComputes (fun x=>if p x then encode [discardPrefix x] else [])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl
end WordList
namespace BinaryFiniteInsert
open WordList BinaryPhaseFirst EffectiveOpenability
noncomputable def old_computes : PolyComputes old := extractPrefix_computes.comp extractPrefix_computes
noncomputable def new_computes : PolyComputes new := extractPrefix_computes.comp discardPrefix_computes
noncomputable def keep (x : List Bool) : Bool :=
  if natEq (pairBits (new x,discardPrefix x)) then true else contains (pairBits (discardPrefix x,old x))
noncomputable def run : List Bool → List Bool := filterWith keep
end BinaryFiniteInsert
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

noncomputable def context_computes : PolyComputes context := extractPrefix_computes.comp extractPrefix_computes
noncomputable def oldBudget_computes : PolyComputes oldBudget := extractPrefix_computes.comp discardPrefix_computes
noncomputable def newFacility_computes : PolyComputes newFacility := discardPrefix_computes.comp extractPrefix_computes
noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteInsert.run
  (pairBits (pairBits (ctxField 1 x,newFacility x),allFacilities (context x)))
noncomputable def updatedContext (x : List Bool) : List Bool := encode [ctxField 0 x,opened x,ctxField 2 x,
  ctxField 3 x,ctxField 4 x,ctxField 5 x,ctxField 6 x,ctxField 7 x,ctxField 8 x]

noncomputable def active (x : List Bool) : Bool := BinaryOpeningPayment.active (pairBits (context (extractPrefix x),discardPrefix x))
noncomputable def budgetItem (x : List Bool) : List Bool :=
  if active x then Lookup.run (pairBits (discardPrefix x,newBudget (extractPrefix x)))
  else Lookup.run (pairBits (discardPrefix x,oldBudget (extractPrefix x)))
noncomputable def updatedBudget (x : List Bool) : List Bool :=
  mapWith budgetItem (pairBits (x,BinaryOpeningEnumeration.clients (context x)))
noncomputable def run (x : List Bool) : List Bool := pairBits (updatedContext x,updatedBudget x)
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DecisionOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
noncomputable def PolyComputes.not {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (fun x=>[!p x]) := by
  have h:=hp.cond (const_computes [false]) (const_computes [true])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases p x <;> rfl
noncomputable def PolyComputes.and {p q : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) (hq : PolyComputes (fun x=>[q x])) :
    PolyComputes (fun x=>[p x && q x]) := by
  have h:=hp.cond hq (const_computes [false])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases p x <;> rfl
noncomputable def PolyComputes.or {p q : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) (hq : PolyComputes (fun x=>[q x])) :
    PolyComputes (fun x=>[p x || q x]) := by
  have h:=hp.cond (const_computes [true]) hq
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases p x <;> rfl
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

noncomputable def reverseTest_computes {p : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) : PolyComputes (fun x=>[reverseTest p x]) :=
  (discardPrefix_computes.pair extractPrefix_computes).comp hp

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

noncomputable def levelWords_computes : PolyComputes levelWords := extractPrefix_computes
noncomputable def parentWords_computes : PolyComputes parentWords := discardPrefix_computes.comp extractPrefix_computes
noncomputable def table_computes : PolyComputes table := extractPrefix_computes.comp extractPrefix_computes
noncomputable def label_computes : PolyComputes label := extractPrefix_computes.comp discardPrefix_computes
attribute [local irreducible] MetricTable.get
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelMatrix
open WordOperations WordList RationalLeaves
attribute [local irreducible] mapWith

noncomputable def table_computes : PolyComputes table := (extractPrefix_computes.comp extractPrefix_computes).comp extractPrefix_computes
noncomputable def item_computes : PolyComputes item := extractPrefix_computes.comp discardPrefix_computes
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

namespace MetricKMedianRecovery.BitMachine.BinaryLabelSelect
open Classical
open WordOperations BinaryArithmetic WordList RationalLeaves EffectiveOpenability

noncomputable def alphabet_computes : PolyComputes alphabet := extractPrefix_computes.comp extractPrefix_computes
noncomputable def target_computes : PolyComputes target := extractPrefix_computes.comp discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryLabelSelect

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
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def lengthBits : List Bool → List Bool := UnaryResources.lengthBits ∘ Count.run
end WordList
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

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordOperations WordList BinaryArithmetic
noncomputable def contains : List Bool→Bool := BinaryPhaseFirst.contains
noncomputable def absent (x : List Bool) : Bool := !contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def diff (x : List Bool) : List Bool := sort (filterWith absent (pairBits (discardPrefix x,extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryNatSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawTake
open WordOperations BinaryArithmetic
noncomputable def number (x : List Bool) : List Bool :=
  (value (UnaryResources.lengthBits (discardPrefix x))-value (extractPrefix x)).bits
noncomputable def run (x : List Bool) : List Bool :=
  (RawDrop.run (pairBits (number x,(discardPrefix x).reverse))).reverse
attribute [local irreducible] number RawDrop.run
end MetricKMedianRecovery.BitMachine.RawTake

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
open WordOperations
variable {A : Type*}
noncomputable def addLast_computes : PolyComputes addLast :=
  discardPrefix_computes.append (cons_computes extractPrefix_computes (const_computes []))
noncomputable def cap (d : ℕ) : PolynomialCounter ((Polynomial.X+1)^d) := PolynomialCounter.choose _
noncomputable def run (d : ℕ) (x : List Bool) : List Bool :=
  CappedFold.run op (pairBits ((cap d).word x,Fold.pack (discardPrefix x) [] (encode [[]])))
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
open WordOperations WordList
variable {n : ℕ}
noncomputable def run (d : ℕ) : List Bool→List Bool := Subsets.run d
noncomputable def blocks (d : ℕ) (x : List Bool) : List Bool := filterWith nonemptyKey (pairBits ([],run d x))
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

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def old (x : List Bool) : List Bool := BinaryBlueLookup.run
  (pairBits (BinaryNatSet.diff (pairBits (whole x,discardPrefix x)),field 3 (ctx x)))
noncomputable def op (x : List Bool) : List Bool := BinaryBlueMerge.run (pairBits (block x,old x))
noncomputable def run (x : List Bool) : List Bool := BinaryBlueChoice.select
  (mapWith op (pairBits (x,BinaryBlueStates.blocks 3 x)))
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
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def row (x : List Bool) : List Bool := pairBits (discardPrefix x,BinaryBlueCell.run x)
noncomputable def next (x : List Bool) : List Bool := mapWith row (pairBits (x,field 2 x))
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
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def newTable (x : List Bool) : List Bool := BinaryBlueTable.next (nextCtx x)
noncomputable def newBest (x : List Bool) : List Bool := BinaryBlueChoice.run
  (pairBits (oldBest x,BinaryBlueLookup.run (pairBits (field 3 (extractPrefix x),newTable x))))
noncomputable def step (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (newTable x,newBest x))
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose _
noncomputable def loop (x : List Bool) : List Bool := BoundedIteration.run step
  (pairBits (field 4 x,pairBits (cap.word x,initial x)))
noncomputable def run (x : List Bool) : List Bool := if field 3 x=[] then BinaryBlueChoice.encode id (some (0,[])) else oldBest (loop x)
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
noncomputable def states (d : ℕ) (x : List Bool) : List Bool := BinaryBlueStates.run d (pairBits (x,field 2 x))
noncomputable def prepare (d : ℕ) (x : List Bool) : List Bool := encode [field 0 x,field 1 x,states d x,field 2 x,field 3 x]
noncomputable def run (d : ℕ) : List Bool→List Bool := BinaryBlueLoop.run ∘ prepare d
end MetricKMedianRecovery.BitMachine.BinaryBlueProgram

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
noncomputable def entry (x : List Bool) : List Bool :=
  if BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x)) then discardPrefix x
  else head (extractPrefix x)
noncomputable def row (x : List Bool) : List Bool := mapWith entry (pairBits (ball x,columns x))
attribute [local irreducible] mapWith flatMapWith
noncomputable def locations (x : List Bool) : List Bool := flatMapWith row (pairBits (x,indices x))
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

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
noncomputable def remaining (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (field 3 x,extractPrefix (field 5 x)))
attribute [local irreducible] remaining
noncomputable def context (x : List Bool) : List Bool := encode [lengthBits (field 0 x),field 4 x,remaining x,discardPrefix (field 5 x)]
attribute [local irreducible] context
noncomputable def oracle (x : List Bool) : List Bool := encode [field 0 x,field 1 x,context x]
attribute [local irreducible] oracle
noncomputable def classOf (j : ℕ) (x : List Bool) : List Bool := BinaryClassFilter.run
  (pairBits (pairBits (field 6 x,j.bits),remaining x))
attribute [local irreducible] classOf
noncomputable def greenContext (x : List Bool) : List Bool := encode [lengthBits (field 0 x),field 4 x,classOf 0 x,discardPrefix (field 5 x)]
attribute [local irreducible] greenContext
noncomputable def greenOracle (x : List Bool) : List Bool := encode [field 0 x,field 1 x,greenContext x]
attribute [local irreducible] greenOracle
attribute [local irreducible] ballInput
attribute [local irreducible] copyData
attribute [local irreducible] parts
attribute [local irreducible] origins
noncomputable def locations (x : List Bool) : List Bool := BinaryCopyTables.locations (copyData x)
attribute [local irreducible] locations
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def runCap : PolynomialCounter runCapPoly := PolynomialCounter.choose _
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def blueInput (x : List Bool) : List Bool := encode [oracle x,classOf 2 x,field 7 x]
attribute [local irreducible] blueInput
noncomputable def records (x : List Bool) : List Bool := BinaryBlueRecords.run (blueInput x)
attribute [local irreducible] records
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

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
noncomputable def outside (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (extractPrefix (field 5 x),field 3 x))
noncomputable def lhs (x : List Bool) : List Bool := (value (lengthBits (discardPrefix (field 5 x)))+(field 10 x).length).bits
noncomputable def rhs (x : List Bool) : List Bool :=
  (value (lengthBits (extractPrefix (field 5 x)))+value (field 9 x)+value (lengthBits (field 8 x))).bits
noncomputable def run (x : List Bool) : Bool :=
  decide (outside x=[] ∧ badBalls x=[] ∧ badRadii x=[] ∧ value (field 9 x)≤value (lengthBits (classOf 1 x)) ∧ value (lhs x)≤value (rhs x))
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ActionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryActions
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open RationalSampling
variable {n : ℕ}
attribute [local irreducible] RawTake.run
noncomputable def entry (k : ℕ) (x : List Bool) : List Bool :=
  pairBits (k.bits,RawTake.run (pairBits (discardPrefix x,extractPrefix x)))
noncomputable def block (k : ℕ) (x : List Bool) : List Bool :=
  mapWith (entry k) (pairBits (x,BinaryEllipsoidInitial.indices x))
noncomputable def menus (x : List Bool) : List Bool :=
  block 0 (field 0 x)++block 1 (field 1 x++[true])++block 2 (field 2 x)
noncomputable def run (x : List Bool) : List Bool := encode [encode [(0:ℕ).bits,[],[]]]++
  mapWith delete (pairBits ([],extractPrefix x))++crossWith add (pairBits (extractPrefix x,menus (discardPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryActions

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
noncomputable def num_computes : PolyComputes num := discardPrefix_computes.comp extractPrefix_computes
noncomputable def capacity : PolynomialCounter (10*Polynomial.X+20) := PolynomialCounter.choose _
noncomputable def runInput (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (capacity.word x,initial x))
noncomputable def runInput_computes : PolyComputes runInput := extractPrefix_computes.pair (capacity.computes.pair initial_computes)
noncomputable def stateRun (query : List Bool→List Bool) : List Bool→List Bool := BoundedIteration.run (step query) ∘ runInput
noncomputable def run (query : List Bool→List Bool) : List Bool→List Bool := finish ∘ stateRun query
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
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def predWords_computes : PolyComputes predWords := by
  change PolyComputes (fun x=>(value x-1).bits)
  simpa only [value_bits,id_eq] using NatOps.sub id_computes (const_computes (1:ℕ).bits)
noncomputable def run (query : List Bool→List Bool) : List Bool→List Bool := BinaryGrid.run query ∘ input
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

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels )

noncomputable def capacity : PolynomialCounter capacityPoly := PolynomialCounter.choose capacityPoly
end MetricKMedianRecovery.BitMachine.BinaryDelete

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
noncomputable def countInter : List Bool → List Bool := lengthBits ∘ inter
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end


