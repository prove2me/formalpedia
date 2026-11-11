-- Prove2me | Definitions.Def_Q238K042
-- name    : Q238K042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:42:38.33281+00:00
-- url     : https://prove2.me/theorems/0099b556-865a-49e6-bd2c-bb8a451ed72f
-- title:
--   Definitions bundle Q238K042 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 59 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.pword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.aword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.bword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.cut_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.dimensions_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.leftShape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.lword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.qword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.rightShape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.right_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.runInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.tword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.anext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.bword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.factor_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.lbits_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.lword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.qnext_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.tbits_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.tword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.unary_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choices_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.labelOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.clientValues_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.redValues_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.options_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.pick_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.test_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.fillInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redValues_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.ball_computes` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_RationalBest`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Sampling_SeedTensor`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K039` and `Q238K040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K048`, `Q238K049` and `Q238K050`; the statements `OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_base_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteMachine_continuation_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLengthSearch_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_iterate_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_step_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryScan_run_pack_s238`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_base_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteMachine_continuation_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLengthSearch_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_iterate_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_step_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryScan_run_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K039
import Definitions.Def_Q238K040

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalBest
open WordOperations WordList BinaryArithmetic
noncomputable def choose_computes {score : List Bool→List Bool} (hs : PolyComputes score) : PolyComputes (choose score) := by
  have h := (RatOps.lt (RatOps.ofWords ((Find.context_computes.pair Fold.accum_computes).comp hs))
    (RatOps.ofWords ((Find.context_computes.pair Find.item_computes).comp hs))).cond Find.item_computes Fold.accum_computes
  unfold choose
  simpa only [decide_eq_true_eq,Function.comp_def] using h
noncomputable def run_computes {score : List Bool→List Bool} (hs : PolyComputes score) : PolyComputes (run score) :=
  (id_computes.pair (Fold.pack_computes (discardPrefix_computes.comp discardPrefix_computes) extractPrefix_computes
    (discardPrefix_computes.comp extractPrefix_computes))).comp (CappedFold.run_computes (choose_computes hs))
noncomputable def fromList_computes {score : List Bool→List Bool} (hs : PolyComputes score) : PolyComputes (fromList score) :=
  (extractPrefix_computes.pair ((discardPrefix_computes.comp WordList.head_computes).pair
    (discardPrefix_computes.comp WordList.tail_computes))).comp (run_computes hs)
end MetricKMedianRecovery.BitMachine.BinaryRationalBest

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
noncomputable def choose_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (choose g) :=
  (extractPrefix_computes.pair bagWords_computes).comp (BinaryRationalBest.fromList_computes (score_computes hg))
attribute [local irreducible] mapWith
noncomputable def choices_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (choices g) := by
  unfold choices
  exact (id_computes.pair ((field_computes 1).comp Indices.run_computes)).comp (mapWith_computes (choose_computes hg))
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
attribute [local irreducible] advance choices
noncomputable def nextTable_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (nextTable g) := by
  unfold nextTable
  exact (cons_computes (Fold.accum_computes.comp (field_computes 1))
    (cons_computes (stepScore_computes.comp (choices_computes hg))
      (cons_computes (Fold.accum_computes.comp (field_computes 0)) (const_computes [])))).comp advance_computes
noncomputable def step_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (step g) := by
  have hn := NatOps.add (Fold.accum_computes.comp (field_computes 0)) (const_computes (1:ℕ).bits)
  have hu := cons_computes hn (cons_computes (nextTable_computes hg) (const_computes []))
  have he := (NatOps.lt (Fold.accum_computes.comp (field_computes 0))
    ((Find.context_computes.comp (field_computes 2)).comp UnaryResources.lengthBits_computes)).cond hu Fold.accum_computes
  unfold step
  simpa only [Function.comp_def,value_bits,UnaryResources.lengthBits_eq,decide_eq_true_eq,encode] using he
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
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
noncomputable def run_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (run g) :=
  (runCap.computes.pair (Fold.pack_computes (field_computes 4) context_computes initial_computes)).comp
    (CappedFold.run_computes (step_computes hg))
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
namespace Drop
open Lookup (step step_computes iterate_bounds step_zero step_succ)
noncomputable def run_computes : PolyComputes run := by
  have hi := BoundedIteration.polynomialRun_computes step_computes Polynomial.X (4*Polynomial.X+1)
  have hh := hi.comp discardPrefix_computes
  have he (x : List Bool) : BoundedIteration.polynomialRun step Polynomial.X (4*Polynomial.X+1) x=
      step^[x.length] x := by
    have ht := BoundedIteration.polynomialRun_eq step Polynomial.X (4*Polynomial.X+1) x (by
      intro j _
      have hb := (iterate_bounds x j).2.2
      obtain ⟨hf,hr⟩ := ProductBits.projections_length x
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
        Polynomial.eval_one]
      omega)
    simpa only [Polynomial.eval_X] using ht
  change PolyComputes (fun x=>discardPrefix (step^[x.length] x))
  simpa only [Function.comp_def,he] using hh
end Drop
end WordList
end MetricKMedianRecovery.BitMachine

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
noncomputable def product_computes (d : ℕ) : PolyComputes (product d) := by
  induction d with
  | zero=>exact const_computes _
  | succ d ih=>exact NatOps.mul (WordList.head_computes.comp UnaryResources.lengthBits_computes) (WordList.tail_computes.comp ih)
noncomputable def width_computes (d : ℕ) : PolyComputes (width d) :=
  ((extractPrefix_computes.comp extractPrefix_computes).comp WordList.tail_computes).comp (product_computes _)
attribute [local irreducible] width RawTake.run RawDrop.run
noncomputable def chunk_computes (d : ℕ) : PolyComputes (chunk d) :=
  ((width_computes d).pair (((NatOps.mul (width_computes d) discardPrefix_computes).pair
    (extractPrefix_computes.comp discardPrefix_computes)).comp RawDrop.run_computes)).comp RawTake.run_computes
noncomputable def child_computes (d : ℕ) : PolyComputes (child d) :=
  ((extractPrefix_computes.comp extractPrefix_computes).comp WordList.tail_computes).pair (chunk_computes d)
noncomputable def indices_computes : PolyComputes indices :=
  (extractPrefix_computes.comp WordList.head_computes).comp BinaryEllipsoidInitial.indices_computes
noncomputable def nest_computes (d : ℕ) : PolyComputes (nest d) := by
  induction d with
  | zero=>exact discardPrefix_computes.comp normalizeBig_computes
  | succ dimension inductionHypothesis=>
    change PolyComputes (fun input=>mapWith (fun word=>nest dimension (child dimension word))
      (pairBits (input,indices input)))
    simpa only [Function.comp_def,id_eq] using
      (id_computes.pair indices_computes).comp
        (mapWith_computes ((child_computes dimension).comp inductionHypothesis))
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
noncomputable def output_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (output g) :=
  (cons_computes ((extractPrefix_computes.comp (run_computes hg)).comp (field_computes 1))
    (cons_computes discardPrefix_computes (cons_computes
      ((extractPrefix_computes.comp (field_computes 2)).comp UnaryResources.lengthBits_computes)
      (const_computes [])))).comp draw_computes
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources
open WordOperations WordList BinaryArithmetic
open Categorical.Explicit

noncomputable def bword_computes : PolyComputes bword :=
  ((UnaryResources.copy_computes (const_computes [true,true])
    (((discardPrefix_computes.comp UnaryResources.lengthBits_computes).comp UnaryResources.inc_computes).comp RawUnary.run_computes)).append (const_computes _))
noncomputable def tbits_computes : PolyComputes tbits :=
  (bword_computes.pair (const_computes _)).comp NaturalArray.exponentiate_computes
attribute [local irreducible] bword tbits RawTake.run RawUnary.run NaturalArray.exponentiate
noncomputable def qnext_computes : PolyComputes qnext := (extractPrefix_computes.comp UnaryResources.lengthBits_computes).comp UnaryResources.inc_computes
noncomputable def anext_computes : PolyComputes anext := (discardPrefix_computes.comp UnaryResources.lengthBits_computes).comp UnaryResources.inc_computes
attribute [local irreducible] qnext anext
noncomputable def factor_computes : PolyComputes factor := by
  unfold factor
  have hh:=NatOps.mul (NatOps.mul (const_computes (1000000000:ℕ).bits) tbits_computes) qnext_computes
  simpa only [value_bits] using hh
attribute [local irreducible] factor
noncomputable def lbits_computes : PolyComputes lbits := by
  unfold lbits
  have hh:=NatOps.mul factor_computes (NatOps.mul anext_computes anext_computes)
  simpa only [value_bits,pow_two] using hh
attribute [local irreducible] cap
noncomputable def unary_computes {w : List Bool→List Bool} (hw : PolyComputes w) : PolyComputes (unary w) :=
  ((hw.pair cap.computes).comp RawTake.run_computes).comp RawUnary.run_computes
noncomputable def tword_computes : PolyComputes tword := unary_computes tbits_computes
noncomputable def lword_computes : PolyComputes lword := unary_computes lbits_computes
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources

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

noncomputable def ranked_computes : PolyComputes ranked := by
  have computation := ((const_computes []).pair ((Indices.run_computes.pair id_computes).comp Zip.run_computes)).comp
    (mapWith_computes ((discardPrefix_computes.comp discardPrefix_computes).pair (discardPrefix_computes.comp extractPrefix_computes)))
  unfold ranked
  simpa only [Function.comp_def, id_eq] using computation
attribute [local irreducible] sort ranked Take.run
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

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
open BinaryOpeningPayment (field field_computes field_encode)
open Categorical.Explicit
variable {q a : ℕ}
noncomputable def qword_computes : PolyComputes qword := (extractPrefix_computes.comp (field_computes 1)).comp Count.run_computes
noncomputable def aword_computes : PolyComputes aword := extractPrefix_computes.comp (field_computes 2)
noncomputable def dimensions_computes : PolyComputes dimensions := qword_computes.pair aword_computes
attribute [local irreducible] Resources.tword Resources.lword Resources.bword dimensions
noncomputable def tword_computes : PolyComputes tword := dimensions_computes.comp Resources.tword_computes
noncomputable def lword_computes : PolyComputes lword := dimensions_computes.comp Resources.lword_computes
noncomputable def bword_computes : PolyComputes bword := dimensions_computes.comp Resources.bword_computes
noncomputable def leftShape_computes : PolyComputes leftShape := cons_computes tword_computes
  (cons_computes qword_computes (cons_computes lword_computes (cons_computes aword_computes (cons_computes bword_computes (const_computes [])))))
noncomputable def rightShape_computes : PolyComputes rightShape := cons_computes aword_computes (cons_computes bword_computes (const_computes []))
attribute [local irreducible] BinarySeed.product leftShape
noncomputable def cut_computes : PolyComputes cut := leftShape_computes.comp (BinarySeed.product_computes 5)
attribute [local irreducible] BinarySeed.nest RawTake.run RawDrop.run cut rightShape tword lword bword
noncomputable def left_computes : PolyComputes left :=
  (leftShape_computes.pair ((cut_computes.pair discardPrefix_computes).comp RawTake.run_computes)).comp (BinarySeed.nest_computes 4)
noncomputable def right_computes : PolyComputes right :=
  (rightShape_computes.pair ((cut_computes.pair discardPrefix_computes).comp RawDrop.run_computes)).comp (BinarySeed.nest_computes 1)
noncomputable def runInput_computes : PolyComputes runInput := cons_computes (extractPrefix_computes.comp (field_computes 0))
  (cons_computes (extractPrefix_computes.comp (field_computes 1)) (cons_computes aword_computes (cons_computes tword_computes (cons_computes left_computes (const_computes [])))))
noncomputable def run_computes : PolyComputes run := runInput_computes.pair right_computes
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a : ℕ}
noncomputable def test_computes : PolyComputes (fun x=>[test x]) :=
  NatOps.eq (((discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes))
    (extractPrefix_computes.comp (field_computes 1))
noncomputable def options_computes : PolyComputes options :=
  ((cons_computes (extractPrefix_computes.comp (field_computes 0)) (cons_computes discardPrefix_computes (const_computes []))).pair
    (extractPrefix_computes.comp (field_computes 2))).comp (filterWith_computes test_computes)
attribute [local irreducible] options
noncomputable def pick_computes : PolyComputes pick := by
  have h := (options_computes.comp isEmpty_computes).cond
    ((discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 1))).comp Lookup.run_computes)
    (options_computes.comp WordList.head_computes)
  unfold pick
  simpa only [decide_eq_true_eq,Function.comp_def] using h
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,id_eq] using
    (id_computes.pair ((field_computes 1).comp Indices.run_computes)).comp (mapWith_computes pick_computes)
end MetricKMedianRecovery.BitMachine.BinaryCompletionFill

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIndexMap
open WordOperations WordList
noncomputable def item_computes : PolyComputes item := (discardPrefix_computes.pair extractPrefix_computes).comp Lookup.run_computes
noncomputable def run_computes : PolyComputes run := mapWith_computes item_computes
end MetricKMedianRecovery.BitMachine.BinaryIndexMap

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryColorLabel
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] WordList.mapWith
noncomputable def labelOp_computes : PolyComputes labelOp := NatOps.mod discardPrefix_computes extractPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryColorLabel

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {q p r : ℕ}
noncomputable def clientValues_computes : PolyComputes clientValues := by
  have clientValuesComputes :=
    (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 1))).comp (mapWith_computes cap_computes)
  unfold clientValues
  simpa only [Function.comp_def] using clientValuesComputes
noncomputable def redValues_computes : PolyComputes redValues := by
  have redValuesComputes :=
    (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp (mapWith_computes weightedCap_computes)
  unfold redValues
  simpa only [Function.comp_def] using redValuesComputes
end MetricKMedianRecovery.BitMachine.BinaryCompletion

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {n q a p r b : ℕ}
noncomputable def fillInput_computes : PolyComputes fillInput :=
  cons_computes (field_computes 3) (cons_computes (field_computes 4) (cons_computes (field_computes 9) (const_computes [])))
attribute [local irreducible] fillInput BinaryCompletionFill.run BinaryFinSet.image
noncomputable def redValues_computes : PolyComputes redValues := by
  have redValuesComputes :=
    ((field_computes 10).pair (field_computes 9)).comp BinaryCompletion.redValues_computes
  unfold redValues
  simpa only [Function.comp_def] using redValuesComputes
attribute [local irreducible] redValues BinaryNatSet.sort BinaryRationalSort.rawIndices
attribute [local irreducible] redIndices
attribute [local irreducible] red blue dest BinaryNatSet.union
attribute [local irreducible] removed BinaryNatSet.diff
attribute [local irreducible] filled
attribute [local irreducible] remain added
attribute [local irreducible] core
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {n a : ℕ}
noncomputable def ball_computes : PolyComputes ball :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 1))).comp Lookup.run_computes
noncomputable def columns_computes : PolyComputes columns :=
  ((extractPrefix_computes.comp (field_computes 0)).comp BinaryEllipsoidInitial.indices_computes)
attribute [local irreducible] mapWith flatMapWith
noncomputable def indices_computes : PolyComputes indices := ((field_computes 1).comp Count.run_computes).comp BinaryEllipsoidInitial.indices_computes
noncomputable def partRow_computes : PolyComputes partRow := by
  unfold partRow
  exact (discardPrefix_computes.pair columns_computes).comp (mapWith_computes extractPrefix_computes)
noncomputable def parts_computes : PolyComputes parts := by
  unfold parts
  exact (id_computes.pair indices_computes).comp (flatMapWith_computes partRow_computes)
noncomputable def origin_computes : PolyComputes origin := by
  unfold origin
  simpa only [Function.comp_def,UnaryResources.lengthBits_eq,value_bits] using NatOps.add
    (NatOps.mul (((extractPrefix_computes.comp (field_computes 0)).comp UnaryResources.lengthBits_computes)) discardPrefix_computes)
    (ball_computes.comp WordList.head_computes)

noncomputable def origins_computes : PolyComputes origins := by
  unfold origins
  exact (id_computes.pair indices_computes).comp (mapWith_computes origin_computes)
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Categorical.Explicit
variable {n q a p r c : ℕ}
noncomputable def context_computes : PolyComputes context :=
  cons_computes (extractPrefix_computes.comp (field_computes 10))
    (cons_computes (extractPrefix_computes.comp (field_computes 3))
      (cons_computes ((extractPrefix_computes.comp (field_computes 4)).comp Count.run_computes) (const_computes [])))
attribute [local irreducible] prepared
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

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
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCategorical
noncomputable def pword_computes : PolyComputes pword := ((field_computes 5).comp discardPrefix_computes).comp Count.run_computes
attribute [local irreducible] dimensions Resources.tword Resources.lword Resources.bword BinarySeed.product
attribute [local irreducible] leftShape rightShape BinaryBranchRandomize.csize BinaryBranchRandomize.lsize
attribute [local irreducible] run RawTake.run
end MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count

end OAI
end


