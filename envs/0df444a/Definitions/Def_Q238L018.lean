-- Prove2me | Definitions.Def_Q238L018
-- name    : Q238L018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:23:49.972685+00:00
-- url     : https://prove2.me/theorems/b18764fa-ba97-43ef-a119-d42b2131b5f5
-- title:
--   Definitions bundle Q238L018 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 116 declarations of OpenAI's Lean: 104 definitions and 12 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueOutput.query`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueRecords.tag`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchBalls.input`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchBalls.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBall`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badRadius`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.ballInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.cshape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.nword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.oracleInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.dimensions`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.pword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.qword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Seed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.completionCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.layout`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.aword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.dimensions`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.qword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagTest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawPick`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawRow`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elementPart`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elementSamples`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.initial`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stepScore`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClassFilter.tag`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.colorWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.labelOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.look`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.offers`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.test`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.fillInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.ball`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.columns`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.indices` and 64 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueDPValue`, `KMedianRecovery_Branching_BlueItem`, `KMedianRecovery_Branching_BluePlan`, `KMedianRecovery_Branching_BlueProgram`, `KMedianRecovery_Branching_BranchBalls`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchObjective`, `KMedianRecovery_Branching_BranchPhysical`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Branching_FavorableReady`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_RationalBest`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Machines_CoupledPrimitives`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LoopMachine`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Machines_StartResources`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_ClassFilter`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SeedTensor`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L006`, `Q238L007`, `Q238L008` and `Q238L009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L024`, `Q238L025` and `Q238L026`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L006
import Definitions.Def_Q238L007
import Definitions.Def_Q238L008
import Definitions.Def_Q238L009

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueDPValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A L : Type*}
lemma value_collect (xs : List (Candidate (List A))) : value (collect xs)=(xs.map value).sum := by
  induction xs with
  | nil=>simp [collect,value]
  | cons x xs ih=>simpa only [collect,List.foldr_cons,value_merge,List.map_cons,List.sum_cons] using congrArg (value x+·) ih

variable [LinearOrder L]
lemma recurrence_value (C : Finset L→Candidate (List A)) (t : ℕ) (U : Finset L) :
    value (recurrence C t U)=BlueSubsetDP.value (fun V=>value (C V)) t U := by
  induction t generalizing U with
  | zero=>by_cases h : U=∅ <;> simp [recurrence,BlueSubsetDP.value,h,value]
  | succ t ih=>
    rw [recurrence,select_finset,enumBlocks_set]
    simp only [value_merge,ih,BlueSubsetDP.value]
lemma best_value (C : Finset L→Candidate (List A)) (c : ℕ) (U : Finset L) :
    value (best C c U)=BlueSubsetDP.best (fun V=>value (C V)) c U := by
  by_cases h : U=∅
  · simp [best,BlueSubsetDP.best,h,value]
  · rw [best,ite_eq_right h,BlueSubsetDP.best,ite_eq_right h]
    have he : ((List.range c).map (fun t=>recurrence C (t+1) U))=
      (((List.range c).map (·+1)).map (fun t=>recurrence C t U)) := by simp
    rw [he,select_finset,range_succ_set]
    simp only [recurrence_value]
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
omit [LinearOrder Y] in
lemma item_value (B : Finset R) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y) :
    value (item B label q l y)=(B.filter (label ·=l)).inf (fun r=>((q r y:ℝ):WithTop ℝ)) := by
  rw [item,select_finset,Finset.sort_toFinset]
  rfl
omit [LinearOrder Y] in
lemma blockAt_value (B : Finset R) (label : R→L) (q : R→Y→ℚ) (U : Finset L) (y : Y) :
    value (blockAt B label q U y)=∑ l∈U,(B.filter (label ·=l)).inf (fun r=>((q r y:ℝ):WithTop ℝ)) := by
  rw [blockAt,value_collect,List.map_map]
  simp only [Function.comp_def,item_value]
  rw [←List.sum_toFinset _ (Finset.sort_nodup U (·≤·)),Finset.sort_toFinset]
lemma block_value (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L) :
    value (block B F label q U)=BlueSubsetDP.blockCost B F label (fun r y=>(q r y:ℝ)) U := by
  rw [block,select_finset,Finset.sort_toFinset]
  simp only [blockAt_value,BlueSubsetDP.blockCost]
lemma optimizer_value (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ) (U : Finset L) :
    value (best (block B F label q) c U)=BlueSubsetDP.best (BlueSubsetDP.blockCost B F label (fun r y=>(q r y:ℝ))) c U := by
  rw [best_value]
  simp only [block_value]
end MetricKMedianRecovery.BlueDP

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
open EffectiveOpenability RationalPhase BinaryOpeningPayment

def paramV (x : List Bool) : ℚ := BinaryRational.decode (sf 2 x)
def paramZ (x : List Bool) : ℚ := BinaryRational.decode (sf 3 x)
def phase (x : List Bool) : ℚ := (1+paramV x*paramV x)*paramZ x
def query (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),discardPrefix x)
noncomputable def context (x : List Bool) : List Bool := encode [sf 0 x,sf 1 x,sf 2 x,BinaryRational.encode (phase x),
  sf 4 x,sf 5 x,sf 6 x,sf 7 x,sf 8 x]
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

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
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryOpeningPayment
attribute [local irreducible] WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run 
noncomputable def powerInput (x : List Bool) : List Bool := pairBits
  (encode [[],[],x,BinaryRational.encode 1,BinaryRational.encode 0,BinaryRational.encode 0,[],[],[]],[])
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

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

noncomputable def data : List Bool → List Bool := discardPrefix ∘ discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

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
open Lookup (step )
def run (x : List Bool) : List Bool := discardPrefix (step^[x.length] x)
end Drop
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryOpeningPayment (field )
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
def jf (n : ℕ) : List Bool → List Bool := field n ∘ discardPrefix
noncomputable def tagIs (n : ℕ) (x : List Bool) : Bool := decide (value (jf 0 x)=n)

end MetricKMedianRecovery.BitMachine.BinaryJump

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
open WordOperations WordList
variable {m n : ℕ}
def table (f : Fin m→Fin n) : List Bool := WordList.encode (List.ofFn (fun i=>(f i).val.bits))
end MetricKMedianRecovery.BitMachine.BinaryFinSet

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
noncomputable def indices (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (head (extractPrefix x))
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

namespace MetricKMedianRecovery.BitMachine.BinaryColorLabel
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] WordList.mapWith
noncomputable def colorWord (x : List Bool) : List Bool :=
  if value x<2 then (0:ℕ).bits else if value x=2 then (1:ℕ).bits else (2:ℕ).bits
noncomputable def labelOp (x : List Bool) : List Bool := (value (discardPrefix x)%value (extractPrefix x)).bits
end MetricKMedianRecovery.BitMachine.BinaryColorLabel

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
noncomputable def tag (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,field 2 (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryBlueRecords

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BluePlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
lemma recurrence_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (t : ℕ) (U : Finset L) :
    Spec B F label q U t (recurrence (block B F label q) t U) := by
  induction t generalizing U with
  | zero=>
    rw [recurrence]
    split_ifs with h
    · subst U;exact empty_spec B F label q 0
    · trivial
  | succ t ih=>
    rw [recurrence]
    apply select_spec _ _ trivial
    intro x hx
    obtain ⟨V,hV,rfl⟩:=List.mem_map.mp hx
    have hVU := (BlueSubsetDP.mem_blocks.mp (enumBlocks_set U ▸ List.mem_toFinset.mpr hV)).2
    have hd : Disjoint V (U\V) := by
      apply Finset.disjoint_left.mpr
      intro l hl hrest
      exact (Finset.mem_sdiff.mp hrest).2 hl
    have hu : V∪(U\V)=U := by
      ext l
      simp only [Finset.mem_union,Finset.mem_sdiff]
      exact ⟨fun h=>h.elim (hVU ·) And.left,fun h=>by by_cases hV : l∈V;exact Or.inl hV;exact Or.inr ⟨h,hV⟩⟩
    have hh:=merge_spec B F label q V (U\V) 1 t _ _ (block_spec B F label q V) (ih (U\V)) hd
    simpa only [hu,Nat.add_comm 1] using hh
lemma best_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ) (U : Finset L) :
    Spec B F label q U c (best (block B F label q) c U) := by
  unfold best
  split_ifs with h
  · subst U;exact empty_spec B F label q c
  · apply select_spec _ _ trivial
    intro x hx
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hx
    exact spec_mono B F label q U (t+1) c (by have hh:=List.mem_range.mp ht;omega) _
      (recurrence_spec B F label q (t+1) U)
omit [LinearOrder R] [LinearOrder Y] in
lemma pick_mem (r0 : R) (y0 : Y) (xs : List (Atom L R Y)) (l : L) (hl : l∈(labels xs).toFinset) :
    pick r0 y0 xs l∈xs ∧ (pick r0 y0 xs l).1=l := by
  obtain ⟨a,ha,hal⟩:=List.mem_map.mp (List.mem_toFinset.mp hl)
  have hn : xs.find? (fun a=>a.1=l)≠none := by
    intro he
    exact List.find?_eq_none.mp he a ha (decide_eq_true hal)
  obtain ⟨b,hb⟩:=Option.ne_none_iff_exists'.mp hn
  simp only [pick,hb,Option.getD_some]
  exact ⟨List.mem_of_find?_eq_some hb,of_decide_eq_true (List.find?_some (p := fun a : Atom L R Y => decide (a.1=l)) hb)⟩
omit [LinearOrder R] [LinearOrder Y] in
lemma pick_eq (r0 : R) (y0 : Y) (xs : List (Atom L R Y)) (hn : (labels xs).Nodup)
    (a : Atom L R Y) (ha : a∈xs) : pick r0 y0 xs a.1=a := by
  have hp:=pick_mem r0 y0 xs a.1 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩))
  exact List.inj_on_of_nodup_map hn hp.1 ha hp.2
omit [LinearOrder R] [LinearOrder Y] in
lemma cost_pick (r0 : R) (y0 : Y) (q : R→Y→ℚ) (xs : List (Atom L R Y)) (U : Finset L) (h : Route U xs) :
    (∑ l∈U,q (pick r0 y0 xs l).2.1 (pick r0 y0 xs l).2.2)=cost q xs := by
  rw [←h.2,List.sum_toFinset _ h.1]
  simp only [labels,List.map_map,Function.comp_def,cost]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [pick_eq r0 y0 xs h.1 a ha]
variable [Fintype L]
noncomputable def makePlan (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ)
    (r0 : R) (y0 : Y) (k : ℚ) (xs : List (Atom L R Y))
    (h : best (block B F label q) c Finset.univ=some (k,xs)) : BlueSubsetDP.Plan B F label (fun r y=>(q r y:ℝ)) c := by
  have hs:=best_spec B F label q c Finset.univ
  rw [h] at hs
  let sel : L→R := fun l=>(pick r0 y0 xs l).2.1
  let dst : L→Y := fun l=>(pick r0 y0 xs l).2.2
  have hp (l : L) := pick_mem r0 y0 xs l (hs.1.2 ▸ Finset.mem_univ l)
  have hv (l : L) : sel l∈B ∧ label (sel l)=l ∧ dst l∈F := by
    have hh:=hs.2.1 _ (hp l).1
    exact ⟨hh.1,hh.2.1.trans (hp l).2,hh.2.2⟩
  refine ⟨sel,dst,hv,?_,?_,?_⟩
  · intro l m he
    exact (hv l).2.1.symm.trans ((congrArg label he).trans (hv m).2.1)
  · apply (Finset.card_le_card ?_).trans hs.2.2.1
    intro y hy
    obtain ⟨l,_,rfl⟩:=Finset.mem_image.mp hy
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,(hp l).1,rfl⟩)
  · have hk : (∑ l,q (sel l) (dst l))=k := by
      simpa only [sel,dst] using (cost_pick r0 y0 q xs Finset.univ hs.1).trans hs.2.2.2.symm
    have hh:=optimizer_value B F label q c Finset.univ
    rw [h] at hh
    rw [←hh]
    change (((∑ l,(q (sel l) (dst l):ℝ)):ℝ):WithTop ℝ)=((k:ℝ):WithTop ℝ)
    rw [←Rat.cast_sum,hk]
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueOutput
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {m n r : ℕ}

noncomputable def query (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
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
open WordOperations WordList BinaryArithmetic
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
open WordOperations WordList BinaryArithmetic
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
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n a : ℕ}
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
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def tag (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix (extractPrefix x)))
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
noncomputable def ballInput (x : List Bool) : List Bool := encode [field 0 x,field 2 x,discardPrefix (field 5 x)]
attribute [local irreducible] ballInput
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

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
noncomputable def drawRow (x : List Bool) : List Bool :=
  Lookup.run (pairBits (extractPrefix (discardPrefix x),field 0 (extractPrefix x)))
noncomputable def drawPick (x : List Bool) : List Bool :=
  if value (extractPrefix (discardPrefix x))=value (field 2 (extractPrefix x)) then []
  else Lookup.run (pairBits (discardPrefix (discardPrefix x),drawRow x))
attribute [local irreducible] mapWith
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
noncomputable def elementPart (x : List Bool) : List Bool :=
  Lookup.run (pairBits (discardPrefix x,field 3 (extractPrefix x)))
noncomputable def elementSamples (x : List Bool) : List Bool :=
  Lookup.run (pairBits (discardPrefix x,field 2 (extractPrefix x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
noncomputable def choose (score : List Bool→List Bool) (x : List Bool) : List Bool :=
  if BinaryRational.decode (score (pairBits (Find.context x,Fold.accum x))) <
      BinaryRational.decode (score (pairBits (Find.context x,Find.item x)))
  then Find.item x else Fold.accum x
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
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def bagTest (x : List Bool) : Bool :=
  decide (value (elementPart (pairBits (extractPrefix (extractPrefix x),discardPrefix x)))=
    value (discardPrefix (extractPrefix x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def stepScore (x : List Bool) : List Bool :=
  encode [field 0 (Find.context x),field 1 (Fold.accum x),Find.item x,field 1 (Find.context x)]
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
noncomputable def initial (x : List Bool) : List Bool :=
  encode [[],repeatWords (pairBits (field 2 x,repeatWords (pairBits (field 3 x,[]))))]
noncomputable def context (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 3 x]
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

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open Categorical.Explicit
variable {q a : ℕ}
noncomputable def qword (x : List Bool) : List Bool := Count.run (field 1 (extractPrefix x))
noncomputable def aword (x : List Bool) : List Bool := field 2 (extractPrefix x)
noncomputable def dimensions (x : List Bool) : List Bool := pairBits (qword x,aword x)
attribute [local irreducible] dimensions
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a : ℕ}
noncomputable def test (x : List Bool) : Bool :=
  decide (value (Lookup.run (pairBits (discardPrefix x,field 0 (extractPrefix x))))=value (field 1 (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryCompletionFill

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

noncomputable def look (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix x))
noncomputable def offers (x : List Bool) : List Bool :=
  mapWith look (pairBits (field 1 (discardPrefix x),extractPrefix x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCompletion

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
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n q r : ℕ}
noncomputable def oracleInput (j : ℕ) (x : List Bool) : List Bool := pairBits (field j (extractPrefix x),discardPrefix x)
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
noncomputable def fillInput (x : List Bool) : List Bool := encode [field 3 x,field 4 x,field 9 x]
attribute [local irreducible] fillInput
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

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
open BinaryOpeningPayment (field )
open Categorical.Explicit
variable {n q a p r c : ℕ}
noncomputable def context (x : List Bool) : List Bool := encode
  [field 10 (extractPrefix x),field 3 (extractPrefix x),Count.run (field 4 (extractPrefix x))]
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

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
noncomputable def badBall (x : List Bool) : Bool := decide (discardPrefix x=[])
noncomputable def badRadius (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix (discardPrefix x))<0)
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (colors : Fin n→Fin 3) (label : Fin n→Fin m) (q c : ℕ) (r0 y0 : Fin n)
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) : Finset (Fin n) := by
  classical
  exact if hr : BinaryBranchCheck.Ready δ F S s colors q c m then
    match hb : BlueDP.best (BlueDP.block ((S\s.deleted).filter (fun i=>colors i=2)) F label (rationalScore δ D S Δ s)) c Finset.univ with
    | none=>S
    | some (v,xs)=>
      let P:=BlueDP.makePlan _ _ _ _ _ r0 y0 v xs hb
      result δ D F S Δ s colors hr.2.1 P.sel P.dst q bits
  else S
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_FavorableReady
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
abbrev Bits (n p : ℕ) := Categorical.BinaryOracleIndex (Fin (p*n)) p (Categorical.Explicit.exponent p)
  (Categorical.Explicit.samples (p*n) p)→Bool
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed BinaryObservableBranch
abbrev completionCount (n p : ℕ) :=
  BinaryCategorical.Tape.M (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p)+
    BinaryCategorical.Tape.K p (Categorical.Explicit.exponent p)
abbrev count (n b p : ℕ) := (colorCount n+labelCount n b)+completionCount n p
abbrev Seed (n b p : ℕ) := ((Fin n→Fin 4)×(Fin n→Fin (ColorLabel.labelRange b)))×Bits n p
def layout (n b p : ℕ) : (Fin (count n b p)→Bool)≃Seed n b p :=
  (split (colorCount n+labelCount n b) (completionCount n p)).trans
    (Equiv.prodCongr ((split (colorCount n) (labelCount n b)).trans
      (Equiv.prodCongr (colors n) (labels n b)))
      (BinaryCategorical.Tape.layout (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p)))
def raw {n b p : ℕ} (s : Seed n b p) : List Bool :=
  (BinarySeed.raw (colorTensor s.1.1)++BinarySeed.raw (labelTensor s.1.2))++
    BinaryCategorical.Tape.raw (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p) s.2
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRandomize
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
attribute [local irreducible] Count.run 
noncomputable def nword (x : List Bool) : List Bool := Count.run (field 0 x)
noncomputable def cshape (x : List Bool) : List Bool := encode [nword x,[true,true]]
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
noncomputable def pword (x : List Bool) : List Bool := Count.run (discardPrefix (field 5 x))
noncomputable def qword (x : List Bool) : List Bool := RepeatedAppend.copies (pword x).length (BinaryBranchRandomize.nword x)
noncomputable def dimensions (x : List Bool) : List Bool := pairBits (qword x,pword x)
attribute [local irreducible] dimensions
end MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count

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
noncomputable def finish (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x++field 3 x]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

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
noncomputable def advance (x : List Bool) : List Bool :=
  encode [field 0 (field 0 x),field 1 (field 0 x)++cons (field 1 x) [],field 2 (field 0 x),
    field 3 (field 0 x),field 4 (field 0 x),field 2 x,field 3 x]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

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

def sf (n : ℕ) (x : List Bool) : List Bool := field n (discardPrefix (discardPrefix x))
def item (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def front (x : List Bool) : List Bool := sf 0 x++cons (item x) []
noncomputable def rest (x : List Bool) : List Bool := tail (sf 1 x)
noncomputable def cut (x : List Bool) : List Bool := encode [sf 0 x,item x,rest x]
noncomputable def output (x : List Bool) : List Bool := sf 2 x++cons (cut x) []
noncomputable def step (x : List Bool) : List Bool := encode [front x,rest x,output x]
noncomputable def initial (x : List Bool) : List Bool := Fold.pack x [] (encode [[],x,[]])
end MetricKMedianRecovery.BitMachine.WordList.Slices

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
open BinaryOpeningPayment (field )

def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def addOp (x : List Bool) : List Bool := encode [(0:ℕ).bits,[],[],[],discardPrefix x]
noncomputable def replaceOp (x : List Bool) : List Bool := encode [(2:ℕ).bits,jf 0 x,jf 2 x,[],jf 1 x]
noncomputable def adds (x : List Bool) : List Bool := mapWith addOp (pairBits (x,field 1 x))
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def threeQ (x : List Bool) : List Bool := (3*value (field 2 x)).bits
noncomputable def threeQOne (x : List Bool) : List Bool := (value (threeQ x)+1).bits
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryOpeningPayment (field )
noncomputable def ct (x : List Bool) : List Bool := jf 1 x++jf 2 x
noncomputable def edgeG (x : List Bool) : List Bool := field 4 (field 0 x)
noncomputable def edgeData (x : List Bool) : List Bool := encode [field 1 x,edgeG x]
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
open BinaryOpeningPayment (field )
noncomputable def cutTail (x : List Bool) : List Bool := field 2 (discardPrefix x)
noncomputable def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegularChain
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryOpeningPayment (field )
noncomputable def context (x : List Bool) : List Bool := encode [field 2 (field 0 x),field 3 x,field 1 x,field 2 x]
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

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
open BinaryOpeningPayment (field )
noncomputable def chainInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 2 x,field 2 (field 0 x),field 6 x,field 7 x]
noncomputable def crossCtx (x : List Bool) : List Bool := encode [field 2 (field 0 x),field 3 (field 0 x),field 3 x]
noncomputable def nextQ (x : List Bool) : List Bool := true::field 5 x
noncomputable def firstNode (x : List Bool) : List Bool := pairBits (field 6 x,field 8 x)
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
def sf (i : ℕ) : List Bool→List Bool := field i ∘ field 6
def bf (i : ℕ) : List Bool→List Bool := field i ∘ field 0
noncomputable def H (x : List Bool) : List Bool := WordList.head (sf 5 x)
noncomputable def T (x : List Bool) : List Bool := WordList.tail (sf 5 x)
noncomputable def G (x : List Bool) : List Bool := WordList.head (sf 6 x)
noncomputable def U (x : List Bool) : List Bool := WordList.tail (sf 6 x)
noncomputable def qbits (x : List Bool) : List Bool := (field 2 x).length.bits
noncomputable def key (x : List Bool) : List Bool := (3*value (qbits x)).bits
noncomputable def spare (x : List Bool) : List Bool := (value (key x)+1).bits
noncomputable def leafKey (x : List Bool) : List Bool := (value (key x)+2).bits
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
noncomputable def input (x : List Bool) : List Bool := encode [field 0 x,(field 1 x).tail,field 2 x,
  field 3 x,field 4 x,field 5 x,discardPrefix (field 6 x)]
attribute [local instance] RationalLeaves.metric
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

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
def bf (j : ℕ) : List Bool→List Bool := field j ∘ discardPrefix ∘ extractPrefix
noncomputable def atPrice (x : List Bool) : List Bool :=
  encode [bf 0 x,bf 1 x,bf 2 x,bf 3 x,bf 4 x,bf 5 x,bf 6 x,discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

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
noncomputable def ctx (x : List Bool) : List Bool := pairBits (field 3 x,field 0 x)

noncomputable def loInput (x : List Bool) : List Bool := pairBits (ctx x,field 5 x)

end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end


