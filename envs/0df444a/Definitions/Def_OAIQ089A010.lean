-- Prove2me | Definitions.Def_OAIQ089A010
-- name    : OAIQ089A010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T03:17:02.46299+00:00
-- url     : https://prove2.me/theorems/f8f7b0cf-221a-4753-bd54-06cd931beaa4
-- title:
--   Definitions bundle OAIQ089A010 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 180 declarations of OpenAI's Lean: 49 definitions and 131 theorems. The definitions and types are `OAI.ContingencyTables.ProfilePrograms.profilePaddingData`, `OAI.ContingencyTables.SmallGraphProfiles.ArithmeticEdge`, `OAI.ContingencyTables.SmallGraphProfiles.ArithmeticRepair`, `OAI.ContingencyTables.SmallGraphProfiles.actualOutputData`, `OAI.ContingencyTables.SmallGraphProfiles.boxCode`, `OAI.ContingencyTables.SmallGraphProfiles.codeNeighborStates`, `OAI.ContingencyTables.SmallGraphProfiles.completionJointDefect`, `OAI.ContingencyTables.SmallGraphProfiles.encodedConfiguration`, `OAI.ContingencyTables.SmallGraphProfiles.encodedStepInput`, `OAI.ContingencyTables.SmallGraphProfiles.flatUnitWalk`, `OAI.ContingencyTables.SmallGraphProfiles.fullEnergy`, `OAI.ContingencyTables.SmallGraphProfiles.idealReferenceLaw`, `OAI.ContingencyTables.SmallGraphProfiles.instDecidableEqPaperStates_2`, `OAI.ContingencyTables.SmallGraphProfiles.instDecidableEqPaperStates_3`, `OAI.ContingencyTables.SmallGraphProfiles.listedJointLaw`, `OAI.ContingencyTables.SmallGraphProfiles.paperSmallChain`, `OAI.ContingencyTables.SmallGraphProfiles.physicalEnergy`, `OAI.ContingencyTables.SmallGraphProfiles.profileBoxStep`, `OAI.ContingencyTables.SmallGraphProfiles.repairedCompletion`, `OAI.ContingencyTables.SmallGraphProfiles.smallBitProposal`, `OAI.ContingencyTables.SmallGraphProfiles.smallMoveRat`, `OAI.ContingencyTables.SmallGraphProfiles.smallStationaryLaw`, `OAI.ContingencyTables.SmallGraphProfiles.smallStationaryRat`, `OAI.ContingencyTables.SmallGraphProfiles.smallTransitionLaw`, `OAI.ContingencyTables.SmallGraphProfiles.smallTransitionRat`, `OAI.ContingencyTables.SmallGraphProfiles.smallWalkLaw`, `OAI.ContingencyTables.SmallGraphProfiles.stateGraphEnergy`, `OAI.ContingencyTables.SmallGraphProfiles.stationaryJointLaw`, `OAI.ContingencyTables.SmallGraphProfiles.unitBitStep`, `OAI.ContingencyTables.SmallGraphProfiles.unitBoxStep`, `OAI.ContingencyTables.SmallGraphProfiles.unitJointDraw`, `OAI.ContingencyTables.SmallGraphProfiles.unitOuterDraw`, `OAI.ContingencyTables.SmallGraphProfiles.unitOutputData`, `OAI.ContingencyTables.SmallGraphProfiles.unitSmallChain`, `OAI.MatchingFPRAS.LiteralPacked.chunkFn`, `OAI.MatchingFPRAS.OnlineTree.PolynomialTime`, `OAI.MatchingFPRAS.OnlineTree.WorkBound`, `OAI.MatchingFPRAS.TreeTyped.canonical`, `OAI.MatchingFPRAS.TreeTyped.colexLe`, `OAI.MatchingFPRAS.TreeTyped.finsetBiUnion` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Sampling_AllSamplingAccuracy`, `ContingencyTables_Sampling_AllSmallBoolean`, `ContingencyTables_Sampling_AllSmallChain`, `ContingencyTables_Sampling_AllSmallFibres`, `ContingencyTables_Sampling_AllSmallOuter`, `ContingencyTables_Sampling_AllSmallRational`, `ContingencyTables_Sampling_CompiledResidualCorrection`, `ContingencyTables_Sampling_FirstPaperBooleanProposal`, `ContingencyTables_Sampling_FirstPaperCodeNeighbors`, `ContingencyTables_Sampling_FirstPaperCodeProposal`, `ContingencyTables_Sampling_FirstPaperCorrectionBudget`, `ContingencyTables_Sampling_FirstPaperFeasibility`, `ContingencyTables_Sampling_FirstPaperIdealKernel`, `ContingencyTables_Sampling_FirstPaperJointLaw`, `ContingencyTables_Sampling_FirstPaperLocalNeighbors`, `ContingencyTables_Sampling_FirstPaperProposal`, `ContingencyTables_Sampling_FirstPaperRationalMixing`, `ContingencyTables_Sampling_FirstPaperSmallChain`, `ContingencyTables_Sampling_FirstPaperSmallKernel`, `ContingencyTables_Sampling_FirstPaperSmallMixing`, `ContingencyTables_Sampling_FirstPaperStationaryMass`, `ContingencyTables_Sampling_InverseSmallRepair`, `ContingencyTables_Sampling_PhysicalEdgeMargins`, `ContingencyTables_Sampling_PhysicalGraphVertices`, `ContingencyTables_Sampling_PhysicalMassBound`, `ContingencyTables_Sampling_PhysicalPrefixEnergies`, `ContingencyTables_Sampling_PhysicalRepairGraph`, `ContingencyTables_Sampling_PhysicalRepairMargins`, `ContingencyTables_Sampling_PhysicalRepairMass`, `ContingencyTables_Sampling_PhysicalSmallEnergy`, `ContingencyTables_Sampling_PhysicalSmallGraph`, `ContingencyTables_Sampling_ProfileBoxLaw`, `ContingencyTables_Sampling_ProfileMatrixSemantics`, `ContingencyTables_Sampling_ProfileRepairProgram`, `ContingencyTables_Sampling_ProfileScheduleSemantics`, `ContingencyTables_Sampling_ProfileTransitionSemantics`, `ContingencyTables_Sampling_RepairSmallMargins`, `ContingencyTables_Sampling_SmallDefectLabels`, `ContingencyTables_Sampling_SmallInverseRepairList`, `ContingencyTables_Sampling_SmallProfileCode`, `ContingencyTables_Sampling_SmallProfileEncoding`, `ContingencyTables_Sampling_SmallProfileRepair`, `ContingencyTables_Sampling_SmallProfileValidator`, `ContingencyTables_Sampling_SmallRepairCodeProgram`, `ContingencyTables_Sampling_SmallRepairListProgram`, `ContingencyTables_Sampling_SmallResidualTotals`, `ContingencyTables_Sampling_UnitBoxLaw`, `ContingencyTables_Sampling_UnitFiniteLaw`, `ContingencyTables_Sampling_UnitIntegerLaw`, `ContingencyTables_Sampling_UnitOutputSemantics`, `ContingencyTables_Transport_BoundedProfileSemantics`, `ContingencyTables_Transport_ListedBooleanDraw`, `ContingencyTables_Transport_ListedBooleanStep`, `ContingencyTables_Transport_ListedCompletion`, `ContingencyTables_Transport_ListedDenseDraw`, `ContingencyTables_Transport_ListedIntegerLaw`, `ContingencyTables_Transport_ListedKernelAccuracy`, `ContingencyTables_Transport_ListedOutputSemantics`, `ContingencyTables_Transport_ListedReferenceDecision`, `ContingencyTables_Transport_ListedReservedDraw`, `ContingencyTables_Transport_ReferenceCompletionBounds`, `ContingencyTables_Transport_ReferenceEdgeAcceptance`, `ContingencyTables_Transport_ResidualEnumerationBounds`, `MatchingCount_Complexity_OnlineCost`, `MatchingCount_Machines_TreeCanonical`, `MatchingCount_Machines_TreeColex`, `MatchingCount_Machines_TreeFinite`, `MatchingCount_Machines_TreeFiniteCollections`, `MatchingCount_Machines_TreeFiniteOps`, `MatchingCount_Tapes_Codec`, `MatchingCount_Tapes_Packed`, `MatchingCount_Tapes_PackedInverse`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`; the bundles `OAIQ089A007` and `OAIQ089A008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ089A011`; the proofs of `OAI.ContingencyTables.CompanionObservedUpdateProgram.polynomial_output`, `OAI.ContingencyTables.CompanionPhaseTrialProgram.polynomial_output`, `OAI.ContingencyTables.CompanionRepeatedReturnProgram.polynomial_output`, `OAI.ContingencyTables.CountingBranchProgram.polynomial_publicBudget`, `OAI.ContingencyTables.CountingBranchProgram.polynomial_publicOutput`, `OAI.ContingencyTables.CountingExecutedMachine.polynomial_positive`, `OAI.ContingencyTables.CountingExecutedMachine.public_time`, `OAI.ContingencyTables.ExactGatePolynomial.public_bound`, `OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput`, `OAI.ContingencyTables.ProfilePrograms.work_optionalTrialCount`, `OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output`, `OAI.ContingencyTables.SmallGraphProfiles.allSamplingMachineTime_public_bound`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A007
import Definitions.Def_OAIQ089A008

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeCanonical
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

variable (r : A → A → Prop) [DecidableRel r]

variable [DecidableEq A]
def canonical (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) :
    Realizer (fun as : List A=>as.dedup.insertionSort r) := composition (dedup E) (insertionSort r R)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFinite
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

variable [LinearOrder A]

def listFinset (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (List.toFinset (α:=A)) :=
  (canonical (·≤·) E R).recode id List.toFinset (fun _=>rfl) (fun as=>by
    change encode (as.dedup.insertionSort (·≤·))=encode (as.toFinset.sort (·≤·))
    rw [canonical_eq_sort])

def finsetMember (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×Finset A=>decide (x.1∈x.2)) :=
  (contains E).recode (fun x=>(x.1,x.2.sort (·≤·))) _ (fun _=>rfl) (fun x=>by simp)

def finsetUnion (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) :
    Realizer (fun x : Finset A×Finset A=>x.1∪x.2) :=
  (composition (composition (pair (composition first finsetList) (composition second finsetList)) append)
    (listFinset E R)).congr (by intro x; simp)

def finsetImage [LinearOrder B] {f : A → B} (F : Realizer f)
    (E : Realizer (fun x : B×B=>decide (x.1=x.2)))
    (R : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (Finset.image f) :=
  (composition (composition finsetList (map F)) (listFinset E R)).congr (by intro s; ext a; simp)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteOps
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

variable [LinearOrder A]

def finsetSubset (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>decide (x.1⊆x.2)) :=
  (composition (pair second first) (finsetAll (composition (pair second first) (finsetMember E)))).congr (by
    intro x; simp only [Function.comp_apply,decide_eq_true_eq]; rfl)

def finsetEqual (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>decide (x.1=x.2)) :=
  (composition (pair (finsetSubset E) (composition (pair second first) (finsetSubset E))) boolAnd).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,Finset.Subset.antisymm_iff])

def finsetSDiff (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>x.1\x.2) :=
  (composition (pair second first) (finsetFilterWith (composition
    (composition (pair second first) (finsetMember E)) boolNot))).congr (by intro x; ext a; simp)

def finsetInter (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>x.1∩x.2) :=
  (composition (pair second first) (finsetFilterWith (composition
    (pair second first) (finsetMember E)))).congr (by
      intro x; ext a
      simp only [Function.comp_apply,Finset.mem_filter,decide_eq_true_eq,Finset.mem_inter])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeColex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B] [LinearOrder A] [LinearOrder B]

def colexLe (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) :
    Realizer (fun x : Finset A×Finset A=>decide (toColex x.1≤toColex x.2)) :=
  (composition (pair (composition (pair second first) (finsetSDiff E)) (finsetSDiff E))
    (finsetAll (composition (pair second first) (finsetAny R)))).congr (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,decide_eq_true_eq,Finset.mem_sdiff]
      rw [Finset.Colex.toColex_le_toColex]
      constructor
      · intro h a ha hn
        obtain ⟨b,⟨hb,hbn⟩,hab⟩:=h a ⟨ha,hn⟩
        exact ⟨b,hb,hbn,hab⟩
      · intro h a ⟨ha,hn⟩
        obtain ⟨b,hb,hbn,hab⟩:=h ha hn
        exact ⟨b,⟨hb,hbn⟩,hab⟩)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteCollections
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

variable [LinearOrder A]

def finsetInsert (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (fun x : A×Finset A=>insert x.1 x.2) :=
  (composition (pair (composition first finsetSingleton) second) (finsetUnion E R)).congr (by intro x; simp)

variable [LinearOrder B]
def finsetBiUnion {f : C×A → Finset B} (F : Realizer f)
    (E : Realizer (fun x : B×B=>decide (x.1=x.2)))
    (R : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (fun x : C×Finset A=>x.2.biUnion (fun a=>f (x.1,a))) :=
  (composition (composition (composition (pair first (composition second finsetList))
    (mapWith (composition F finsetList))) flatten) (listFinset E R)).congr (by
      intro x
      ext b
      simp only [Function.comp_apply,List.mem_toFinset,List.mem_flatten,List.mem_map,
        Finset.mem_biUnion,Finset.mem_sort]
      constructor
      · rintro ⟨bs,⟨a,ha,rfl⟩,hb⟩
        exact ⟨a,ha,(Finset.mem_sort (r:=fun x y : B=>x≤y)).mp hb⟩
      · rintro ⟨a,ha,hb⟩
        exact ⟨(f (x.1,a)).sort (·≤·),⟨a,ha,rfl⟩,(Finset.mem_sort (r:=fun x y : B=>x≤y)).mpr hb⟩)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalGraphVertices
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite physical vertices containing every contextual transport leaf -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma mem_vertices_iff (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small) :
    z ∈ vertices small B ↔ (∀ a, z a ≤ B a.1.val.1 a.1.val.2) ∧ Pattern small B z := by
  constructor
  · intro hz
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨naturalProfile_bounded p.val,p.property⟩
  · rintro ⟨hb,hp⟩
    let p : BoundedProfile small B := fun a => ⟨z a,Nat.lt_succ_of_le (hb a)⟩
    let q : Profiles small B := ⟨p,hp⟩
    exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileRepair
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal small-profile repair and its typewise inverse -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma repairedProfile_bounded (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hcap : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2) :
    ∀ a,repairedProfile small B z s t a ≤ B a.1.val.1 a.1.val.2 := by
  rintro ⟨a,b⟩
  cases b
  · exact hcap a
  · exact Nat.sub_le _ _

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRepairProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the literal small-profile repair -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) {n : ℕ} (e : Fin n ≃ Cells small)

/-- The executable row transfer and complement produce exactly the
graph repair, including a large crossing cell outside the stored list. -/
theorem repairedViews_eq (B : I → J → ℕ) (v : SmallProfile small) (s t : I×J) :
    repairedViews (viewList small e v false,
      (List.ofFn (fun i => B (e i).val.1 (e i).val.2),
        (cellIndex small e t,cellIndex small e (t.1,s.2))))=
      (viewList small e (repairedProfile small B v s t) false,
        viewList small e (repairedProfile small B v s t) true) := by
  let w : Fin n → ℕ := fun i => v (e i,false)+
    (if i.val=cellIndex small e (t.1,s.2) then 1 else 0)-
      (if i.val=cellIndex small e t then 1 else 0)
  have hw (i : Fin n) : w i=repairMatrix (smallView small v false) s t (e i).val.1 (e i).val.2 :=
    (indexed_transfer small e v t (t.1,s.2) i).symm
  simp only [repairedViews,viewList,listExchange_ofFn_nat,listDifference_ofFn]
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    exact hw i
  · apply congrArg List.ofFn
    funext i
    exact congrArg (fun a => B (e i).val.1 (e i).val.2-a) (hw i)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPrefixEnergies
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical prefix contexts use each exchange edge at most once -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def physicalEnergy (small : I → J → Bool) (B : I → J → ℕ)
    (f H : SmallProfile small → ℝ) : ℝ :=
  (∑ p ∈ physicalEdges small B,edgeTerm f H p)/2

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalRepairMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal completion-retaining repair dominates the physical weight -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def completionJointDefect (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) (s t : I×J)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (Z : CompletionFibre small B r rbar c cbar z) : JointDefect small r c rbar cbar s t :=
  ⟨Z.val,defect_fibre_views Z hs ht hd,Z.property.1,Z.property.2.1⟩

lemma jointRepair_small_entry (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) (s t : I×J)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (Z : CompletionFibre small B r rbar c cbar z) (i : I) (j : J) (hij : small i j=true) :
    (jointRepair hs ht (completionJointDefect small B r rbar c cbar z s t hs ht hd Z)).val.val i j=
      repairMatrix (smallView small z false) s t i j := by
  change repairMatrix Z.val.val.1 s t i j=repairMatrix (smallView small z false) s t i j
  apply repairMatrix_pointwise
  have hx := (Z.property.2.2.1 i j hij).1
  simpa only [smallView,hij,dite_eq_left] using hx

noncomputable def repairedCompletion (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) (s t : I×J)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (hsmall : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (hcap : ∀ T : ResidualTables small r c rbar cbar,∀ i j,T.val.val i j ≤ B i j)
    (Z : CompletionFibre small B r rbar c cbar z) :
    CompletionFibre small B r rbar c cbar (repairedProfile small B z s t) := by
  let T := jointRepair hs ht (completionJointDefect small B r rbar c cbar z s t hs ht hd Z)
  refine ⟨⟨(T.val.val,T.val.val),T.val.property.1,T.val.property.2⟩,T.property.1,T.property.2,?_,?_,?_⟩
  · intro i j hij
    have he := jointRepair_small_entry small B r rbar c cbar z s t hs ht hd Z i j hij
    change T.val.val i j=repairMatrix (smallView small z false) s t i j at he
    constructor
    · exact he
    · change T.val.val i j=B i j-(B i j-repairMatrix (smallView small z false) s t i j)
      rw [he]
      exact (Nat.sub_sub_self (hsmall ⟨(i,j),hij⟩)).symm
  · intro _ _ _
    rfl
  · intro i j _
    exact hcap T i j

lemma repairedCompletion_injective (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) (s t : I×J)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (hsmall : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (hcap : ∀ T : ResidualTables small r c rbar cbar,∀ i j,T.val.val i j ≤ B i j) :
    Function.Injective (repairedCompletion small B r rbar c cbar z s t hs ht hd hsmall hcap) := by
  intro X Y he
  have htables : jointRepair hs ht (completionJointDefect small B r rbar c cbar z s t hs ht hd X)=
      jointRepair hs ht (completionJointDefect small B r rbar c cbar z s t hs ht hd Y) := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun V => V.val.val.1) he
  have hj := jointRepair_injective hs ht htables
  apply Subtype.ext
  exact congrArg (fun V : JointDefect small r c rbar cbar s t => V.val) hj

/-- The repair is the manuscript's actual profile map, and the weight
inequality counts all completions through its explicit injective map. -/
theorem physical_repair_weight_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (z : SmallProfile (firstPaperSmall r c U))
    (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2) (s t : I×J)
    (hs : firstPaperSmall r c U s.1 s.2=true) (ht : firstPaperSmall r c U t.1 t.2=true)
    (hd : IsDefect (smallView (firstPaperSmall r c U) z false)
      (smallQ (firstPaperSmall r c U) B z) s t)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j ≤ B i j)
    (hf : 0 < hardMarginal (firstPaperSmall r c U) B r c L z) :
    hardMarginal (firstPaperSmall r c U) B r c L z ≤
      hardMarginal (firstPaperSmall r c U) B r c L (repairedProfile (firstPaperSmall r c U) B z s t) := by
  have hsmall := repair_small_capacity r c U L B hB z hz s t hs ht hd hf
  rw [hardMarginal_eq_fibre_card _ _ _ _ _ z hz,
    hardMarginal_eq_fibre_card _ _ _ _ _ _ (repairedProfile_bounded _ _ _ _ _ hsmall)]
  exact_mod_cast Fintype.card_le_of_injective
    (repairedCompletion _ B r _ c _ z s t hs ht hd hsmall hcap)
    (repairedCompletion_injective _ B r _ c _ z s t hs ht hd hsmall hcap)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalRepairGraph
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small graph contains its exchanges and designated repairs -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def fullEnergy (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) : ℝ :=
  symmetricEnergy (fullEdges r c U L B hB) (hardMarginal (firstPaperSmall r c U) B r c L) H

lemma physicalEnergy_le_full (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    physicalEnergy (firstPaperSmall r c U) B (hardMarginal (firstPaperSmall r c U) B r c L) H ≤
      fullEnergy r c U L B hB H :=
  symmetricEnergy_mono _ _ Finset.subset_union_left _ _ (hardMarginal_nonnegative _ _ _ _ _)

lemma fullEnergy_nonnegative (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) : 0 ≤ fullEnergy r c U L B hB H := by
  unfold fullEnergy symmetricEnergy
  exact div_nonneg (Finset.sum_nonneg (fun p _ => pairTerm_nonnegative _ _
    (hardMarginal_nonnegative _ _ _ _ _) p)) (by norm_num)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileEncoding
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The variance encoding retains exactly the positive physical states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma encodeProfile_injective (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    Function.Injective (encodeProfile small B r c L U hB) := by
  intro x y he
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      apply congrArg Sum.inl
      apply (wordChoices small U).injective
      apply rawChoice_injective small U
      exact congrArg (fun z : Profiles small B => naturalProfile z.val) he
    | inr y =>
      have hp := choiceProfile_balanced small B U hB (wordChoices small U x)
      have hxy := congrArg (fun z : Profiles small B => naturalProfile z.val) he
      change rawChoice small U (wordChoices small U x)=naturalProfile y.val at hxy
      have hb : Balanced small B (naturalProfile y.val) := by rwa [← hxy]
      exact False.elim (balanced_not_defect small B _ hb y.property.1)
  | inr x =>
    cases y with
    | inl y =>
      have hp := choiceProfile_balanced small B U hB (wordChoices small U y)
      have hxy := congrArg (fun z : Profiles small B => naturalProfile z.val) he
      change naturalProfile x.val=rawChoice small U (wordChoices small U y) at hxy
      have hb : Balanced small B (naturalProfile x.val) := by rwa [hxy]
      exact False.elim (balanced_not_defect small B _ hb x.property.1)
    | inr y =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg (fun z : Profiles small B => z.val) he

/-- Every omitted physical profile has zero completion weight. -/
lemma outside_encoding_weight_zero (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (p : Profiles small B)
    (hp : p ∉ Set.range (encodeProfile small B r c L U hB)) :
    hardMarginal small B r c L (naturalProfile p.val)=0 := by
  have hn : ¬0 < hardMarginal small B r c L (naturalProfile p.val) := by
    intro hpos
    apply hp
    rcases p.property with hb|hd
    · refine ⟨.inl (balancedWord small B U hB p.val),?_⟩
      apply Subtype.ext
      apply naturalProfile_injective small B
      exact balancedWord_profile small B U hB p.val hb
    · exact ⟨.inr ⟨p.val,hd,hpos⟩,rfl⟩
  exact le_antisymm (le_of_not_gt hn) (hardMarginal_nonnegative _ _ _ _ _ _)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalSmallGraph
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite graph on positive-weight physical states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open CompletionCounts SmallContextEnumeration IntegerWeightedTransport

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma fullEdges_symmetric (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x y : SmallProfile (firstPaperSmall r c U)) :
    (x,y) ∈ fullEdges r c U L B hB ↔ (y,x) ∈ fullEdges r c U L B hB := by
  suffices hs : ∀ x y,(x,y) ∈ fullEdges r c U L B hB → (y,x) ∈ fullEdges r c U L B hB from
    ⟨hs x y,hs y x⟩
  intro x y he
  rcases Finset.mem_union.mp he with he|he
  · apply Finset.mem_union_left
    obtain ⟨hp,D,i,j,hij,hi,hj,hx,hy⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr (Finset.mem_product.mp hp).symm,
      D,j,i,hij.symm,hj,hi,hy,hx⟩
  · apply Finset.mem_union_right
    rcases Finset.mem_union.mp he with he|he
    · apply Finset.mem_union_right
      obtain ⟨z,hz,he⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨z,hz,Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)⟩
    · apply Finset.mem_union_left
      obtain ⟨z,hz,he⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨z,hz,Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)⟩

lemma physicalAdjacent_symmetric (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L) :
    physicalAdjacent r c U L B hB x y ↔ physicalAdjacent r c U L B hB y x :=
  fullEdges_symmetric r c U L B hB _ _

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalSmallEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact energy on the positive physical graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts SmallContextEnumeration RowMajorEnumeration
open IntegerWeightedTransport

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma fullEdges_vertices (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (p : SmallProfile (firstPaperSmall r c U)×SmallProfile (firstPaperSmall r c U))
    (hp : p ∈ fullEdges r c U L B hB) :
    p.1 ∈ vertices (firstPaperSmall r c U) B ∧ p.2 ∈ vertices (firstPaperSmall r c U) B := by
  have hd (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
      naturalProfile z.val ∈ vertices (firstPaperSmall r c U) B :=
    (mem_vertices_iff _ B _).mpr ⟨naturalProfile_bounded z.val,Or.inr z.property.1⟩
  have ht (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
      rawChoice (firstPaperSmall r c U) U (wordChoices _ U (repairWord r c U L B hB z)) ∈
        vertices (firstPaperSmall r c U) B :=
    (mem_vertices_iff _ B _).mpr ⟨rawChoice_bounded _ B U hB _,Or.inl (rawChoice_balanced _ B U hB _)⟩
  rcases Finset.mem_union.mp hp with hp|hp
  · exact Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  · rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hd z,ht z⟩
    · obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨ht z,hd z⟩

lemma positive_vertex_is_physical (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (v : SmallProfile small)
    (hv : v ∈ vertices small B) (hp : 0 < hardMarginal small B r c L v) :
    ∃ z : PhysicalStates small B r c L,physicalProfile small B r c L z=v := by
  obtain ⟨hb,hpattern⟩ := (mem_vertices_iff small B v).mp hv
  let b : BoundedProfile small B := fun a => ⟨v a,Nat.lt_succ_of_le (hb a)⟩
  let p : Profiles small B := ⟨b,hpattern⟩
  exact ⟨⟨p,hp⟩,rfl⟩

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairSmallMargins
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained small margins change by at most one under repair -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles SmallContextFibres SmallContextCoordinates PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [Fintype I] in
lemma repaired_small_row (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J) (i : I) :
    smallRow small (smallView small (repairedProfile small B z s t) false) i=
      smallRow small (repairMatrix (smallView small z false) s t) i := by
  unfold smallRow
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j <;> simp [smallView,repairedProfile,hs]

omit [Fintype J] in
lemma repaired_small_column (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hcap : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (j : J) :
    smallColumn small B (smallView small (repairedProfile small B z s t) true) j=
      smallColumnView small (repairMatrix (smallView small z false) s t) j := by
  unfold smallColumn smallColumnView
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j
  · simp
  · simp only [hs,ite_true, if_true,smallView,dite_eq_left,repairedProfile,ite_true]
    exact Nat.sub_sub_self (hcap ⟨(i,j),hs⟩)

/-- The only loss from a retained margin is the possible single unit
placed into the large receiver. This also covers coincident receiver slots. -/
theorem repair_small_margin_abs (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2=true)
    (hcap : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2) :
    (∀ i,|(smallRow small (smallView small (repairedProfile small B z s t) false) i:ℤ)-
      smallRow small (smallView small z false) i| ≤ 1) ∧
    (∀ j,|(smallColumn small B (smallView small (repairedProfile small B z s t) true) j:ℤ)-
      smallColumn small B (smallView small z true) j| ≤ 1) := by
  have hm := repairMatrix_margins hd (fun i => ∑ j,smallView small z false i j)
    (fun j => ∑ i,smallQ small B z i j) (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i
    rw [repaired_small_row]
    have he := row_small_large small (repairMatrix (smallView small z false) s t) i
    rw [hm.1 i] at he
    dsimp only at he
    rw [← selectedRow_eq small z false i,selectedRow_eq_smallRow] at he
    have hb := repair_large_row_le_one small B z s t hd ht i
    apply abs_le.mpr
    constructor <;> omega
  · intro j
    rw [repaired_small_column small B z s t hcap]
    have he := column_small_large small (repairMatrix (smallView small z false) s t) j
    rw [hm.2 j] at he
    dsimp only at he
    rw [smallQ_column_sum] at he
    have hb := repair_large_column_le_one small B z s t hd ht j
    apply abs_le.mpr
    constructor <;> omega

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalRepairMargins
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The physical padded residuals change by at most one on a repair -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions SmallContextFibres SmallContextCoordinates

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma repair_residual_margins (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (x y : PhysicalStates small B r c L)
    (hxcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L x k) ≤ B i j)
    (hycap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L y k) ≤ B i j)
    (s t : I×J)
    (hd : IsDefect (smallView small (physicalProfile small B r c L x) false)
      (smallQ small B (physicalProfile small B r c L x)) s t)
    (ht : small t.1 t.2=true)
    (hcap : ∀ a : Cells small,repairMatrix
      (smallView small (physicalProfile small B r c L x) false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (heq : physicalProfile small B r c L y=repairedProfile small B (physicalProfile small B r c L x) s t) :
    (∀ i,|(residualRows small B r c L y i:ℤ)-residualRows small B r c L x i| ≤ 1) ∧
    (∀ j,|(residualColumns small B r c L y j:ℤ)-residualColumns small B r c L x j| ≤ 1) := by
  have hx := physical_original_residuals small B r c L x hxcap
  have hy := physical_original_residuals small B r c L y hycap
  have hm := repair_small_margin_abs small B (physicalProfile small B r c L x) s t hd ht hcap
  constructor
  · intro i
    unfold residualRows
    rw [nat_residual_difference _ _ _ _ (hy.1 i) (hx.1 i),heq]
    exact hm.1 i
  · intro j
    unfold residualColumns
    rw [nat_residual_difference _ _ _ _ (hy.2 j) (hx.2 j),heq]
    exact hm.2 j

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalEdgeMargins
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every actual small-graph edge changes each residual margin by at most two -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions SmallContextFibres SmallContextCoordinates
open SmallContextEnumeration RowMajorEnumeration

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma designated_repair_residual_margins (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L x k) ≤ B i j)
    (hycap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L y k) ≤ B i j)
    (z : PositiveDefects (firstPaperSmall r c U) B r c L)
    (hsource : naturalProfile z.val=physicalProfile _ B r c L x)
    (htarget : rawChoice (firstPaperSmall r c U) U
      (wordChoices _ U (repairWord r c U L B hB z))=physicalProfile _ B r c L y) :
    (∀ i,|(residualRows (firstPaperSmall r c U) B r c L y i:ℤ)-residualRows _ B r c L x i| ≤ 1) ∧
    (∀ j,|(residualColumns (firstPaperSmall r c U) B r c L y j:ℤ)-residualColumns _ B r c L x j| ≤ 1) := by
  let st := defectLabels (firstPaperSmall r c U) B r c L z
  have hd := defectLabels_spec (firstPaperSmall r c U) B r c L z
  have hcap := repair_small_capacity r c U L B hB (naturalProfile z.val)
    (naturalProfile_bounded z.val) st.1.val st.2.val st.1.property st.2.property hd z.property.2
  have he := htarget.symm.trans (repairWord_profile r c U L B hB z)
  rw [hsource] at hd hcap he
  exact repair_residual_margins _ B r c L x y hxcap hycap st.1.val st.2.val hd st.2.property hcap he

theorem physical_edge_residual_margins (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hcap : ∀ z : PhysicalStates (firstPaperSmall r c U) B r c L,∀ i j,
      firstPaperSmall r c U i j=false → (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxy : physicalAdjacent r c U L B hB x y) :
    (∀ i,|(residualRows (firstPaperSmall r c U) B r c L y i:ℤ)-residualRows _ B r c L x i| ≤ 2) ∧
    (∀ j,|(residualColumns (firstPaperSmall r c U) B r c L y j:ℤ)-residualColumns _ B r c L x j| ≤ 2) := by
  rcases Finset.mem_union.mp hxy with he|he
  · exact exchange_residual_margins _ B r c L x y (hcap x) (hcap y) (Finset.mem_filter.mp he).2
  · rcases Finset.mem_union.mp he with he|he
    · obtain ⟨z,_,he⟩ := Finset.mem_image.mp he
      have hm := designated_repair_residual_margins r c U L B hB x y (hcap x) (hcap y) z
        (congrArg Prod.fst he) (congrArg Prod.snd he)
      exact ⟨fun i => (hm.1 i).trans (by norm_num),fun j => (hm.2 j).trans (by norm_num)⟩
    · obtain ⟨z,_,he⟩ := Finset.mem_image.mp he
      have hm := designated_repair_residual_margins r c U L B hB y x (hcap y) (hcap x) z
        (congrArg Prod.snd he) (congrArg Prod.fst he)
      constructor
      · intro i
        rw [abs_sub_comm]
        exact (hm.1 i).trans (by norm_num)
      · intro j
        rw [abs_sub_comm]
        exact (hm.2 j).trans (by norm_num)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceCompletionBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Padding and dimension bounds for the actual reference completion block -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma reference_row_padding (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : Option {i : LargeRows r U // i≠i₀}) : L ≤ referenceRows r c U L B i₀ z i :=
  large_row_padding r c U L B z ((Equiv.optionSubtypeNe i₀) i) j₀

lemma reference_column_padding (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (j : Option {j : LargeColumns c U // j≠j₀}) : L ≤ referenceColumns r c U L B j₀ z j :=
  large_column_padding r c U L B z i₀ ((Equiv.optionSubtypeNe j₀) j)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceEdgeAcceptance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Half of every physical completion block accepts an adjacent translation -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open CompletionTranslation

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem reference_edge_acceptance (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hcap : ∀ z : PhysicalStates (firstPaperSmall r c U) B r c
      ((dimensionAllowance (I := I) (J := J))^12),∀ i j,
      firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c _ z k) ≤ B i j)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c
      ((dimensionAllowance (I := I) (J := J))^12))
    (hxy : physicalAdjacent r c U _ B hB x y) :
    (blockCount (referenceRows r c U _ B i₀) (referenceColumns r c U _ B j₀) x:ℝ)/2 ≤
      acceptedCount (referenceRows r c U _ B i₀) (referenceColumns r c U _ B j₀) x y := by
  let d := dimensionAllowance (I := I) (J := J)
  let R := referenceRows r c U (d^12) B i₀
  let P := referenceColumns r c U (d^12) B j₀
  have hm := physical_edge_residual_margins r c U (d^12) B hB hcap x y hxy
  have hr (i) : |(R y i:ℤ)-R x i| ≤ 2 := hm.1 ((Equiv.optionSubtypeNe i₀) i).val
  have hp (j) : |(P y j:ℤ)-P x j| ≤ 2 := hm.2 ((Equiv.optionSubtypeNe j₀) j).val
  have hd := reference_block_dimensions r c U i₀ j₀
  have hD (i j) : |between (R x) (R y) (P x) (P y) i j| ≤ (10*d:ℕ) := by
    have hs := star_abs_le (fun i => (R y i:ℤ)-R x i)
      (fun j => (P y j:ℤ)-P x j) 2 (by norm_num) hr hp i j
    have hc : (Fintype.card {j : LargeColumns c U // j≠j₀}:ℤ)+1 ≤ d := by
      exact_mod_cast (show Fintype.card {j : LargeColumns c U // j≠j₀}+1 ≤ d by
        simpa only [Fintype.card_option] using hd.2.1)
    change |star _ _ i j| ≤ _
    push_cast
    nlinarith
  exact reference_acceptance_half (R x) (P x) (between (R x) (R y) (P x) (P y))
    (reference_totals r c U (d^12) B i₀ j₀ x (hcap x)) (fun _ _ => rfl)
    d (reference_dimension_ge_fourteen r c U i₀ j₀) hd.1 hd.2.1 hd.2.2
    (reference_row_padding r c U (d^12) B i₀ j₀ x)
    (reference_column_padding r c U (d^12) B i₀ j₀ x) hD

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallChain
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal first-paper completion chain has the stated Poincare bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open CompletionTranslation FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def paperSmallChain (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20)) :
    FiniteChain (PaperStates r c) :=
  completionChain
    (referenceRows r c _ _ (stateCapacity r c) i₀)
    (referenceColumns r c _ _ (stateCapacity r c) j₀)
    (fun z => reference_totals r c _ _ (stateCapacity r c) i₀ j₀ z
      (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z))
    (physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (physicalAdjacent_symmetric r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal (dimensionAllowance (I := I) (J := J)))
    ((smallProposal_bounds _ (by unfold dimensionAllowance; omega)).1.le)
    (5*(dimensionAllowance (I := I) (J := J))^2+1)
    (physicalAdjacent_degree_allowance r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal_degree _ (by unfold dimensionAllowance; omega))

noncomputable def stateGraphEnergy (r : I → ℕ) (c : J → ℕ) (H : PaperStates r c → ℝ) : ℝ :=
  fullEnergy r c ((dimensionAllowance (I := I) (J := J))^20)
    ((dimensionAllowance (I := I) (J := J))^12) (stateCapacity r c)
    (stateCapacity_small r c) (physicalExtension _ (stateCapacity r c) r c _ H)

lemma paperSmallChain_pi (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (z : PaperStates r c) :
    (paperSmallChain r c i₀ j₀).π z=stateWeight r c z/(∑ y,stateWeight r c y) := by
  have hw (y : PaperStates r c) := physical_weight_reference_block r c _ _ (stateCapacity r c)
    i₀ j₀ y (physical_paper_capacity _ r c _ _ _ dimension_le_allowance y)
  change _=hardMarginal _ _ _ _ _ _/(∑ y,hardMarginal _ _ _ _ _ _)
  simp_rw [hw]
  rfl

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalMassBound
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Count the small state and its large completion jointly -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres PhysicalLargeProfiles FirstPaperPhysicalMarginal
open SmallContextFibres LargePairEnumeration CompletionCounts NestedPenaltyApplication

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

variable [LinearOrder I] [LinearOrder J]

theorem physical_total_mass_le (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L C : ℕ) (hB : ∀ i j,B i j ≤ C) :
    (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
      (physicalProfile small B r c L z)) ≤
      ((C+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J)) := by
  let s := Fintype.card (SmallView (fun a : I×J => small a.1 a.2))
  let l := Fintype.card (LargeCell (fun a : I×J => small a.1 a.2))
  have hs : Fintype.card (PhysicalStates small B r c L) ≤ (C+1)^s :=
    (Fintype.card_subtype_le _).trans
      ((Fintype.card_subtype_le _).trans (by
        simpa only [s,Fintype.card_eq_nat_card] using boundedProfile_card_le small B C hB))
  have hl : Nat.card (PhysicalAssignments (fun a : I×J => small a.1 a.2)
      (fun a => B a.1 a.2)) ≤ (C+1)^l := by
    simpa only [l,Fintype.card_eq_nat_card] using physicalAssignments_card_le small B C hB
  have he := Fintype.card_congr (partitionEquiv (fun a : I×J => small a.1 a.2))
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool] at he
  have hexp : s+l ≤ 2*dimensionAllowance (I := I) (J := J) := by
    simp only [s,l,Fintype.card_prod,Fintype.card_bool]
    nlinarith [dimension_le_allowance (I := I) (J := J)]
  have hbound (z : PhysicalStates small B r c L) : hardMarginal small B r c L
      (physicalProfile small B r c L z) ≤ (Nat.card (PhysicalAssignments
        (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2)):ℝ) := by
    simpa only [Fintype.card_eq_nat_card] using hardMarginal_le_assignments small B r c L
      (physicalProfile small B r c L z)
  calc
    _ ≤ ∑ _z : PhysicalStates small B r c L,
        (Nat.card (PhysicalAssignments (fun a : I×J => small a.1 a.2)
          (fun a => B a.1 a.2)):ℝ) :=
      Finset.sum_le_sum (fun z _ => hbound z)
    _ = (Fintype.card (PhysicalStates small B r c L):ℝ)*
        Nat.card (PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2)) := by simp
    _ ≤ ((C+1:ℕ):ℝ)^s*((C+1:ℕ):ℝ)^l := by
      apply mul_le_mul
      · exact_mod_cast hs
      · exact_mod_cast hl
      · positivity
      · positivity
    _ = ((C+1:ℕ):ℝ)^(s+l) := (pow_add _ _ _).symm
    _ ≤ _ := by
      exact_mod_cast Nat.pow_le_pow_right (show 1 ≤ C+1 by omega) hexp

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallMixing
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Minimum mass and mixing of the actual small chain -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma stateWeight_ge_one (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) :
    1 ≤ stateWeight r c z := by
  have he := hardMarginal_eq_fibre_card (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z) (naturalProfile_bounded z.val.val)
  change 1 ≤ hardMarginal _ _ _ _ _ _
  rw [he]
  have hp := stateWeight_positive r c z
  change 0 < hardMarginal _ _ _ _ _ _ at hp
  rw [he] at hp
  have hn : 0 < Fintype.card (CompletionFibre (paperSmall r c) (stateCapacity r c) r
      (fun i => r i+PaddedCompletions.rowLargeCount (paperSmall r c) i*
        ((dimensionAllowance (I := I) (J := J))^12)) c
      (fun j => c j+PaddedCompletions.columnLargeCount (paperSmall r c) j*
        ((dimensionAllowance (I := I) (J := J))^12))
      (physicalProfile _ (stateCapacity r c) r c _ z)) := by exact_mod_cast hp
  exact_mod_cast (Nat.succ_le_of_lt hn)

lemma state_total_mass_le (r : I → ℕ) (c : J → ℕ) :
    (∑ z,stateWeight r c z) ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J)) :=
  physical_total_mass_le (paperSmall r c) (stateCapacity r c) r c _ (stateBound r c)
    (stateCapacity_le_bound r c)

lemma paperSmallChain_pi_lower (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (z : PaperStates r c) :
    1/(((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))) ≤
      (paperSmallChain r c i₀ j₀).π z := by
  have hsum : 0 < ∑ y,stateWeight r c y :=
    Finset.sum_pos (fun y _ => stateWeight_positive r c y) Finset.univ_nonempty
  rw [paperSmallChain_pi]
  exact (one_div_le_one_div_of_le hsum (state_total_mass_le r c)).trans
    (div_le_div_of_nonneg_right (stateWeight_ge_one r c z) hsum.le)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallKernel
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact rational law of the actual small-state completion chain -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts CommonBasesFPRAS

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def smallMoveRat (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) : ℚ :=
  if physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x y then
    smallProposalRat (dimensionAllowance (I := I) (J := J))*
      (acceptedCount (referenceRows r c _ _ (stateCapacity r c) i₀)
        (referenceColumns r c _ _ (stateCapacity r c) j₀) x y:ℚ)/
      (blockCount (referenceRows r c _ _ (stateCapacity r c) i₀)
        (referenceColumns r c _ _ (stateCapacity r c) j₀) x:ℚ)
  else 0

noncomputable def smallTransitionRat (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) : ℚ :=
  smallMoveRat r c i₀ j₀ x y+if x=y then 1-∑ z,smallMoveRat r c i₀ j₀ x z else 0

lemma smallMoveRat_cast (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) :
    (smallMoveRat r c i₀ j₀ x y:ℝ)=
      completionMove (referenceRows r c _ _ (stateCapacity r c) i₀)
        (referenceColumns r c _ _ (stateCapacity r c) j₀)
        (physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c))
        (smallProposal (dimensionAllowance (I := I) (J := J))) x y := by
  unfold smallMoveRat completionMove
  split_ifs
  · simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,smallProposalRat,smallProposal,
      Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  · exact Rat.cast_zero

lemma smallTransitionRat_cast (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) :
    (smallTransitionRat r c i₀ j₀ x y:ℝ)=(paperSmallChain r c i₀ j₀).P x y := by
  unfold smallTransitionRat
  dsimp only [paperSmallChain,completionChain,FiniteChain.ofMoves]
  by_cases hxy : x=y <;>
    simp only [hxy,ite_true, if_true,ite_false,Rat.cast_add,Rat.cast_sub,Rat.cast_sum,
      Rat.cast_one,Rat.cast_zero,smallMoveRat_cast]

noncomputable def smallTransitionLaw (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) : RationalLaw (PaperStates r c) where
  mass := smallTransitionRat r c i₀ j₀ x
  nonnegative := fun y => by
    have h := (paperSmallChain r c i₀ j₀).nonnegative x y
    rw [← smallTransitionRat_cast] at h
    exact_mod_cast h
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum,smallTransitionRat_cast,Rat.cast_one]
    exact (paperSmallChain r c i₀ j₀).stochastic x

lemma smallTransitionLaw_mass_ne (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) (hxy : x≠y) :
    (smallTransitionLaw r c i₀ j₀ x).mass y=smallMoveRat r c i₀ j₀ x y := by
  change smallTransitionRat r c i₀ j₀ x y=_
  simp only [smallTransitionRat,hxy,ite_false,add_zero]

noncomputable def smallWalkLaw (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) (n : ℕ) : RationalLaw (PaperStates r c) :=
  walkLaw (smallTransitionLaw r c i₀ j₀) x n

lemma smallWalkLaw_cast (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (n : ℕ) (x y : PaperStates r c) :
    ((smallWalkLaw r c i₀ j₀ x n).mass y:ℝ)=
      ((paperSmallChain r c i₀ j₀).kernel.power n).P x y := by
  exact walkLaw_cast_kernel (smallTransitionLaw r c i₀ j₀) (paperSmallChain r c i₀ j₀)
    (smallTransitionRat_cast r c i₀ j₀) n x y

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperRationalMixing
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixing in total variation for the actual rational small-walk law -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts CommonBasesFPRAS

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def smallStationaryRat (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) : ℚ :=
  (blockCount (referenceRows r c _ _ (stateCapacity r c) i₀)
    (referenceColumns r c _ _ (stateCapacity r c) j₀) x:ℚ)/
  ∑ y : PaperStates r c,(blockCount (referenceRows r c _ _ (stateCapacity r c) i₀)
    (referenceColumns r c _ _ (stateCapacity r c) j₀) y:ℚ)

lemma smallStationaryRat_cast (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) :
    (smallStationaryRat r c i₀ j₀ x:ℝ)=(paperSmallChain r c i₀ j₀).π x := by
  unfold smallStationaryRat
  simp only [Rat.cast_div,Rat.cast_sum,Rat.cast_natCast]
  rfl

noncomputable def smallStationaryLaw (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20)) : RationalLaw (PaperStates r c) where
  mass := smallStationaryRat r c i₀ j₀
  nonnegative := fun x => by
    have h := (paperSmallChain r c i₀ j₀).positive x
    rw [←smallStationaryRat_cast] at h
    exact_mod_cast h.le
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum,smallStationaryRat_cast,Rat.cast_one]
    exact (paperSmallChain r c i₀ j₀).normalized

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperJointLaw
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformity of the actual state/completion joint law -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open ResidualMixture FirstSuccess CompletionTranslation SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma paperFibre_card_block (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (z : PaperStates r c) :
    Fintype.card (PaperFibre r c z)=
      blockCount (referenceRows r c _ _ (stateCapacity r c) i₀)
        (referenceColumns r c _ _ (stateCapacity r c) j₀) z :=
  Fintype.card_congr (referenceFibreEquiv r c _ _ (stateCapacity r c) i₀ j₀ z
    (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z))

noncomputable def stationaryJointLaw (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20)) :
    RationalLaw (PaperStateJoint r c) :=
  dependentJointLaw (smallStationaryLaw r c i₀ j₀) (fun z => uniformLaw (α := PaperFibre r c z))

/-- The law keeps the completion multiplicity exactly: each full pair
has the same probability, including pairs above defective small states. -/
theorem stationaryJointLaw_uniform (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20)) :
    stationaryJointLaw r c i₀ j₀=uniformLaw (α := PaperStateJoint r c) := by
  apply dependentJointLaw_uniform
  intro z
  simp only [paperFibre_card_block r c i₀ j₀]
  rfl

/-- Cardinality of the full joint space is the small chain normalizer. -/
theorem paperStateJoint_card (r : I → ℕ) (c : J → ℕ) :
    (Fintype.card (PaperStateJoint r c):ℝ)=∑ z,stateWeight r c z := by
  rw [Fintype.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (hardMarginal_eq_fibre_card (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z) (naturalProfile_bounded z.val.val)).symm

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperStationaryMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completion-retaining repair bounds the stationary normalizer -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physical_mass_eq_profiles (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :
    (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
      (physicalProfile small B r c L z))=
      ∑ z : Profiles small B,hardMarginal small B r c L (naturalProfile z.val) := by
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro z hz
    have hn : ¬0 < hardMarginal small B r c L (naturalProfile z.val) := by
      intro hp
      exact hz ⟨⟨z,hp⟩,rfl⟩
    exact le_antisymm (le_of_not_gt hn) (hardMarginal_nonnegative _ _ _ _ _ _)
  · intro z
    rfl

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic tests for the positive small-profile state space

Feasibility is decided by coordinate bounds, the allowed local pattern,
and residual margin equations. No completion count is evaluated.
-/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open PhysicalCompletionFibres SmallContextFibres FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions FirstPaperProfiles

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "L" => d^12
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c

lemma stateOfFeasible_profile (z : SmallProfile small) (h : ProfileFeasible r c z) :
    physicalProfile small B r c L (stateOfFeasible r c z h)=z := rfl

lemma decodeProfile_eq_some_iff (z : SmallProfile small) (x : PaperStates r c) :
    decodeProfile r c z=some x ↔ physicalProfile small B r c L x=z := by
  constructor
  · intro hx
    unfold decodeProfile at hx
    split_ifs at hx with h
    · have he := Option.some.inj hx
      rw [←he]
      exact stateOfFeasible_profile r c z h
  · intro hx
    have h : ProfileFeasible r c z := hx ▸ physicalProfile_feasible r c x
    rw [decodeProfile,dite_eq_left h]
    congr 1
    apply physicalProfile_injective small B r c L
    exact (stateOfFeasible_profile r c z h).trans hx.symm

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallDefectLabels
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The defect coordinates are determined by the two integer views -/

namespace ContingencyTables

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

namespace SmallGraphProfiles
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma defectLabels_eq_of_spec (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PositiveDefects small B r c L)
    (st : Cells small×Cells small)
    (h : IsDefect (smallView small (naturalProfile z.val) false)
      (smallQ small B (naturalProfile z.val)) st.1.val st.2.val) :
    defectLabels small B r c L z=st := by
  have he := (defectLabels_spec small B r c L z).labels_unique h
  exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2)

end SmallGraphProfiles
end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_InverseSmallRepair
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit arithmetic inverse of each labelled repair -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma inverseRepairRow_repaired (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (a : Cells small) :
    inverseRepairRow small (repairedProfile small B z s t) s t a.val.1 a.val.2=
      z (a,false) := by
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
  have he := repairMatrix_cast hd a.val.1 a.val.2
  unfold inverseRepairRow transferInt
  simp only [transferInt,smallView,a.property,dite_eq_left,repairedProfile,
    Bool.false_eq_true,ite_false,heta] at *
  omega

/-- The inverse is evaluated once per ordered defect label; no search
through bounded profiles is needed to recover a predecessor. -/
theorem inverseRepairProfile_repaired (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t) :
    inverseRepairProfile small B (repairedProfile small B z s t) s t=z := by
  funext a
  rcases a with ⟨a,b⟩
  cases b
  · exact inverseRepairRow_repaired small B z s t hd a
  · have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
    have hr := inverseRepairRow_repaired small B z s t hd a
    have hq := hd.2 a.val.1 a.val.2
    have hb := hz (a,true)
    simp only [inverseRepairProfile,ite_true, if_true,transferInt,hr]
    simp only [smallQ,smallView,a.property,dite_eq_left,transferInt,heta] at hq
    dsimp only at hb
    omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperLocalNeighbors
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic enumeration of the first-paper chain's neighbors

The list is obtained from ordered coordinate and cell pairs, then filtered
by arithmetic edge and feasibility tests. It never enumerates all states.
-/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open PhysicalCompletionFibres SmallContextFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts SmallContextCoordinates SmallContextEnumeration
open RowMajorEnumeration IntegerWeightedTransport

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "U" => d^20
local notation "L" => d^12
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c
local notation "profile" => physicalProfile small B r c L

/-- A directed repair is identified by its two defect cells. -/
def ArithmeticRepair (v w : SmallProfile small) : Prop :=
  ∃ st : Cells small×Cells small,
    IsDefect (smallView small v false) (smallQ small B v) st.1.val st.2.val ∧
      w=repairedProfile small B v st.1.val st.2.val

/-- All predicates are bounded integer-coordinate tests. -/
def ArithmeticEdge (v w : SmallProfile small) : Prop :=
  (∃ i j,i≠j ∧ 0<v j ∧ w=exchangeTarget v i j) ∨
    ArithmeticRepair r c v w ∨ ArithmeticRepair r c w v

lemma arithmeticRepair_iff (x y : PaperStates r c) :
    ArithmeticRepair r c (profile x) (profile y) ↔
      ∃ z : PositiveDefects small B r c L,
        naturalProfile z.val=profile x ∧
        rawChoice small U (wordChoices small U
          (repairWord r c U L B (stateCapacity_small r c) z))=profile y := by
  constructor
  · rintro ⟨st,hd,hy⟩
    let z : PositiveDefects small B r c L :=
      ⟨x.val.val,⟨st.1.val,st.2.val,st.1.property,st.2.property,hd⟩,x.property⟩
    refine ⟨z,rfl,?_⟩
    rw [repairWord_profile]
    have hl : defectLabels small B r c L z=st := defectLabels_eq_of_spec small B r c L z st hd
    rw [hl]
    exact hy.symm
  · rintro ⟨z,hx,hy⟩
    refine ⟨defectLabels small B r c L z,?_,?_⟩
    · rw [←hx]
      exact defectLabels_spec small B r c L z
    · rw [←hy,repairWord_profile,hx]

/-- On actual states the arithmetic test is exactly the graph relation
used in the Poincare and mixing proofs. -/
theorem arithmeticEdge_iff (x y : PaperStates r c) :
    ArithmeticEdge r c (profile x) (profile y) ↔
      physicalAdjacent r c U L B (stateCapacity_small r c) x y := by
  have hx : profile x ∈ vertices small B :=
    (mem_vertices_iff small B _).mpr ⟨naturalProfile_bounded x.val.val,x.val.property⟩
  have hy : profile y ∈ vertices small B :=
    (mem_vertices_iff small B _).mpr ⟨naturalProfile_bounded y.val.val,y.val.property⟩
  rw [ArithmeticEdge,←adjacent_iff_arithmetic,arithmeticRepair_iff,arithmeticRepair_iff]
  change _ ↔ (profile x,profile y) ∈ physicalEdges small B ∪
    repairEdges r c U L B (stateCapacity_small r c)
  simp only [Finset.mem_union,physicalEdges,Finset.mem_filter,Finset.mem_product,
    hx,hy,true_and,repairEdges,Finset.mem_image,Finset.mem_univ,Prod.mk.injEq]
  constructor
  · rintro (he|he|he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · obtain ⟨z,hz,hw⟩ := he
      exact Or.inr (Or.inr ⟨z,hw,hz⟩)
  · rintro (he|he|he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · obtain ⟨z,hz,hw⟩ := he
      exact Or.inr (Or.inr ⟨z,hw,hz⟩)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallResidualTotals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conservation makes the residual-total test redundant -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextFibres FirstPaperProfiles PaddedCompletions CompletionCounts
open FirstPaperPhysicalMarginal PhysicalCompletionFibres

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The executable tests need bounds, a local pattern and the row/column
inequalities, with equality on small incident margins. No completion
enumeration or additional residual-total oracle is necessary. -/
theorem profileFeasible_of_lineTests (r : I → ℕ) (c : J → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (z : SmallProfile (paperSmall r c))
    (hb : ∀ a,z a ≤ stateCapacity r c a.1.val.1 a.1.val.2)
    (hp : Pattern (paperSmall r c) (stateCapacity r c) z)
    (hr : ∀ i,smallRow (paperSmall r c) (smallView (paperSmall r c) z false) i ≤ r i ∧
      (r i<(dimensionAllowance (I := I) (J := J))^20 →
        smallRow (paperSmall r c) (smallView (paperSmall r c) z false) i=r i))
    (hc : ∀ j,smallColumn (paperSmall r c) (stateCapacity r c)
      (smallView (paperSmall r c) z true) j ≤ c j ∧
      (c j<(dimensionAllowance (I := I) (J := J))^20 →
        smallColumn (paperSmall r c) (stateCapacity r c)
          (smallView (paperSmall r c) z true) j=c j)) :
    ProfileFeasible r c z := by
  refine ⟨hb,hp,⟨fun i => (hr i).1,fun j => (hc j).1⟩,?_,?_,?_⟩
  · intro i hi
    have hi' : r i<(dimensionAllowance (I := I) (J := J))^20 := by omega
    unfold profileRows
    rw [(hr i).2 hi']
    simp [rowLargeCount,paperSmall,firstPaperSmall,hi']
  · intro j hj
    have hj' : c j<(dimensionAllowance (I := I) (J := J))^20 := by omega
    unfold profileColumns
    rw [(hc j).2 hj']
    simp [columnLargeCount,paperSmall,firstPaperSmall,hj']
  · exact padded_residual_totals _ _ z r c _ htotal hp (fun i => (hr i).1) (fun j => (hc j).1)

lemma profileFeasible_lineTests (r : I → ℕ) (c : J → ℕ)
    (z : SmallProfile (paperSmall r c)) (h : ProfileFeasible r c z) :
    (∀ i,smallRow (paperSmall r c) (smallView (paperSmall r c) z false) i ≤ r i ∧
      (r i<(dimensionAllowance (I := I) (J := J))^20 →
        smallRow (paperSmall r c) (smallView (paperSmall r c) z false) i=r i)) ∧
    (∀ j,smallColumn (paperSmall r c) (stateCapacity r c)
      (smallView (paperSmall r c) z true) j ≤ c j ∧
      (c j<(dimensionAllowance (I := I) (J := J))^20 →
        smallColumn (paperSmall r c) (stateCapacity r c)
          (smallView (paperSmall r c) z true) j=c j)) := by
  constructor
  · intro i
    refine ⟨h.residuals.1 i,?_⟩
    intro hi
    have hz := h.rows_outside i (by omega)
    unfold profileRows at hz
    have hb := h.residuals.1 i
    omega
  · intro j
    refine ⟨h.residuals.2 j,?_⟩
    intro hj
    have hz := h.columns_outside j (by omega)
    unfold profileColumns at hz
    have hb := h.residuals.2 j
    omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileValidator
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary validator for the positive profile space -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open PaddedCompletions ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n q : ℕ}

theorem profileTest_iff (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (e : Fin q ≃ Cells (paperSmall r c))
    (z : SmallProfile (paperSmall r c)) :
    profileTest (((cellCatalog (paperSmall r c) e,
      (viewList (paperSmall r c) e z false,viewList (paperSmall r c) e z true)),
      (List.ofFn r,List.ofFn c)),(dimensionAllowance (I := Fin m) (J := Fin n))^20)=true ↔
        ProfileFeasible r c z := by
  let small := paperSmall r c
  let B := stateCapacity r c
  let U := (dimensionAllowance (I := Fin m) (J := Fin n))^20
  have hU (a : Cells small) : B a.val.1 a.val.2=U :=
    stateCapacity_small r c _ _ a.property
  have hb : (∀ a,z a≤U) ↔ ∀ a,z a≤B a.1.val.1 a.1.val.2 := by
    simp only [hU]
  simp only [profileTest,Bool.and_eq_true,cellCatalog,viewList,List.length_ofFn,
    decide_true,true_and]
  change (boundedValues (U,viewList small e z false)=true ∧
    (boundedValues (U,viewList small e z true)=true ∧
    (patternTest ((viewList small e z false,viewList small e z true),U)=true ∧
    (validMargins true (((cellCatalog small e,viewList small e z false),
      (List.ofFn r,List.ofFn c)),U)=true ∧
    validMargins false (((cellCatalog small e,complementValues (U,viewList small e z true)),
      (List.ofFn r,List.ofFn c)),U)=true)))) ↔ _
  constructor
  · rintro ⟨hx,hy,hp,hr,hc⟩
    have hbound : ∀ a,z a≤U := (boundedValues_views small e z U).mp (by simpa using And.intro hx hy)
    apply profileFeasible_of_lineTests r c htotal z (hb.mp hbound)
    · exact (patternTest_views small B e z U hU (fun a => hb.mp hbound (a,true))).mp hp
    · exact (validRows_iff small e z r c U).mp hr
    · exact (validColumns_iff small e B z r c U hU).mp hc
  · intro h
    have hbound := hb.mpr h.bounded
    have hh := (boundedValues_views small e z U).mpr hbound
    have hxy := Bool.and_eq_true_iff.mp hh
    have hl := profileFeasible_lineTests r c z h
    refine ⟨hxy.1,hxy.2,?_,?_,?_⟩
    · exact (patternTest_views small B e z U hU (fun a => h.bounded (a,true))).mpr h.pattern
    · exact (validRows_iff small e z r c U).mpr hl.1
    · exact (validColumns_iff small e B z r c U hU).mpr hl.2

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileCode
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal lists encode exactly the positive physical states -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

lemma profileOfCode_code (z : SmallProfile small) :
    profileOfCode small e (profileCode small e z)=z := by
  funext a
  rcases a with ⟨a,b⟩
  cases b <;>
    simp only [profileOfCode,profileCode,viewList,Bool.false_eq_true,ite_false,ite_true, if_true,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,(e.symm a).isLt,dite_true,
      Option.getD_some,Fin.eta,Equiv.apply_symm_apply]

theorem profileCode_injective : Function.Injective (profileCode small e) := by
  intro z w h
  have hh := congrArg (profileOfCode small e) h
  simpa only [profileOfCode_code] using hh

lemma profileCode_ofCode (v : List ℕ×List ℕ) (hx : v.1.length=q) (hy : v.2.length=q) :
    profileCode small e (profileOfCode small e v)=v := by
  apply Prod.ext
  · simpa only [profileCode,viewList,profileOfCode,Bool.false_eq_true,ite_false,
      Equiv.symm_apply_apply] using ofFn_getD v.1 hx
  · simpa only [profileCode,viewList,profileOfCode,ite_true, if_true,
      Equiv.symm_apply_apply] using ofFn_getD v.2 hy

/-- For arbitrary input lists, the Boolean program succeeds exactly
when those lists encode an actual positive-completion state. -/
theorem profileTest_code_iff (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (e : Fin q ≃ Cells (paperSmall r c))
    (v : List ℕ×List ℕ) :
    profileTest (codeCheckData (cellCatalog (paperSmall r c) e) (List.ofFn r) (List.ofFn c)
      ((dimensionAllowance (I := Fin m) (J := Fin n))^20) v)=true ↔
      ∃ x : PaperStates r c,profileCode (paperSmall r c) e
        (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x)=v := by
  constructor
  · intro h
    have hx : v.1.length=q := by
      have hh := (Bool.and_eq_true_iff.mp h).1
      simpa only [codeCheckData,cellCatalog,List.length_ofFn,decide_eq_true_eq] using hh
    have hy : v.2.length=q := by
      have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
      simpa only [codeCheckData,cellCatalog,List.length_ofFn,decide_eq_true_eq] using hh
    let z := profileOfCode (paperSmall r c) e v
    have hz : profileCode (paperSmall r c) e z=v := profileCode_ofCode _ _ v hx hy
    have hp : ProfileFeasible r c z := by
      apply (profileTest_iff r c htotal e z).mp
      change profileTest (codeCheckData (cellCatalog (paperSmall r c) e)
        (List.ofFn r) (List.ofFn c) ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
        (profileCode (paperSmall r c) e z))=true
      rwa [hz]
    exact ⟨stateOfFeasible r c z hp,hz⟩
  · rintro ⟨x,rfl⟩
    exact (profileTest_iff r c htotal e _).mpr (physicalProfile_feasible r c x)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairCodeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forward and inverse repairs on the stored pair of integer lists -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem forwardRepairCode_eq (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z : SmallProfile small)
    (s t : Cells small) :
    forwardRepairCode (((cellCatalog small e,profileCode small e z),U),
      ((e.symm s).val,(e.symm t).val))=
      profileCode small e (repairedProfile small B z s.val t.val) := by
  have hc : capacityList (U,(profileCode small e z).1)=
      List.ofFn (fun i => B (e i).val.1 (e i).val.2) := by
    simp only [profileCode,viewList,capacityList_ofFn,hU]
  unfold forwardRepairCode
  rw [hc,crossingIndex_eq]
  change repairedViews (viewList small e z false,
    (List.ofFn (fun i => B (e i).val.1 (e i).val.2),
      ((e.symm t).val,cellIndex small e (t.val.1,s.val.2))))=_
  have ht : cellIndex small e t.val=(e.symm t).val := by
    simp only [cellIndex,t.property,dite_true]
  rw [←ht]
  exact repairedViews_eq small e B z s.val t.val

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial lists of encoded forward and inverse repairs -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem mem_forwardRepairList (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z : SmallProfile small)
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) (w : List ℕ×List ℕ) :
    w∈forwardRepairList ((cellCatalog small e,profileCode small e z),U) ↔
      ∃ s t : Cells small,
        IsDefect (smallView small z false) (smallQ small B z) s.val t.val ∧
        w=profileCode small e (repairedProfile small B z s.val t.val) := by
  simp only [forwardRepairList,List.mem_map,forwardRepairLabels,List.mem_filter]
  constructor
  · rintro ⟨⟨i,j⟩,⟨hij,hd⟩,hw⟩
    have hbounds := (mem_cellPairs _ _ i j).mp hij
    simp only [profileCode,viewList,List.length_ofFn] at hbounds
    let si : Fin q := ⟨i,hbounds.1⟩
    let ti : Fin q := ⟨j,hbounds.2⟩
    have hs : e.symm (e si)=si := e.symm_apply_apply si
    have ht : e.symm (e ti)=ti := e.symm_apply_apply ti
    refine ⟨e si,e ti,?_,?_⟩
    · apply (repairLabelTest_iff small e B U hU z hb (e si) (e ti)).mp
      simpa only [hs,ht] using hd
    · rw [←hw]
      simpa only [hs,ht] using forwardRepairCode_eq small e B U hU z (e si) (e ti)
  · rintro ⟨s,t,hd,rfl⟩
    refine ⟨((e.symm s).val,(e.symm t).val),⟨?_,?_⟩,?_⟩
    · apply (mem_cellPairs _ _ _ _).mpr
      simpa only [profileCode,viewList,List.length_ofFn] using
        And.intro (e.symm s).isLt (e.symm t).isLt
    · exact (repairLabelTest_iff small e B U hU z hb s t).mpr hd
    · exact forwardRepairCode_eq small e B U hU z s t

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallInverseRepairList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Checking inverse repair candidates against their forward image -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem mem_checkedInverseRepairList (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z w : SmallProfile small)
    (hw : ∀ a,w a≤B a.1.val.1 a.1.val.2) :
    profileCode small e w∈checkedInverseRepairList ((cellCatalog small e,profileCode small e z),U) ↔
      ∃ s t : Cells small,
        IsDefect (smallView small w false) (smallQ small B w) s.val t.val ∧
        z=repairedProfile small B w s.val t.val := by
  simp only [checkedInverseRepairList,List.mem_map,inverseRepairLabels,List.mem_filter]
  constructor
  · rintro ⟨⟨i,j⟩,⟨hij,htest⟩,hcode⟩
    have hbounds := (mem_cellPairs _ _ i j).mp hij
    simp only [profileCode,viewList,List.length_ofFn] at hbounds
    let s := e ⟨i,hbounds.1⟩
    let t := e ⟨j,hbounds.2⟩
    have hs : (e.symm s).val=i := by simp only [s,Equiv.symm_apply_apply]
    have ht : (e.symm t).val=j := by simp only [t,Equiv.symm_apply_apply]
    have hd := (Bool.and_eq_true_iff.mp htest).1
    have hf := of_decide_eq_true (Bool.and_eq_true_iff.mp htest).2
    simp only [inverseLabelInput,hcode] at hd hf
    refine ⟨s,t,?_,?_⟩
    · apply (repairLabelTest_iff small e B U hU w (fun a => hw (a,true)) s t).mp
      simpa only [hs,ht] using hd
    · have he := forwardRepairCode_eq small e B U hU w s t
      rw [hs,ht] at he
      exact ((profileCode_injective small e) (he.symm.trans hf)).symm
  · rintro ⟨s,t,hd,hz⟩
    let st := ((e.symm s).val,(e.symm t).val)
    have hc : inverseRepairCode (((cellCatalog small e,profileCode small e z),U),st)=
        profileCode small e w := by
      rw [inverseRepairCode_eq small e B U hU z s t,hz,
        inverseRepairProfile_repaired small B w s.val t.val hw hd]
    refine ⟨st,⟨?_,?_⟩,hc⟩
    · apply (mem_cellPairs _ _ _ _).mpr
      simpa only [profileCode,viewList,List.length_ofFn] using
        And.intro (e.symm s).isLt (e.symm t).isLt
    · simp only [inverseLabelTest,inverseLabelInput,hc,Bool.and_eq_true,decide_eq_true_eq]
      refine ⟨(repairLabelTest_iff small e B U hU w (fun a => hw (a,true)) s t).mpr hd,?_⟩
      exact (forwardRepairCode_eq small e B U hU w s t).trans (congrArg (profileCode small e) hz.symm)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeNeighbors
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program for the full physical neighbor list -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n q : ℕ}

theorem mem_rawCodeNeighbors (r : Fin m → ℕ) (c : Fin n → ℕ)
    (e : Fin q ≃ Cells (paperSmall r c)) (x y : PaperStates r c) :
    profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y) ∈
        rawCodeNeighbors (codeCheckData (cellCatalog (paperSmall r c) e)
          (List.ofFn r) (List.ofFn c) ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
          (profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
            ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x))) ↔
      ArithmeticEdge r c
        (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x)
        (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y) := by
  let small := paperSmall r c
  let B := stateCapacity r c
  let U := (dimensionAllowance (I := Fin m) (J := Fin n))^20
  let L := (dimensionAllowance (I := Fin m) (J := Fin n))^12
  let v := physicalProfile small B r c L x
  let w := physicalProfile small B r c L y
  have hU : ∀ a : Cells small,B a.val.1 a.val.2=U :=
    fun a => stateCapacity_small r c _ _ a.property
  have hv : ∀ a : Cells small,v (a,true)≤B a.val.1 a.val.2 :=
    fun a => (physicalProfile_feasible r c x).bounded (a,true)
  have hw : ∀ a,w a≤B a.1.val.1 a.1.val.2 := (physicalProfile_feasible r c y).bounded
  change profileCode small e w ∈ rawCodeNeighbors
    (codeCheckData (cellCatalog small e) (List.ofFn r) (List.ofFn c) U (profileCode small e v)) ↔
      ArithmeticEdge r c v w
  simp only [rawCodeNeighbors,codeCheckData,List.mem_append]
  rw [mem_codeExchangeList,mem_forwardRepairList small e B U hU v hv,
    mem_checkedInverseRepairList small e B U hU v w hw]
  simp only [(profileCode_injective small e).eq_iff,ArithmeticEdge,ArithmeticRepair,Prod.exists]
  rfl

theorem mem_codeNeighbors (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (e : Fin q ≃ Cells (paperSmall r c)) (x y : PaperStates r c) :
    profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y) ∈
        codeNeighbors (codeCheckData (cellCatalog (paperSmall r c) e)
          (List.ofFn r) (List.ofFn c) ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
          (profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
            ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x))) ↔
      physicalAdjacent r c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
        ((dimensionAllowance (I := Fin m) (J := Fin n))^12) (stateCapacity r c)
        (stateCapacity_small r c) x y := by
  rw [codeNeighbors,List.mem_dedup,List.mem_filter]
  have hp := (profileTest_iff r c htotal e
    (physicalProfile (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y)).mpr (physicalProfile_feasible r c y)
  change _ ∧ _ ↔ _
  have hc : profileTest (candidateData
      (codeCheckData (cellCatalog (paperSmall r c) e) (List.ofFn r) (List.ofFn c)
        ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
        (profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x)),
        profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y)))=true := hp
  simp only [hc,and_true]
  rw [mem_rawCodeNeighbors,arithmeticEdge_iff]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperProposal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit small-state proposal realizes the proved ideal kernel -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

lemma smallProposalLaw_mass_some (x y : PaperStates r c) :
    (smallProposalLaw r c x).mass (some y)=proposalWeights r c x y := rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperBooleanProposal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Boolean realization of the small graph proposal law -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

local notation "d" => dimensionAllowance (I := I) (J := J)

lemma smallProposal_codes (x : PaperStates r c) :
    Fintype.card {y // physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x y} ≤
      2^(smallProposalBits (I := I) (J := J)) := by
  rw [Fintype.card_subtype]
  apply (physicalAdjacent_degree_allowance r c _ _ (stateCapacity r c)
    (stateCapacity_small r c) x).trans
  have hd : 1 ≤ d := by unfold dimensionAllowance; omega
  have hs : 1 ≤ d^2 := one_le_pow₀ hd
  exact (show 5*d^2+1 ≤ 32*d^2 by omega).trans (Nat.le_pow_clog (by decide) _)

def smallBitProposal (x : PaperStates r c)
    (bits : Fin (smallProposalBits (I := I) (J := J)) → Bool) : Option (PaperStates r c) :=
  subsetBitDraw (physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x)
    (smallProposalBits (I := I) (J := J)) (smallProposal_codes r c x) bits

/-- The law is independent of the equality decision used by a consumer. -/
theorem smallBitProposal_law_decidableEq (d₀ : DecidableEq (Option (PaperStates r c)))
    (x : PaperStates r c) :
    @mapLaw (Fin (smallProposalBits (I := I) (J := J)) → Bool)
      (Option (PaperStates r c)) _ _ d₀
      (uniformLaw (α := Fin (smallProposalBits (I := I) (J := J)) → Bool))
      (smallBitProposal r c x)=smallProposalLaw r c x := by
  apply law_ext_except _ _ none
  intro y hy
  cases y with
  | none => exact False.elim (hy rfl)
  | some y =>
    exact (subsetBitDraw_mass_decidableEq d₀
      (physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x)
      (smallProposalBits (I := I) (J := J)) (smallProposal_codes r c x) y).trans
        (smallProposalLaw_mass_some r c x y).symm


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compiled neighbor draw has the small-chain proposal law -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts FirstSuccess FairBits

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "L" => d^12
local notation "U" => d^20
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma decode_stateCode (x : PaperStates r c) :
    decodeStateCode r c e (stateCode r c e x)=some x := by
  unfold decodeStateCode stateCode
  rw [ite_eq_left (by simp only [profileCode,viewList,List.length_ofFn,and_self]),profileOfCode_code]
  exact (decodeProfile_eq_some_iff r c _ x).mpr rfl

theorem decodeStateCode_eq_some_iff (v : List ℕ×List ℕ) (x : PaperStates r c) :
    decodeStateCode r c e v=some x ↔ stateCode r c e x=v := by
  constructor
  · intro h
    unfold decodeStateCode at h
    split_ifs at h with hlen
    have hx := (decodeProfile_eq_some_iff r c _ x).mp h
    exact (congrArg (profileCode small e) hx).trans (profileCode_ofCode small e v hlen.1 hlen.2)
  · rintro rfl
    exact decode_stateCode r c e x

def codeNeighborStates (x : PaperStates r c) : List (PaperStates r c) :=
  (codeNeighbors (stateCodeData r c e x)).filterMap (decodeStateCode r c e)

lemma codeNeighborStates_nodup (x : PaperStates r c) : (codeNeighborStates r c e x).Nodup := by
  apply List.Nodup.filterMap
  · intro a b y ha hb
    exact ((decodeStateCode_eq_some_iff r c e a y).mp ha).symm.trans
      ((decodeStateCode_eq_some_iff r c e b y).mp hb)
  · exact codeNeighbors_nodup _

theorem mem_codeNeighborStates (htotal : (∑ i,r i)=∑ j,c j) (x y : PaperStates r c) :
    y∈codeNeighborStates r c e x ↔ physicalAdjacent r c U L B (stateCapacity_small r c) x y := by
  simp only [codeNeighborStates,List.mem_filterMap]
  constructor
  · rintro ⟨v,hv,hy⟩
    have he := (decodeStateCode_eq_some_iff r c e v y).mp hy
    rw [←he] at hv
    exact (mem_codeNeighbors r c htotal e x y).mp hv
  · intro h
    exact ⟨stateCode r c e y,(mem_codeNeighbors r c htotal e x y).mpr h,decode_stateCode r c e y⟩

lemma codeNeighborStates_length (x : PaperStates r c) :
    (codeNeighborStates r c e x).length≤6*d^2 := by
  have hq : q≤d := by
    calc
      q = Fintype.card (Cells small) := by simpa only [Fintype.card_fin] using Fintype.card_congr e
      _ ≤ Fintype.card (Fin m×Fin n) := Fintype.card_subtype_le _
      _ ≤ d := by simpa only [Fintype.card_prod] using (dimension_le_allowance (I := Fin m) (J := Fin n))
  have hc : (codeNeighbors (stateCodeData r c e x)).length≤6*q^2 :=
    codeNeighbors_length _ q (by simp [stateCodeData,codeCheckData,stateCode,profileCode,viewList])
      (by simp [stateCodeData,codeCheckData,stateCode,profileCode,viewList])
  exact (List.length_filterMap_le _ _).trans (hc.trans (by gcongr))

lemma codeNeighborStates_codes (x : PaperStates r c) :
    (codeNeighborStates r c e x).length≤2^s := by
  calc
    _ ≤ 6*d^2 := codeNeighborStates_length r c e x
    _ ≤ 32*d^2 := Nat.mul_le_mul_right _ (by decide)
    _ ≤ 2^s := Nat.le_pow_clog (by decide) _

lemma codeNeighbors_decode_total (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) :
    ∀ v∈codeNeighbors (stateCodeData r c e x),∃ y,decodeStateCode r c e v=some y := by
  intro v hv
  have hp := (List.mem_filter.mp (List.mem_dedup.mp hv)).2
  obtain ⟨y,hy⟩ := (profileTest_code_iff r c htotal e v).mp hp
  exact ⟨y,(decodeStateCode_eq_some_iff r c e v y).mpr hy⟩

lemma decodedCodeProposal_eq (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c)
    (bits : Fin s → Bool) :
    decodedCodeProposal r c e x bits=listBitDraw (codeNeighborStates r c e x) s bits := by
  unfold decodedCodeProposal codeNeighborProposal
  rw [listWordChoice_ofFn]
  exact getElem_filterMap_total (decodeStateCode r c e) _
    (codeNeighbors_decode_total r c e htotal x) _

/-- The implemented binary neighbor choice has exactly the proposal
law used by the already-proved small-chain mixing estimate. -/
theorem decodedCodeProposal_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (decodedCodeProposal r c e x)=smallProposalLaw r c x := by
  have he : decodedCodeProposal r c e x=listBitDraw (codeNeighborStates r c e x) s := by
    funext bits
    exact decodedCodeProposal_eq r c e htotal x bits
  rw [he]
  apply law_ext_except _ _ none
  intro y hy
  cases y with
  | none => exact False.elim (hy rfl)
  | some y =>
    rw [listBitDraw_mass_decidableEq (inferInstance : DecidableEq (Option (PaperStates r c)))
      _ (codeNeighborStates_nodup r c e x) s (codeNeighborStates_codes r c e x) y,
      smallProposalLaw_mass_some]
    unfold proposalWeights
    by_cases hxy : physicalAdjacent r c U L B (stateCapacity_small r c) x y
    · have hy := (mem_codeNeighborStates r c e htotal x y).mpr hxy
      simp only [ite_eq_left hy,ite_eq_left hxy,smallProposalRat]
    · have hy := mt (mem_codeNeighborStates r c e htotal x y).mp hxy
      simp only [ite_eq_right hy,ite_eq_right hxy]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

lemma weight_symbol (a : Symbol) : weight a=17 := by
  change weight (parts a)=17
  simp only [parts,weight_prod,weight_false_list]
  have ha:=a.isLt
  omega
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedCompletion
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entry-preserving completion coordinates in computed list order -/

namespace ContingencyTables.SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open DensePrograms
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ) (B : Fin m → Fin n → ℕ)
variable (hr : 0 < (ProfilePrograms.largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (ProfilePrograms.largeIndices (U,List.ofFn c)).length)

lemma listedFibreEquiv_entry (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k)≤B i j)
    (A : CompletionFibre (firstPaperSmall r c U) B r
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L) c
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)
      (physicalProfile _ B r c L z)) (i) (j) :
    (listedFibreEquiv r c U L B hr hc z hcap A).val i j=
      (referenceFibreEquiv r c U L B (largeOptionEquiv r U hr none)
        (largeOptionEquiv c U hc none) z hcap A).val
          (listedReferenceIndex r U hr i) (listedReferenceIndex c U hc j) := rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedDenseDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A canonical dense draw in the actual retained completion fibre -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)

local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => d^20
local notation "L" => d^12
local notation "R" => listedRows r c U L (stateCapacity r c) hr
local notation "P" => listedColumns r c U L (stateCapacity r c) hc
local notation "nr" => largeTailCount r U
local notation "nc" => largeTailCount c U

theorem listedDenseDraw_variation
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (nr*nc))
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin (nr*nc)) (4*d^8)))
    (h : ℕ) (z : PaperStates r c) :
    (variation (mapLaw (uniformLaw (α := Fin (listedDrawBits r c hr hc h z) → Bool))
      (listedDenseDraw r c hr hc h z)) (uniformLaw (α := PaperFibre r c z)):ℝ) ≤ (2:ℝ)^(-(h:ℝ)) := by
  let E : PaperFibre r c z ≃ Table (R z) (P z) := paperListedEquiv r c hr hc z
  let fb := canonicalFallback (R z) (P z) (listed_paper_totals r c hr hc z)
  let : Nonempty (Table (R z) (P z)) := ⟨fb⟩
  have hv := canonicalDenseDraw_variation (R z) (P z) (listed_dimension_fourteen r c hr hc)
    (listed_row_padding r c U L (stateCapacity r c) hr hc z)
    (listed_column_padding r c U L (stateCapacity r c) hr hc z)
    (listed_dimensions r c hr hc).1 (listed_dimensions r c hr hc).2.1
    (listed_dimensions r c hr hc).2.2 (listed_paper_totals r c hr hc z) hPL hCheeger h
  unfold listedDenseDraw
  rw [mapLaw_equiv_output]
  change (variation (equivLaw E.symm _) (uniformLaw (α := PaperFibre r c z)):ℝ) ≤ _
  rw [←uniform_equiv E.symm,variation_equiv]
  exact hv

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedReservedDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common fixed word for all computed residual completion draws -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

theorem listedPaddedDraw_law (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (z : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin (25*(d+b+h+1)^62) → Bool)) (listedPaddedDraw r c hr hc b h hb z)=
      mapLaw (uniformLaw (α := Fin (listedDrawBits r c hr hc h z) → Bool))
        (listedDenseDraw r c hr hc h z) :=
  padded_draw_law (listedDrawBits_le r c hr hc b h hb z) (listedDenseDraw r c hr hc h z)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperIdealKernel
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separate identification of the ideal small-state completion experiment -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

/-- The ideal reference draw is transported from the nonempty physical
completion fibre, so no additional existence assumption is needed. -/
def idealReferenceLaw (z : PaperStates r c) : RationalLaw (Table (R z) (P z)) :=
  equivLaw (paperReferenceEquiv r c i₀ j₀ z) (uniformLaw (α := PaperFibre r c z))

lemma idealReferenceLaw_uniform (z : PaperStates r c) :
    let _ : Nonempty (Table (R z) (P z)) :=
      ⟨paperReferenceEquiv r c i₀ j₀ z (Classical.choice (inferInstance : Nonempty (PaperFibre r c z)))⟩
    idealReferenceLaw r c i₀ j₀ z=uniformLaw (α := Table (R z) (P z)) := by
  let : Nonempty (Table (R z) (P z)) :=
    ⟨paperReferenceEquiv r c i₀ j₀ z (Classical.choice (inferInstance : Nonempty (PaperFibre r c z)))⟩
  dsimp only
  exact uniform_equiv (paperReferenceEquiv r c i₀ j₀ z)

variable [Nonempty (PaperStates r c)]

theorem smallIdealStep_eq (x : PaperStates r c) :
    completionStepLaw R P (smallProposalLaw r c) (idealReferenceLaw r c i₀ j₀) x=
      smallTransitionLaw r c i₀ j₀ x := by
  let : ∀ z : PaperStates r c,Nonempty (Table (R z) (P z)) := fun z =>
    ⟨paperReferenceEquiv r c i₀ j₀ z (Classical.choice (inferInstance : Nonempty (PaperFibre r c z)))⟩
  have he : idealReferenceLaw r c i₀ j₀ =
      fun z => uniformLaw (α := Table (R z) (P z)) := by
    funext z
    exact idealReferenceLaw_uniform r c i₀ j₀ z
  rw [he]
  rw [completionStepLaw_proposal_at R P (smallProposalLaw r c)
    (fun _ => proposalLaw (proposalWeights r c x) (proposalWeights_nonnegative r c x)
      (proposalWeights_total r c x)) _ x rfl]
  apply uniformCompletionStep_eq R P
    (proposalWeights r c x) (proposalWeights_nonnegative r c x)
    (proposalWeights_total r c x) x (smallTransitionLaw r c i₀ j₀ x)
  intro y hy
  rw [smallTransitionLaw_mass_ne r c i₀ j₀ x y hy.symm]
  unfold smallMoveRat proposalWeights
  split_ifs <;> ring

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedReferenceDecision
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed large rectangle implements the reference decision -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open CompletionTranslation
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] referenceFibreEquiv listedFibreEquiv
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "i₀" => largeOptionEquiv r (d^20) hr none
local notation "j₀" => largeOptionEquiv c (d^20) hc none
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "R₀" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P₀" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

lemma listedReferenceIndex_none (v : Fin m → ℕ) (V : ℕ)
    (hv : 0 < (largeIndices (V,List.ofFn v)).length) :
    listedReferenceIndex v V hv none=none :=
  Equiv.optionSubtypeNe_symm_self _

lemma listed_between (x y : PaperStates r c) (i) (j) :
    between (R x) (R y) (P x) (P y) i j=
      between (R₀ x) (R₀ y) (P₀ x) (P₀ y)
        (listedReferenceIndex r (d^20) hr i) (listedReferenceIndex c (d^20) hc j) := by
  have he := between_reindex (listedReferenceIndex r (d^20) hr)
    (listedReferenceIndex c (d^20) hc)
    (listedReferenceIndex_none r _ hr) (listedReferenceIndex_none c _ hc)
    (R₀ x) (R₀ y) (P₀ x) (P₀ y) i j
  simpa only [listedReference_row,listedReference_column] using he

lemma listed_translated_nonnegative (x y : PaperStates r c) (A : PaperFibre r c x) :
    (∀ i j,0 ≤ ((paperListedEquiv r c hr hc x A).val i j:ℤ)+
      between (R x) (R y) (P x) (P y) i j) ↔
    ∀ i j,0 ≤ ((paperReferenceEquiv r c i₀ j₀ x A).val i j:ℤ)+
      between (R₀ x) (R₀ y) (P₀ x) (P₀ y) i j := by
  have he (i) (j) : (paperListedEquiv r c hr hc x A).val i j=
      (paperReferenceEquiv r c i₀ j₀ x A).val
        (listedReferenceIndex r (d^20) hr i) (listedReferenceIndex c (d^20) hc j) :=
    @listedFibreEquiv_entry m n r c (d^20) (d^12) (stateCapacity r c) hr hc x
      (physical_paper_capacity (paperSmall r c) r c d (d^12) (d^20)
        dimension_le_allowance x) A i j
  simp only [he,listed_between]
  constructor
  · intro h i j
    obtain ⟨i,rfl⟩ := (listedReferenceIndex r (d^20) hr).surjective i
    obtain ⟨j,rfl⟩ := (listedReferenceIndex c (d^20) hc).surjective j
    exact h i j
  · intro h i j
    exact h _ _

theorem listed_completionDecision (x : PaperStates r c) (proposal : Option (PaperStates r c))
    (A : PaperFibre r c x) :
    completionDecision R P x proposal (paperListedEquiv r c hr hc x A)=
      completionDecision R₀ P₀ x proposal (paperReferenceEquiv r c i₀ j₀ x A) := by
  cases proposal with
  | none => rfl
  | some y =>
    unfold completionDecision
    dsimp only
    have he := listed_translated_nonnegative r c hr hc x y A
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (he.mp h₁))
    · exact False.elim (h₁ (he.mpr h₂))
    · rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTransitionSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact semantics of the binary outer transition -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical

noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))

variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

def encodedStepInput (x : PaperStates r c) (proposal : Fin s → Bool) (completion : Fin f → Bool) :
    ProfileStepInput := (((stateCodeData r c e x,d^12),(d,h)),(List.ofFn proposal,List.ofFn completion))


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedKernelAccuracy
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixing with the computed, canonically initialized completion draw -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits CompletionTranslation CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "i₀" => largeOptionEquiv r (d^20) hr none
local notation "j₀" => largeOptionEquiv c (d^20) hc none

def listedJointLaw (x : PaperStates r c) (steps : ℕ) : RationalLaw (PaperStateJoint r c) :=
  dependentJointLaw (walkLaw (listedSmallKernel r c hr hc b h hb) x steps)
    (listedFibreLaw r c hr hc b h hb)

variable (hPL : PublishedInputs.FiniteBoxPrekopaLeindler
  (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
variable (hCheeger : PublishedInputs.FiniteCheeger
  (GridBoundary.Grid (I := Fin (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
    (4*(dimensionAllowance (I := Fin m) (J := Fin n))^8)))

include hPL hCheeger


theorem listedFibreLaw_variation (z : PaperStates r c) :
    variation (listedFibreLaw r c hr hc b h hb z) (uniformLaw (α := PaperFibre r c z)) ≤ 1/(2:ℚ)^h := by
  have ht := @listedDenseDraw_variation m n r c hr hc
    hPL hCheeger h z
  rw [←listedPaddedDraw_law r c hr hc b h hb z] at ht
  change (variation (listedFibreLaw r c hr hc b h hb z)
    (uniformLaw (α := PaperFibre r c z)):ℝ) ≤ _ at ht
  rw [←dyadicError_cast] at ht
  exact (Rat.cast_le (K := ℝ)).mp ht

theorem listedReferenceLaw_variation (z : PaperStates r c) :
    variation (listedReferenceLaw r c hr hc b h hb z) (idealReferenceLaw r c i₀ j₀ z) ≤ 1/(2:ℚ)^h := by
  unfold listedReferenceLaw idealReferenceLaw
  rw [variation_equiv]
  exact listedFibreLaw_variation r c hr hc b h hb hPL hCheeger z

variable [Nonempty (PaperStates r c)]

theorem listedSmallKernel_variation (x : PaperStates r c) :
    variation (listedSmallKernel r c hr hc b h hb x) (smallTransitionLaw r c i₀ j₀ x) ≤ 1/(2:ℚ)^h := by
  rw [←smallIdealStep_eq r c i₀ j₀]
  apply completionStep_variation
  intro z
  exact listedReferenceLaw_variation r c hr hc b h hb hPL hCheeger z


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedBooleanStep
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed binary outer step has the proved mixing kernel -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open ResidualMixture FirstSuccess FairBits CompletionTranslation SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "i₀" => largeOptionEquiv r (d^20) hr none
local notation "j₀" => largeOptionEquiv c (d^20) hc none
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

lemma listedBlockDraw_law (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin f → Bool)) (listedBlockDraw r c hr hc b h hb x)=
      listedReferenceLaw r c hr hc b h hb x := by
  exact mapLaw_equiv_output (paperReferenceEquiv r c i₀ j₀ x) _ _

attribute [local irreducible] FirstSuccess.mapLaw completionStepLaw

theorem listedBitStep_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin (s+f) → Bool)) (listedBitStep r c e hr hc b h hb x)=
      listedSmallKernel r c hr hc b h hb x := by
  have he := wordCompletionStep_law R P (decodedCodeProposal r c e)
    (listedBlockDraw r c hr hc b h hb) x
  have hp := funext (decodedCodeProposal_law r c e htotal)
  have hd := funext (listedBlockDraw_law r c hr hc b h hb)
  have hP := congrArg (fun prop : PaperStates r c → RationalLaw (Option (PaperStates r c)) =>
    completionStepLaw R P prop
      (fun x => mapLaw (uniformLaw (α := Fin f → Bool)) (listedBlockDraw r c hr hc b h hb x)) x) hp
  have hD := congrArg (fun draw : (x : PaperStates r c) → RationalLaw (Table (R x) (P x)) =>
    completionStepLaw R P (smallProposalLaw r c) draw x) hd
  have hq := funext (fun y : PaperStates r c =>
    mapLaw_decidableEq_irrel (@Option.instDecidableEq (PaperStates r c) inferInstance)
      (inferInstance : DecidableEq (Option (PaperStates r c)))
      (uniformLaw (α := Fin s → Bool)) (decodedCodeProposal r c e y))
  have hQ := congrArg (fun prop : PaperStates r c → RationalLaw (Option (PaperStates r c)) =>
    completionStepLaw R P prop
      (fun x => mapLaw (uniformLaw (α := Fin f → Bool)) (listedBlockDraw r c hr hc b h hb x)) x) hq
  exact he.trans (hQ.trans (hP.trans hD))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded binary loop preserves the physical profile walk -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open SmallContextCoordinates FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)

def encodedConfiguration (initial current : PaperStates r c) : ProfileConfiguration :=
  (((stateCodeData r c e initial,d^12),(d,h)),stateCode r c e current)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedBooleanDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal finite-word outer sampling with the computed dense draw -/

namespace ContingencyTables.SmallGraphProfiles
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

theorem listedFlatWalk_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*(s+f)) → Bool))
      (listedFlatWalk r c e hr hc b h hb x n)=
      walkLaw (listedSmallKernel r c hr hc b h hb) x n := by
  unfold listedFlatWalk
  rw [←map_equiv (GridBoundary.gridWordEquiv n (s+f)),uniform_equiv]
  change wordWalkLaw _ _ _=_
  rw [wordWalkLaw_eq]
  exact congrArg (fun K => walkLaw K x n)
    (funext (listedBitStep_law r c e hr hc b h hb htotal))

/-- The terminal completion uses fresh bits at the adaptively obtained
state, with exactly the joint law used in the error proof. -/
theorem listedJointDraw_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*(s+f)+f) → Bool))
      (listedJointDraw r c e hr hc b h hb x n)=
      listedJointLaw r c hr hc b h hb x n := by
  let E := splitWordEquiv (n*(s+f)) f
  let F := fun ab : (Fin (n*(s+f)) → Bool) × (Fin f → Bool) =>
    let z := listedFlatWalk r c e hr hc b h hb x n ab.1
    (⟨z,listedPaddedDraw r c hr hc b h hb z ab.2⟩ : PaperStateJoint r c)
  have he := map_equiv E (uniformLaw (α := Fin (n*(s+f)+f) → Bool)) F
  rw [uniform_equiv,←uniform_product] at he
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin (n*(s+f)) → Bool))
        (uniformLaw (α := Fin f → Bool))) F := he.symm
    _ = dependentJointLaw
        (mapLaw (uniformLaw (α := Fin (n*(s+f)) → Bool))
          (listedFlatWalk r c e hr hc b h hb x n))
        (fun z => mapLaw (uniformLaw (α := Fin f → Bool))
          (listedPaddedDraw r c hr hc b h hb z)) :=
      mapLaw_dependent_product (A := Fin (n*(s+f)) → Bool) (B := Fin f → Bool)
        (X := PaperStates r c) (Y := PaperFibre r c)
        (uniformLaw (α := Fin (n*(s+f)) → Bool)) (uniformLaw (α := Fin f → Bool))
        (listedFlatWalk r c e hr hc b h hb x n)
        (fun z => listedPaddedDraw r c hr hc b h hb z)
    _ = _ := by rw [listedFlatWalk_law r c e hr hc b h hb htotal]; rfl

/-- All trial words are independent and failed trials return the fixed
feasible fallback. In particular, every bit word returns a feasible table. -/
theorem listedOuterDraw_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) (n J₀ : ℕ) (z₀ : Table r c) :
    mapLaw (uniformLaw (α := Fin (J₀*(n*(s+f)+f)) → Bool))
      (listedOuterDraw r c e hr hc b h hb x n J₀ z₀)=
      retryLaw (listedJointLaw r c hr hc b h hb x n)
        (stateTrial r c) z₀ J₀ := by
  unfold listedOuterDraw
  rw [←map_equiv (GridBoundary.gridWordEquiv J₀ (n*(s+f)+f)),uniform_equiv]
  change wordRetryLaw _ _ _=_
  rw [wordRetryLaw_eq,←retryLaw_map,listedJointDraw_law r c e hr hc b h hb htotal]


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedOutputSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable output entries for actual retained completion fibres -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open FirstPaperProfiles PaddedCompletions CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] referenceFibreEquiv listedFibreEquiv
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "L" => d^12

def actualOutputData (x : PaperStates r c) (A : PaperFibre r c x) : OuterTableData :=
  outputData ((stateCodeData r c e x,L),tableOutput (paperListedEquiv r c hr hc x A))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileScheduleSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed schedule and initializer equal the proved sampler data -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] profileRetry listedOuterDraw tableState
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

lemma marginDimension_ofFn : marginDimension (List.ofFn r,List.ofFn c)=d := by
  simp only [marginDimension,List.length_ofFn,dimensionAllowance,Fintype.card_fin]

lemma marginPadding_ofFn : marginPadding (List.ofFn r,List.ofFn c)=d^12 := by
  rw [marginPadding,marginDimension_ofFn]

lemma marginStateBound_ofFn : marginStateBound (List.ofFn r,List.ofFn c)=stateBound r c := by
  rw [marginStateBound,List.sum_ofFn,marginDimension_ofFn,marginPadding_ofFn,marginThreshold_ofFn]
  rfl

lemma marginBinaryLength_ofFn : marginBinaryLength (List.ofFn r,List.ofFn c)=b := by
  rw [marginBinaryLength,marginDimension_ofFn,marginStateBound_ofFn]
  rfl

lemma parameterDimension_ofFn (k : ℕ) : parameterDimension ((List.ofFn r,List.ofFn c),k)=d :=
  marginDimension_ofFn r c

lemma parameterBinaryLength_ofFn (k : ℕ) : parameterBinaryLength ((List.ofFn r,List.ofFn c),k)=b :=
  marginBinaryLength_ofFn r c

lemma parameterSteps_ofFn (k : ℕ) :
    parameterSteps ((List.ofFn r,List.ofFn c),k)=outerSteps d b k := by
  rw [parameterSteps,parameterDimension_ofFn,parameterBinaryLength_ofFn]
  rfl

lemma parameterAccuracy_ofFn (k : ℕ) :
    parameterAccuracy ((List.ofFn r,List.ofFn c),k)=outerAccuracy d b k := by
  rw [parameterAccuracy,parameterDimension_ofFn,parameterBinaryLength_ofFn]
  rfl

lemma parameterProposalWidth_ofFn (k : ℕ) :
    parameterProposalWidth ((List.ofFn r,List.ofFn c),k)=smallProposalBits (I := Fin m) (J := Fin n) := by
  rw [parameterProposalWidth,parameterDimension_ofFn]

lemma parameterCompletionWidth_ofFn (k : ℕ) :
    parameterCompletionWidth ((List.ofFn r,List.ofFn c),k)=25*(d+b+outerAccuracy d b k+1)^62 := by
  rw [parameterCompletionWidth,parameterDimension_ofFn,parameterBinaryLength_ofFn,
    parameterAccuracy_ofFn]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallFibres
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Empty large rectangles have a unique retained completion -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

lemma paperFibre_card_allSmall (hsmall : ∀ i j,paperSmall r c i j=true)
    (z : PaperStates r c) : Fintype.card (PaperFibre r c z)=1 := by
  let : Subsingleton (PaperFibre r c z) := completionFibre_subsingleton _ _ _ _ _ _ _ hsmall
  let : Unique (PaperFibre r c z) := ⟨⟨Classical.choice inferInstance⟩,fun x => Subsingleton.elim x _⟩
  exact Fintype.card_unique

/-- No dense sampler or numerical integral is needed in this branch. -/
lemma stateWeight_allSmall (hsmall : ∀ i j,paperSmall r c i j=true)
    (z : PaperStates r c) : stateWeight r c z=1 := by
  change hardMarginal _ _ _ _ _ _=1
  rw [hardMarginal_eq_fibre_card (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z) (naturalProfile_bounded z.val.val)]
  exact_mod_cast paperFibre_card_allSmall r c hsmall z

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallChain
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-state walk when no dense completion remains

Every retained completion then has weight one. The same local graph is
sampled by accepting every valid proposal; no reference row is chosen.
-/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts CommonBasesFPRAS FiniteExposureVariance

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
local notation "d" => dimensionAllowance (I := I) (J := J)

local notation "Adj" => physicalAdjacent r c (d^20) (d^12) (stateCapacity r c) (stateCapacity_small r c)

local instance instDecidableEqPaperStates_r5e6e21_1 : DecidableEq (PaperStates r c) := Classical.decEq _
def unitSmallChain : FiniteChain (PaperStates r c) :=
  MetropolisChain.chain (fun _ => 1) (fun _ => by norm_num) Adj
    (physicalAdjacent_symmetric r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal d) ((smallProposal_bounds d (by unfold dimensionAllowance; omega)).1.le)
    (5*d^2+1)
    (physicalAdjacent_degree_allowance r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal_degree d (by unfold dimensionAllowance; omega))

lemma unitSmallChain_pi (z : PaperStates r c) :
    (unitSmallChain r c).π z=1/(Fintype.card (PaperStates r c):ℝ) := by
  simp only [unitSmallChain,MetropolisChain.chain,FiniteChain.ofMoves,
    MetropolisChain.normalizer,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

lemma unitSmallChain_energy (H : PaperStates r c → ℝ) :
    (unitSmallChain r c).energy H=
      (smallProposal d/(Fintype.card (PaperStates r c):ℝ))*
        ((∑ x,∑ y,if Adj x y then (H x-H y)^2 else 0)/2) := by
  exact MetropolisChain.unit_chain_energy Adj
    (physicalAdjacent_symmetric r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal d) ((smallProposal_bounds d (by unfold dimensionAllowance; omega)).1.le)
    (5*d^2+1)
    (physicalAdjacent_degree_allowance r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal_degree d (by unfold dimensionAllowance; omega)) H

lemma unitSmallChain_pi_weight
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true) (z : PaperStates r c) :
    (unitSmallChain r c).π z=stateWeight r c z/(∑ y,stateWeight r c y) := by
  rw [unitSmallChain_pi]
  simp only [stateWeight_allSmall r c hsmall,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallRational
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rational walk on an empty large rectangle -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts CommonBasesFPRAS

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)

attribute [local instance] OAI.ContingencyTables.SmallGraphProfiles.instDecidableEqPaperStates_1
lemma unitSmallStep_mass (x y : PaperStates r c) :
    (unitSmallStep r c x).mass y=proposalWeights r c x y+
      if x=y then 1-∑ z,proposalWeights r c x z else 0 :=
  proposalStayLaw_mass _ _ _ x y

variable [Nonempty (PaperStates r c)]

lemma unitSmallStep_cast (x y : PaperStates r c) :
    ((unitSmallStep r c x).mass y:ℝ)=(unitSmallChain r c).P x y := by
  rw [unitSmallStep_mass]
  simp only [Rat.cast_add,apply_ite,Rat.cast_sub,Rat.cast_one,Rat.cast_zero,Rat.cast_sum]
  simp only [proposalWeights,apply_ite,smallProposalRat_cast,Rat.cast_zero]
  simp only [unitSmallChain,MetropolisChain.chain,FiniteChain.ofMoves,MetropolisChain.move,
    div_self (one_ne_zero : (1:ℝ)≠0),min_self,mul_one]
  by_cases hxy : x=y <;> simp only [hxy,ite_true, if_true,ite_false]

lemma unitSmallChain_pi_lower
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (z : PaperStates r c) :
    1/(((stateBound r c+1:ℕ):ℝ)^(2*d)) ≤ (unitSmallChain r c).π z := by
  have hs : 0 < ∑ y,stateWeight r c y :=
    Finset.sum_pos (fun y _ => stateWeight_positive r c y) Finset.univ_nonempty
  rw [unitSmallChain_pi_weight r c hsmall]
  exact (one_div_le_one_div_of_le hs (state_total_mass_le r c)).trans
    (div_le_div_of_nonneg_right (stateWeight_ge_one r c z) hs.le)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallBoolean
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boolean implementation when all cells are retained -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits CompletionTranslation CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "s" => smallProposalBits (I := I) (J := J)
local instance instDecidableEqPaperStates_2 : DecidableEq (PaperStates r c) := Classical.decEq _

def unitBitStep (x : PaperStates r c) (bits : Fin s → Bool) : PaperStates r c :=
  (smallBitProposal r c x bits).getD x

lemma unitBitStep_law (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (unitBitStep r c x)=unitSmallStep r c x := by
  unfold unitBitStep
  calc
    _ = mapLaw (mapLaw (uniformLaw (α := Fin s → Bool)) (smallBitProposal r c x))
        (fun z : Option (PaperStates r c) => z.getD x) :=
      (mapLaw_comp _ (smallBitProposal r c x)
        (fun z : Option (PaperStates r c) => z.getD x)).symm
    _ = _ := by rw [smallBitProposal_law_decidableEq r c _ x]; rfl

def flatUnitWalk (x : PaperStates r c) (n : ℕ) (bits : Fin (n*s) → Bool) : PaperStates r c :=
  wordWalk (unitBitStep r c) x n (GridBoundary.gridWordEquiv n s bits)

lemma flatUnitWalk_law (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (flatUnitWalk r c x n)=
      walkLaw (unitSmallStep r c) x n := by
  unfold flatUnitWalk
  rw [←map_equiv (GridBoundary.gridWordEquiv n s),uniform_equiv]
  change wordWalkLaw _ _ _=_
  rw [wordWalkLaw_eq]
  exact congrArg (fun K => walkLaw K x n) (funext (unitBitStep_law r c))

lemma uniform_singleton_joint [Nonempty (PaperStates r c)]
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (fallback : (z : PaperStates r c) → PaperFibre r c z) :
    mapLaw (uniformLaw (α := PaperStates r c))
      (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c))=
        uniformLaw (α := PaperStateJoint r c) := by
  rw [mapLaw_deterministicJoint]
  have he (z : PaperStates r c) : pointLaw (fallback z)=uniformLaw (α := PaperFibre r c z) := by
    let : Subsingleton (PaperFibre r c z) :=
      PhysicalCompletionFibres.completionFibre_subsingleton _ _ _ _ _ _ _ hsmall
    exact pointLaw_eq_uniform _
  simp_rw [he]
  apply dependentJointLaw_uniform
  intro z
  simp only [uniformLaw,uniformMass,paperFibre_card_allSmall r c hsmall,
    Nat.cast_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]


def unitJointDraw (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n : ℕ) (bits : Fin (n*s) → Bool) : PaperStateJoint r c :=
  let z := flatUnitWalk r c x n bits
  ⟨z,fallback z⟩

lemma unitJointDraw_law (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (unitJointDraw r c fallback x n)=
      mapLaw (walkLaw (unitSmallStep r c) x n)
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c)) := by
  unfold unitJointDraw
  calc
    _ = mapLaw (mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (flatUnitWalk r c x n))
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c)) :=
      (mapLaw_comp _ (flatUnitWalk r c x n)
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c))).symm
    _ = _ := by rw [flatUnitWalk_law]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallOuter
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete finite rejection sampling when the large rectangle is empty -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "s" => smallProposalBits (I := I) (J := J)
local instance instDecidableEqPaperStates_3 : DecidableEq (PaperStates r c) := Classical.decEq _

/-- Each trial reads a disjoint word; failed trials use the feasible fallback. -/
def unitOuterDraw (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c)
    (bits : Fin (M*(n*s)) → Bool) : Table r c :=
  wordRetry (fun w => stateTrial r c (unitJointDraw r c fallback x n w)) z₀ M
    (GridBoundary.gridWordEquiv M (n*s) bits)

lemma unitOuterDraw_law (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c) :
    mapLaw (uniformLaw (α := Fin (M*(n*s)) → Bool))
      (unitOuterDraw r c fallback x n M z₀)=
      retryLaw (mapLaw (uniformLaw (α := Fin (n*s) → Bool))
        (unitJointDraw r c fallback x n)) (stateTrial r c) z₀ M := by
  unfold unitOuterDraw
  rw [←map_equiv (GridBoundary.gridWordEquiv M (n*s)),uniform_equiv]
  change wordRetryLaw _ _ _=_
  rw [wordRetryLaw_eq,←retryLaw_map]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitFiniteLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed all-small walk has the proved uniform sampling law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms FirstPaperPhysicalMarginal CompletionCounts
open FirstSuccess FairBits CompletionTranslation SmallContextCoordinates ResidualMixture
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

attribute [local irreducible] FirstSuccess.mapLaw

lemma mapped_walk_decidableEq_irrel {X Y : Type*} [Fintype X] [Fintype Y]
    (dX eX : DecidableEq X) (dY eY : DecidableEq Y)
    (K : X → RationalLaw X) (x : X) (n : ℕ) (f : X → Y) :
    @mapLaw X Y _ _ dY (@walkLaw X _ dX K x n) f=
      @mapLaw X Y _ _ eY (@walkLaw X _ eX K x n) f := by
  cases Subsingleton.elim dX eX
  cases Subsingleton.elim dY eY
  rfl

lemma unitCodeBitStep_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (unitCodeBitStep r c e x)=unitSmallStep r c x := by
  have hp := decodedCodeProposal_law r c e htotal x
  calc
    _ = mapLaw (mapLaw (uniformLaw (α := Fin s → Bool)) (decodedCodeProposal r c e x))
        (fun z => z.getD x) := (mapLaw_comp _ _ _).symm
    _ = mapLaw (smallProposalLaw r c x) (fun z => z.getD x) :=
      congrArg (fun p : RationalLaw (Option (PaperStates r c)) => mapLaw p (fun z => z.getD x))
        hp
    _ = _ := by
      unfold unitSmallStep proposalStayLaw smallProposalLaw
      exact mapLaw_decidableEq_irrel _ _ _ _

lemma flatUnitCodeWalk_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (flatUnitCodeWalk r c e x n)=
      walkLaw (unitSmallStep r c) x n := by
  unfold flatUnitCodeWalk
  rw [←map_equiv (GridBoundary.gridWordEquiv n s),uniform_equiv]
  change wordWalkLaw _ _ _=_
  rw [wordWalkLaw_eq]
  exact congrArg (fun K => walkLaw K x n) (funext (unitCodeBitStep_law r c e htotal))

lemma unitCodeJointDraw_law (htotal : (∑ i,r i)=∑ j,c j)
    (fallback : (z : PaperStates r c) → PaperFibre r c z) (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (unitCodeJointDraw r c e fallback x n)=
      mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (unitJointDraw r c fallback x n) := by
  calc
    _ = mapLaw (mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (flatUnitCodeWalk r c e x n))
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c)) :=
      (mapLaw_comp _ (flatUnitCodeWalk r c e x n)
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c))).symm
    _ = _ := by
      rw [flatUnitCodeWalk_law r c e htotal]
      exact (mapped_walk_decidableEq_irrel _ _ _ _ _ _ _ _).trans
        ((unitJointDraw_law r c fallback x n).symm.trans
          (mapLaw_decidableEq_irrel _ _ _ _))

lemma unitCodeOuterDraw_law (htotal : (∑ i,r i)=∑ j,c j)
    (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c) :
    mapLaw (uniformLaw (α := Fin (M*(n*s)) → Bool))
      (unitCodeOuterDraw r c e fallback x n M z₀)=
      mapLaw (uniformLaw (α := Fin (M*(n*s)) → Bool))
        (unitOuterDraw r c fallback x n M z₀) := by
  unfold unitCodeOuterDraw
  rw [←map_equiv (GridBoundary.gridWordEquiv M (n*s)),uniform_equiv]
  change wordRetryLaw _ _ _=_
  rw [wordRetryLaw_eq,←retryLaw_map,unitCodeJointDraw_law r c e htotal,unitOuterDraw_law]
  exact congrArg (fun p : RationalLaw (PaperStateJoint r c) =>
    retryLaw p (stateTrial r c) z₀ M) (mapLaw_decidableEq_irrel _ _ _ _)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitOutputSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstructing the original table when every cell is small -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open FirstPaperProfiles PaddedCompletions CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "L" => d^12

def unitOutputData (x : PaperStates r c) : OuterTableData :=
  outputData ((stateCodeData r c e x,L),[])

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the single computed sampler for arbitrary margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma law_uniform_of_subsingleton {Y : Type*} [Fintype Y] [Subsingleton Y]
    [Nonempty Y] (p : RationalLaw Y) : p=uniformLaw (α := Y) := by
  apply RationalLaw.ext
  funext y
  let : Unique Y := ⟨⟨y⟩,fun z => Subsingleton.elim z y⟩
  have ht : p.mass (default : Y)=1 := by simpa using p.total
  have hy : p.mass y=1 := (congrArg p.mass (Subsingleton.elim y default)).trans ht
  simp only [uniformLaw,uniformMass,Fintype.card_unique,Nat.cast_one,div_one,hy]

lemma variation_uniform_of_subsingleton {Y : Type*} [Fintype Y] [Subsingleton Y]
    [Nonempty Y] (p : RationalLaw Y) : variation p (uniformLaw (α := Y))=0 := by
  rw [law_uniform_of_subsingleton p,variation_self]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_OnlineCost
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def WorkBound {f : A→Experiment B} (F : Realizer f) (measure : A→ℕ) : Prop :=
  ∃ p : Polynomial ℕ,∀ a,F.cost a+(f a).worst weight≤p.eval (measure a)
abbrev PolynomialTime {f : A→Experiment B} (F : Realizer f) : Prop := WorkBound F weight
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

lemma symbolBits_length (a : Symbol) : (symbolBits a).length=18 := by
  simp only [symbolBits,List.length_append,List.length_reverse,List.length_singleton]
  change weight a+1=18
  rw [LiteralCodec.weight_symbol]
lemma chunk_length (a : Symbol) : (chunk a).length=18*width := by
  exact (flatMap_uniform_length (symbolBits a) (fun b=>block (letter b)) width
    (fun b=>block_length (letter b))).trans (congrArg (fun n=>n*width) (symbolBits_length a))

end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedInverse
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreePost

noncomputable def chunkFn (a : Symbol) : LiteralBlockMap.Block (18*width) :=
  fun i=>(chunk a)[i.val]'(by rw [chunk_length];exact i.isLt)
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCorrectionBudget
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cardinality and rare-branch precision for exact correction -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators
open CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

lemma table_card_binary_bound (r : I → ℕ) (c : J → ℕ) :
    Fintype.card (Table r c)≤
      2^((dimensionAllowance (I := I) (J := J))*smallBinaryLength r c) := by
  have hn : (∑ i,r i)+1≤2^(smallBinaryLength r c) := by
    apply (show (∑ i,r i)+1 ≤ stateBound r c+1 by unfold stateBound; omega).trans
    exact (smallBinaryLength_parameters r c).2.2
  have hdim : Fintype.card I*Fintype.card J≤dimensionAllowance (I := I) (J := J) := by
    unfold dimensionAllowance
    nlinarith
  calc
    _ ≤ ((∑ i,r i)+1)^(Fintype.card I*Fintype.card J) := table_card_le r c
    _ ≤ (2^(smallBinaryLength r c))^(Fintype.card I*Fintype.card J) := Nat.pow_le_pow_left hn _
    _ = 2^(smallBinaryLength r c*(Fintype.card I*Fintype.card J)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

lemma table_card_correction_bound (r : I → ℕ) (c : J → ℕ) :
    Fintype.card (Table r c)≤2^(correctionPrecision r c) := by
  apply (table_card_binary_bound r c).trans
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul (Nat.le_self_pow (by decide : 6≠0) _)
    (Nat.le_self_pow (by decide : 2≠0) _)

lemma correction_card_mass (r : I → ℕ) (c : J → ℕ) :
    (Fintype.card (Table r c):ℚ)*(1/(2:ℚ)^(correctionPrecision r c))≤1 := by
  rw [mul_one_div]
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast table_card_correction_bound r c

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_CompiledResidualCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residual correction for the compiled public draw -/

namespace ContingencyTables.SmallGraphProfiles
open ResidualMixture FirstSuccess CompletionCounts ProfilePrograms Algorithms
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "D" => correctionPrecision r c

lemma correctionPrecision_pos : 1≤D := by
  have hd : 1≤d := by unfold dimensionAllowance; omega
  have hb : 1 ≤ smallBinaryLength r c := hd.trans (smallBinaryLength_parameters r c).2.1
  exact Nat.mul_le_mul (one_le_pow₀ hd) (one_le_pow₀ hb)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedIntegerLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer transition counts for the actual outer-profile walk -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open CompletionCounts SmallContextCoordinates ResidualMixture FirstSuccess FairBits CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

lemma listedCompletionCounts_law (x : PaperStates r c) :
    (listedCompletionCounts r c hr hc b h hb x).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin f → Bool)) (listedPaddedDraw r c hr hc b h hb x) := by
  unfold listedCompletionCounts
  rw [IntegerLaw.toRational_equiv,paddedCanonicalCounts_law]
  unfold listedPaddedDraw listedDenseDraw
  rw [mapLaw_equiv_output]

lemma listedStepCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) :
    (listedStepCounts r c e hr hc b h hb x).toRational (by positivity)=
      listedSmallKernel r c hr hc b h hb x := by
  unfold listedStepCounts
  rw [IntegerLaw.toRational_booleanFinish _ _ _
    (listedCompletionCounts_law r c hr hc b h hb x)]
  have he : (fun bits : Fin (s+f) → Bool =>
      completionDecision R P x (decodedCodeProposal r c e x (splitWordEquiv s f bits).1)
        (paperListedEquiv r c hr hc x
          (listedPaddedDraw r c hr hc b h hb x (splitWordEquiv s f bits).2)))=
      listedBitStep r c e hr hc b h hb x := by
    funext bits
    rw [listed_completionDecision r c hr hc]
    rfl
  rw [he]
  exact listedBitStep_law r c e hr hc b h hb htotal x

attribute [local irreducible] listedStepCounts listedSmallKernel

attribute [local irreducible] listedWalkCounts

lemma listedWalkCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (N : ℕ) :
    (listedWalkCounts r c e hr hc b h hb x N).toRational (by positivity)=
      walkLaw (listedSmallKernel r c hr hc b h hb) x N := by
  unfold listedWalkCounts
  rw [IntegerLaw.toRational_walk]
  congr 1
  funext y
  exact listedStepCounts_law r c e hr hc b h hb htotal y

lemma listedTrialCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (N : ℕ) :
    (listedTrialCounts r c e hr hc b h hb x N).toRational (by positivity)=
      mapLaw (listedJointLaw r c hr hc b h hb x N) (stateTrial r c) := by
  unfold listedTrialCounts
  rw [IntegerLaw.toRational_bind _ _ (by positivity) (by positivity),
    listedWalkCounts_law r c e hr hc b h hb htotal]
  have hf (y : PaperStates r c) :
      ((listedCompletionCounts r c hr hc b h hb y).push
        (fun A => stateTrial r c ⟨y,A⟩)).toRational (by positivity)=
      mapLaw (listedFibreLaw r c hr hc b h hb y) (fun A => stateTrial r c ⟨y,A⟩) := by
    rw [IntegerLaw.toRational_push]
    exact congrArg (fun p => mapLaw p (fun A => stateTrial r c ⟨y,A⟩))
      (listedCompletionCounts_law r c hr hc b h hb y)
  have hk := funext hf
  rw [hk]
  apply RationalLaw.ext
  funext T
  simp only [mapLaw,listedJointLaw,listedFibreLaw,dependentJointLaw,bindLaw,
    Fintype.sum_sigma,Finset.mul_sum,mul_ite,mul_zero]

lemma listedOuterCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c)
    (N J : ℕ) (fallback : Table r c) :
    (listedOuterCounts r c e hr hc b h hb x N J fallback).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (J*(N*(s+f)+f)) → Bool))
        (listedOuterDraw r c e hr hc b h hb x N J fallback) := by
  unfold listedOuterCounts
  rw [IntegerLaw.toRational_retry _ (by positivity),
    listedTrialCounts_law r c e hr hc b h hb htotal,
    retryLaw_map,listedOuterDraw_law r c e hr hc b h hb htotal]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileBoxLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual adaptive profile walk embedded in its enumerable box -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] listedStepCounts profileIndex

/-- Invalid vectors get harmless stationary rows. Every actual profile
row is exactly the computed sampler transition transported to the box. -/
def profileBoxStep (k : BoxIndex) : IntegerLaw BoxIndex (2^(s+f)) :=
  (profileAt r c e k).elim (IntegerLaw.point (2^(s+f)) k)
    (fun x => (listedStepCounts r c e hr hc b h hb x).push (profileIndex r c e))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileMatrixSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed matrix is the actual profile transition law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] stateCode stateCodeData listedStepCounts listedCompletionCounts

def boxCode (k : BoxIndex) : List ℕ×List ℕ :=
  splitViews (q,List.ofFn
    (fun i => ((finFunctionFinEquiv.symm k : ProfileBox (m := m) (n := n) (q := q)) i).val))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitIntegerLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer counts for the all-small sampler's actual random words -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open FirstSuccess FairBits CompletionCounts ResidualMixture SmallContextCoordinates
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma unitStepCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) :
    (unitStepCounts r c e x).toRational (by positivity)=unitSmallStep r c x := by
  unfold unitStepCounts
  rw [IntegerLaw.toRational_push,IntegerLaw.toRational_boolean,unitCodeBitStep_law r c e htotal]

attribute [local irreducible] unitStepCounts unitSmallStep

attribute [local irreducible] unitWalkCounts

lemma unitWalkCounts_law (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (N : ℕ) :
    (unitWalkCounts r c e x N).toRational (by positivity)=walkLaw (unitSmallStep r c) x N := by
  unfold unitWalkCounts
  rw [IntegerLaw.toRational_walk _ (by positivity)]
  have he : (fun y => (unitStepCounts r c e y).toRational (by positivity))=unitSmallStep r c := by
    funext y
    exact unitStepCounts_law r c e htotal y
  exact congrArg (fun K => walkLaw K x N) he

lemma unitTrialCounts_law (htotal : ∑ i,r i=∑ j,c j)
    (hsmall : ∀ i j,paperSmall r c i j=true) (x : PaperStates r c) (N : ℕ) :
    (unitTrialCounts r c e hsmall x N).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (N*s) → Bool))
        (fun bits => stateTrial r c (unitCodeJointDraw r c e (allSmallFibre r c hsmall) x N bits)) := by
  unfold unitTrialCounts unitCodeJointDraw
  rw [IntegerLaw.toRational_push,unitWalkCounts_law r c e htotal,←flatUnitCodeWalk_law r c e htotal,
    mapLaw_comp]

lemma unitOuterCounts_law (htotal : ∑ i,r i=∑ j,c j)
    (hsmall : ∀ i j,paperSmall r c i j=true) (x : PaperStates r c) (N J : ℕ) (fallback : Table r c) :
    (unitOuterCounts r c e hsmall x N J fallback).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (J*(N*s)) → Bool))
        (unitCodeOuterDraw r c e (allSmallFibre r c hsmall) x N J fallback) := by
  unfold unitOuterCounts unitCodeOuterDraw
  rw [IntegerLaw.toRational_retry _ (by positivity),unitTrialCounts_law r c e htotal]
  rw [←map_equiv (GridBoundary.gridWordEquiv J (N*s)),uniform_equiv]
  rw [retryLaw_map]
  exact (wordRetryLaw_eq
    (fun bits : Fin (N*s) → Bool => stateTrial r c
      (unitCodeJointDraw r c e (allSmallFibre r c hsmall) x N bits)) fallback J).symm

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitBoxLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual adaptive profile walk embedded in its enumerable box -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] unitStepCounts profileIndex

/-- Invalid vectors get harmless stationary rows. Every actual profile
row is exactly the computed sampler transition transported to the box. -/
def unitBoxStep (k : BoxIndex) : IntegerLaw BoxIndex (2^(s)) :=
  (profileAt r c e k).elim (IntegerLaw.point (2^(s)) k)
    (fun x => (unitStepCounts r c e x).push (profileIndex r c e))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ResidualEnumerationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The completion boxes used at arbitrary enumerated profiles -/

namespace ContingencyTables.ProfilePrograms
open DensePrograms

def profilePaddingData (row : Bool) (z : ProfileCheckData×ℕ) : PaddingData :=
  let view := if row then z.1.1.1.2.1 else complementValues (z.1.2,z.1.1.1.2.2)
  let line : MarginCheckData := (((z.1.1.1.1,view),z.1.1.2),z.1.2)
  (line,z.2)

end ContingencyTables.ProfilePrograms

end OAI
end


