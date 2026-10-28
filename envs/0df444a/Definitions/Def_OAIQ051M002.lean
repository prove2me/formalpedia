-- Prove2me | Definitions.Def_OAIQ051M002
-- name    : OAIQ051M002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:25:45.586771+00:00
-- url     : https://prove2.me/theorems/fb65fec1-db6a-4678-9fa6-0b6e839e5eb5
-- title:
--   Definitions bundle OAIQ051M002 of the split of OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 706 declarations of OpenAI's Lean: 657 definitions, 2 inductive types or structures, 4 instances and 43 theorems. The definitions and types are `OAI.MatchingFPRAS.ExecutableAdaptive.cellDataRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.coolingRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.estimateCell`, `OAI.MatchingFPRAS.ExecutableAdaptive.estimateCellRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.estimateMatrix`, `OAI.MatchingFPRAS.ExecutableAdaptive.estimateMatrixRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.estimateRow`, `OAI.MatchingFPRAS.ExecutableAdaptive.estimateRowRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.graphRep`, `OAI.MatchingFPRAS.ExecutableAdaptive.multiplyVector`, `OAI.MatchingFPRAS.ExecutableAdaptive.multiplyVectorRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.orderedPairRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.probeValue`, `OAI.MatchingFPRAS.ExecutableAdaptive.probeValueRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.rawCell`, `OAI.MatchingFPRAS.ExecutableAdaptive.rawCellRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.stageCell`, `OAI.MatchingFPRAS.ExecutableAdaptive.stageCellRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.stageMatrix`, `OAI.MatchingFPRAS.ExecutableAdaptive.stageMatrixRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.stageRow`, `OAI.MatchingFPRAS.ExecutableAdaptive.stageRowRealizer`, `OAI.MatchingFPRAS.ExecutableAdaptive.updateVector`, `OAI.MatchingFPRAS.ExecutableAdaptive.updateVectorRealizer`, `OAI.MatchingFPRAS.ExecutableBottleneck.Matrix`, `OAI.MatchingFPRAS.ExecutableBottleneck.advance`, `OAI.MatchingFPRAS.ExecutableBottleneck.advanceRealizer`, `OAI.MatchingFPRAS.ExecutableBottleneck.cell`, `OAI.MatchingFPRAS.ExecutableBottleneck.cellRealizer`, `OAI.MatchingFPRAS.ExecutableBottleneck.close`, `OAI.MatchingFPRAS.ExecutableBottleneck.closeRealizer`, `OAI.MatchingFPRAS.ExecutableBottleneck.entry`, `OAI.MatchingFPRAS.ExecutableBottleneck.entryRealizer`, `OAI.MatchingFPRAS.ExecutableBottleneck.matrixRep`, `OAI.MatchingFPRAS.ExecutableBottleneck.one`, `OAI.MatchingFPRAS.ExecutableBottleneck.seed`, `OAI.MatchingFPRAS.ExecutableBottleneck.seedEntry`, `OAI.MatchingFPRAS.ExecutableBottleneck.seedEntryRealizer`, `OAI.MatchingFPRAS.ExecutableBottleneck.seedRealizer`, `OAI.MatchingFPRAS.ExecutableBottleneck.squareRealizer` and 619 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/MatchingCount, in whole or in part: `MatchingCount_Algorithm_TreeEstimator`, `MatchingCount_Algorithm_TreeGeneratedCertificate`, `MatchingCount_Algorithm_TreeGeneratedMarked`, `MatchingCount_Algorithm_TreeGeneratedPrepared`, `MatchingCount_Algorithm_TreeGeneratedStage`, `MatchingCount_Algorithm_TreeGeneratedUpdate`, `MatchingCount_Algorithm_TreeNumericStatistics`, `MatchingCount_Algorithm_TreeObservables`, `MatchingCount_Algorithm_TreeReweight`, `MatchingCount_Algorithm_TreeReweightTable`, `MatchingCount_Algorithm_TreeScaling`, `MatchingCount_Algorithm_TreeScalingCorrect`, `MatchingCount_Algorithm_TreeStageActivity`, `MatchingCount_Algorithm_TreeTierWeights`, `MatchingCount_Algorithm_TreeWeights`, `MatchingCount_Arithmetic_BinarySubtract`, `MatchingCount_Arithmetic_TreeAdaptiveArithmetic`, `MatchingCount_Arithmetic_TreeCompare`, `MatchingCount_Arithmetic_TreeDyadic`, `MatchingCount_Arithmetic_TreeFraction`, `MatchingCount_Arithmetic_TreeFractionExtra`, `MatchingCount_Arithmetic_TreeGCD`, `MatchingCount_Arithmetic_TreeNatDivision`, `MatchingCount_Arithmetic_TreeNumberOps`, `MatchingCount_Arithmetic_TreeStateNormalize`, `MatchingCount_Arithmetic_TreeSubtract`, `MatchingCount_Complexity_TreeChoiceCosts`, `MatchingCount_Complexity_TreePolynomial`, `MatchingCount_Complexity_TreePolynomialGrid`, `MatchingCount_Graphs_Related`, `MatchingCount_Graphs_Related2`, `MatchingCount_Graphs_TreeBagBuild`, `MatchingCount_Graphs_TreeBagTable`, `MatchingCount_Graphs_TreeBags`, `MatchingCount_Graphs_TreeCycleTable`, `MatchingCount_Graphs_TreeGeometry`, `MatchingCount_Graphs_TreeHeight`, `MatchingCount_Graphs_TreeHierarchyRoot`, `MatchingCount_Graphs_TreeMatchingCheck`, `MatchingCount_Graphs_TreeProfile`, `MatchingCount_Graphs_TreeRankPlan`, `MatchingCount_Graphs_TreeSwitchRaw`, `MatchingCount_Graphs_TreeSwitchValid`, `MatchingCount_Machines_TreeBindings`, `MatchingCount_Machines_TreeBottleneck`, `MatchingCount_Machines_TreeBottleneckCorrect`, `MatchingCount_Machines_TreeBuild`, `MatchingCount_Machines_TreeCanonical`, `MatchingCount_Machines_TreeCappedAssembly`, `MatchingCount_Machines_TreeCertify`, `MatchingCount_Machines_TreeChoice`, `MatchingCount_Machines_TreeClippedRun`, `MatchingCount_Machines_TreeColex`, `MatchingCount_Machines_TreeColor`, `MatchingCount_Machines_TreeColorRaw`, `MatchingCount_Machines_TreeFastChoose`, `MatchingCount_Machines_TreeFastLookup`, `MatchingCount_Machines_TreeFinite`, `MatchingCount_Machines_TreeFiniteCollections`, `MatchingCount_Machines_TreeFiniteOps`, `MatchingCount_Machines_TreeFold`, `MatchingCount_Machines_TreeGuideTables`, `MatchingCount_Machines_TreeIndex`, `MatchingCount_Machines_TreeInitial`, `MatchingCount_Machines_TreeLabelTable`, `MatchingCount_Machines_TreeList`, `MatchingCount_Machines_TreeListMore`, `MatchingCount_Machines_TreeListOps`, `MatchingCount_Machines_TreeMarkTable`, `MatchingCount_Machines_TreeMatrix`, `MatchingCount_Machines_TreeNaturalComb`, `MatchingCount_Machines_TreeParentTable`, `MatchingCount_Machines_TreePartialChoice`, `MatchingCount_Machines_TreePhantom`, `MatchingCount_Machines_TreePortion`, `MatchingCount_Machines_TreePredicate`, `MatchingCount_Machines_TreeQuad`, `MatchingCount_Machines_TreeQuadDistinct`, `MatchingCount_Machines_TreeRationalWeight`, `MatchingCount_Machines_TreeReach`, `MatchingCount_Machines_TreeReachCorrect`, `MatchingCount_Machines_TreeRefreshCatalog`, `MatchingCount_Machines_TreeRefreshIndexed`, `MatchingCount_Machines_TreeRefreshNumbered`, `MatchingCount_Machines_TreeRefreshTables`, `MatchingCount_Machines_TreeRepeat`, `MatchingCount_Machines_TreeSlotWeight`, `MatchingCount_Machines_TreeStart`, `MatchingCount_Machines_TreeStateTable`, `MatchingCount_Machines_TreeSum`, `MatchingCount_Machines_TreeTyped`, `MatchingCount_Machines_TreeWeightTable`, `MatchingCount_Probability_AdaptiveLaw`, `MatchingCount_Sampling_Endpoints2`, `MatchingCount_Sampling_TreeCategorical`, `MatchingCount_Sampling_TreeClippedDP`, `MatchingCount_Sampling_TreeDPCounts`, `MatchingCount_Sampling_TreeDPEntry`, `MatchingCount_Sampling_TreeFastDPEntry`, `MatchingCount_Sampling_TreeFastDescent`, `MatchingCount_Sampling_TreeFastSample`, `MatchingCount_Sampling_TreeFastUnit`, `MatchingCount_Sampling_TreeIndexedPair`, `MatchingCount_Sampling_TreeIndexedPairCorrect`, `MatchingCount_Sampling_TreeIndexedPairPost`, `MatchingCount_Sampling_TreeIndexedPairUniform`, `MatchingCount_Sampling_TreeLocalSampler`, `MatchingCount_Sampling_TreeMarking`, `MatchingCount_Sampling_TreeNumericLadder`, `MatchingCount_Sampling_TreeNumericMarking`, `MatchingCount_Sampling_TreeOptions`, `MatchingCount_Sampling_TreeOptionsAccept`, `MatchingCount_Sampling_TreeOptionsFinite`, `MatchingCount_Sampling_TreePairStep`, `MatchingCount_Sampling_TreePairTable`, `MatchingCount_Sampling_TreePrepareLadder`, `MatchingCount_Sampling_TreePreparedMarked`, `MatchingCount_Sampling_TreeProbe`, `MatchingCount_Sampling_TreeScan`, `MatchingCount_Sampling_TreeScanChoice`, `MatchingCount_Sampling_TreeScanRun`, `MatchingCount_Sampling_TreeUnitAssemble`, `MatchingCount_Sampling_TreeUnitBranch`, `MatchingCount_Sampling_TreeUnitDraw`, `MatchingCount_Tapes_TreeNumberedCodec`, `MatchingCount_Tapes_TreeSparseCertificate`, `MatchingCount_Tapes_TreeSparseComponents`, `MatchingCount_Tapes_TreeSparseNeighbors`, `MatchingCount_Tapes_TreeSparseStage`.
--
--   **Imports.** It imports the published bundle `Def_MatchingFPRAS`; the bundles `OAIQ051M000` and `OAIQ051M001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ051M004`.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/MatchingCount at commit adc7f12

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M000
import Definitions.Def_OAIQ051M001

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Related
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Hierarchy

variable {V : Type*} [Fintype V]

variable (B : V → V → ℝ)

variable (hsym : ∀ a b, B a b = B b a)

variable (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)

def Mem {H : ℕ} (l : Label B hsym htri H) (x : V) : Prop := Quotient.mk _ x = l.2

end MatchingFPRAS.Hierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeNumberOps
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeBits
open Turing MachineCost RegisterProc BinaryNormalize TreeData

lemma encodeForward_exec (A C : List Bool) :
    Exec encodeForward ![A,[],C] ![encode (bits A),[],C] (2*A.length+3) := by
  have h₁:=reverseRaw_exec A [] C
  simp only [List.append_nil] at h₁
  have h₂ : Exec (atom (.push (0 : Fin 3) (fun _=>false) .halt))
      ![[],A.reverse,C] ![[false],A.reverse,C] 1 := by
    apply exec_atom
    simp only [TM2.stepAux]
    congr 1
    funext i; fin_cases i <;> simp
  have h₃:=reindex_swap encodeRaw A.reverse [false] C [] _ C _ (encodeRaw_exec A C)
  apply (h₁.seq (h₂.seq h₃)).mono
  omega
end MatchingFPRAS.TreeBits

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

theorem add_exec (E : Env R) (i j : R) (hij : i≠j) (m n : ℕ)
    (hm : E i=nat m) (hn : E j=nat n) :
    Exec (add i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (m+n)) .nil))
      (9*(m.bits.length+n.bits.length)+20) := by
  let A:=m.bits
  let B:=n.bits
  let S:=StackAddition.addDigits false A B
  have h₁:=on_left TreeBits.decodeForward E i j hij (TreeData.encode (bits A)) (TreeData.encode (bits B)) A _
    (TreeBits.decodeForward_exec A [])
  have h₂:=on_right TreeBits.decodeForward E i j hij A (TreeData.encode (bits B)) B _
    (TreeBits.decodeForward_exec B [])
  have h₃:=on_pair BinaryArithmeticProc.add E i j hij A B S [] _ (BinaryArithmeticProc.add_exec A B)
  have h₄:=on_left BinaryNormalize.program E i j hij S [] (BinaryNormalize.normalize S) _
    (BinaryNormalize.exec S [])
  have h₅:=on_left TreeBits.encodeForward E i j hij (BinaryNormalize.normalize S) []
    (TreeData.encode (bits (BinaryNormalize.normalize S))) _ (TreeBits.encodeForward_exec _ [])
  have h₆ : Exec (atom (.push (.inl j) (fun _=>false) .halt))
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [])
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [false]) 1 := by
    apply exec_atom
    simp only [TM2.stepAux,rawPair_right]
    congr 1
    simp [rawPair]
  have hh:=h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  have hS : BinaryNormalize.normalize S=(m+n).bits := by
    rw [BinaryNormalize.normalize_bits,StackAddition.addition_numerals]
  rw [hS] at hh
  have hstart : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    change rawPair E i j (TreeData.encode (nat m)) (TreeData.encode (nat n))=encodeEnv E
    rw [←hm,←hn]
    exact rawPair_same E i j
  have hend : rawPair E i j (TreeData.encode (bits (m+n).bits)) [false]=
      encodeEnv (putPair E i j (nat (m+n)) .nil) := rawPair_encode E i j (nat (m+n)) .nil
  rw [hstart,hend] at hh
  apply hh.mono
  have hl:=StackAddition.addDigits_length A B false
  have hl' := BinaryNormalize.normalize_length S
  rw [hS] at hl'
  dsimp only [A,B,S] at hl hl' ⊢
  omega
end MatchingFPRAS.TreeArithmetic

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeCompare
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

def less (i j : R) (hij : i≠j) : Proc (K R) :=
  seq (decode i) (seq (decode j) (seq (reindex BinaryArithmeticProc.less (pairEmbedding i j hij))
    (atom (.push (.inl j) (fun _=>false) .halt))))

theorem less_bits_exec (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool)
    (hi : E i=bits A) (hj : E j=bits B) :
    Exec (less i j hij) (encodeEnv E)
      (encodeEnv (putPair E i j (bit (decide (StackAddition.value A<StackAddition.value B))) .nil))
      (3*(A.length+B.length)+7) := by
  have h₁:=on_left TreeBits.decodeForward E i j hij (TreeData.encode (bits A)) (TreeData.encode (bits B)) A _
    (TreeBits.decodeForward_exec A [])
  have h₂:=on_right TreeBits.decodeForward E i j hij A (TreeData.encode (bits B)) B _
    (TreeBits.decodeForward_exec B [])
  have h₃:=on_pair BinaryArithmeticProc.less E i j hij A B _ [] _ (BinaryArithmeticProc.less_exec A B)
  have h₄ : Exec (atom (.push (.inl j) (fun _=>false) .halt))
      (rawPair E i j (TreeData.encode (bit (decide (StackAddition.value A<StackAddition.value B)))) [])
      (rawPair E i j (TreeData.encode (bit (decide (StackAddition.value A<StackAddition.value B)))) [false]) 1 := by
    apply exec_atom
    simp only [TM2.stepAux,rawPair_right]
    congr 1
    simp [rawPair]
  have hh:=h₁.seq (h₂.seq (h₃.seq h₄))
  have hs : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    rw [←hi,←hj]; exact rawPair_same E i j
  have he : rawPair E i j (TreeData.encode (bit (decide (StackAddition.value A<StackAddition.value B)))) [false]=
      encodeEnv (putPair E i j (bit (decide (StackAddition.value A<StackAddition.value B))) .nil) :=
    rawPair_encode E i j _ .nil
  rw [hs,he] at hh
  exact hh.mono (by omega)

lemma less_exec (E : Env R) (i j : R) (hij : i≠j) (m n : ℕ)
    (hi : E i=nat m) (hj : E j=nat n) :
    Exec (less i j hij) (encodeEnv E) (encodeEnv (putPair E i j (bit (decide (m<n))) .nil))
      (3*(m.bits.length+n.bits.length)+7) := by
  simpa only [StackAddition.value_bits] using less_bits_exec E i j hij m.bits n.bits hi hj
end MatchingFPRAS.TreeArithmetic

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeTyped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

export Codec (encode)

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def second : Realizer (Prod.snd : A×B → B) where
  program := seq (TreeFunction.split 1 0 (by decide)) (TreeFunction.clear 1)
  cost := fun ab=>3*TreeFunction.size (encode ab.1)+7
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (encode a) (encode b) .nil s
    have h2:=clear1 (encode b) (encode a) s
    apply (h1.seq h2).mono
    simp only [size_nil]; omega

def add : Realizer (fun ab : ℕ×ℕ=>ab.1+ab.2) where
  program := seq (TreeFunction.split 1 0 (by decide)) (TreeArithmetic.add 0 1 (by decide))
  cost := fun ab=>2*TreeFunction.size (nat ab.1)+5+9*(ab.1.bits.length+ab.2.bits.length)+20
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (nat a) (nat b) .nil s
    have h2:=TreeArithmetic.add_exec (env (nat b) (nat a) s) 0 1 (by decide) b a rfl rfl
    rw [putPair,env_update0,env_update1,Nat.add_comm b a] at h2
    apply (h1.seq h2).mono
    simp only [size_nil]
    omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def less : Realizer (fun ab : ℕ×ℕ=>decide (ab.1<ab.2)) where
  program := seq (TreeFunction.split 1 0 (by decide))
    (seq (TreeArithmetic.less 1 0 (by decide))
      (seq (TreeFunction.copy 1 0 (by decide)) (TreeFunction.clear 1)))
  cost := fun ab=>2*TreeFunction.size (nat ab.1)+3*(ab.1.bits.length+ab.2.bits.length)+31
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (nat a) (nat b) .nil s
    have h2:=TreeArithmetic.less_exec (env (nat b) (nat a) s) 1 0 (by decide) a b rfl rfl
    simp only [putPair,env_update0,env_update1] at h2
    have h3:=copy10 .nil (bit (decide (a<b))) s
    have h4:=clear1 (bit (decide (a<b))) (bit (decide (a<b))) s
    apply (h1.seq (h2.seq (h3.seq h4))).mono
    have hs : TreeFunction.size (bit (decide (a<b))) ≤ 3 := by
      cases decide (a<b) <;> simp [bit]
    simp only [size_nil]; omega

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]
namespace Fold
open RegisterControl (Instr Runs Effect)

def code (P : Proc (K Reg)) : Point → RegisterControl.Instr Reg Point
  | .loop => .call (TreeFunction.split 1 0 (by decide)) .check
  | .check => .branch 1 .halt .splitHead
  | .splitHead => .call (TreeFunction.split 3 1 (by decide)) .pushTail
  | .pushTail => .call (TreeFunction.cons 1 2 (by decide)) .pushArgs
  | .pushArgs => .call (TreeFunction.cons 3 0 (by decide)) .body
  | .body => .call P .popTail
  | .popTail => .call (TreeFunction.split 1 2 (by decide)) .rebuild
  | .rebuild => .call (TreeFunction.cons 1 0 (by decide)) .loop
  | .halt => .halt

lemma splitHeads (a b r s : Data) :
    Exec (TreeFunction.split 3 1 (by decide)) (encodeEnv (env b (.cons a r) s)) (encodeEnv (heads a b r s))
      (2*TreeFunction.size a+5) := by
  have hh := split_exec (env b (.cons a r) s) 3 1 (by decide) () a r rfl
  have he : putPair (env b (.cons a r) s) 3 1 a r=heads a b r s := by
    funext i; fin_cases i <;> simp [heads,putPair,env]
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try rfl
  simp [TreeFunction.size,env,TreeData.encode]
  omega
lemma pushTail (a b r s : Data) :
    Exec (TreeFunction.cons 1 2 (by decide)) (encodeEnv (heads a b r s)) (encodeEnv (heads a b .nil (.cons r s)))
      (2*TreeFunction.size r+3) := by
  have hh := cons_exec (heads a b r s) 1 2 (by decide) ()
  have he : putPair (heads a b r s) 1 2 .nil (.cons (heads a b r s 1) (heads a b r s 2))=
      heads a b .nil (.cons r s) := by
    funext i; fin_cases i <;> simp [heads,putPair,env]
  rw [he] at hh
  exact hh
lemma pushArgs (a b r s : Data) :
    Exec (TreeFunction.cons 3 0 (by decide)) (encodeEnv (heads a b .nil (.cons r s)))
      (encodeEnv (env (.cons a b) .nil (.cons r s))) (2*TreeFunction.size a+3) := by
  have hh := cons_exec (heads a b .nil (.cons r s)) 3 0 (by decide) ()
  have he : putPair (heads a b .nil (.cons r s)) 3 0 .nil
      (.cons (heads a b .nil (.cons r s) 3) (heads a b .nil (.cons r s) 0))=
      env (.cons a b) .nil (.cons r s) := by
    funext i; fin_cases i <;> simp [heads,putPair,env]
  rw [he] at hh
  exact hh

def cost (f : A×B → B) (t : A×B → ℕ) : List A → B → ℕ
  | [],_ => 10
  | a::as,b => t (a,b)+6*TreeFunction.size (encode a)+8*TreeFunction.size (encode as)+34+cost f t as (f (a,b))

lemma runs {f : A×B → B} (F : Realizer f) (as : List A) (b : B) (s : Data) :
    Runs (code F.program) (some Point.loop) (env (encode (as,b)) .nil s)
      (env (encode (as.foldl (fun b a=>f (a,b)) b)) .nil s) (cost f F.cost as b) := by
  induction as generalizing b with
  | nil =>
    have hh : Runs (code F.program) (some Point.halt) (env (encode b) .nil s) (env (encode b) .nil s) 1 :=
      Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
    have hc : Runs (code F.program) (some Point.check) (env (encode b) .nil s) (env (encode b) .nil s) 2 :=
      Runs.step _ _ _ _ _ 1 1 (Effect.nilBranch _ 1 _ _ rfl) hh
    have hs:=split10 .nil (encode b) .nil s
    have hs' : Exec (TreeFunction.split 1 0 (by decide)) (encodeEnv (env (encode (([] : List A),b)) .nil s))
        (encodeEnv (env (encode b) .nil s)) 7 := by simpa [size_nil,encode_prod,encode_list_nil] using hs
    exact Runs.step _ _ _ _ _ 2 8 (Effect.call _ _ _ _ 7 hs') hc
  | cons a as ih =>
    let z:=as.foldl (fun b a=>f (a,b)) (f (a,b))
    let sa:=TreeFunction.size (encode a)
    let sr:=TreeFunction.size (encode as)
    let rest:=cost f F.cost as (f (a,b))
    have hr := ih (f (a,b))
    have h1:=cons10 (encode (f (a,b))) (encode as) s
    have hreb : Runs (code F.program) (some Point.rebuild) (env (encode (f (a,b))) (encode as) s)
        (env (encode z) .nil s) ((2*sr+4)+rest) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h1) hr
    have h2 := (split12 (encode (f (a,b))) .nil (encode as) s).mono
      (show TreeFunction.size Data.nil+2*TreeFunction.size (encode as)+4 ≤ 2*sr+5 by
        change 1+2*sr+4 ≤ 2*sr+5
        omega)
    have hpop : Runs (code F.program) (some Point.popTail) (env (encode (f (a,b))) .nil (.cons (encode as) s))
        (env (encode z) .nil s) ((2*sr+6)+((2*sr+4)+rest)) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h2) hreb
    have h3:=F.correct (a,b) (.cons (encode as) s)
    have hbody : Runs (code F.program) (some Point.body) (env (encode (a,b)) .nil (.cons (encode as) s))
        (env (encode z) .nil s) ((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h3) hpop
    have h4:=pushArgs (encode a) (encode b) (encode as) s
    have ha : Runs (code F.program) (some Point.pushArgs) (heads (encode a) (encode b) .nil (.cons (encode as) s))
        (env (encode z) .nil s) ((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest)))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h4) hbody
    have h5:=pushTail (encode a) (encode b) (encode as) s
    have ht : Runs (code F.program) (some Point.pushTail) (heads (encode a) (encode b) (encode as) s)
        (env (encode z) .nil s) ((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest))))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h5) ha
    have h6:=splitHeads (encode a) (encode b) (encode as) s
    have hsh : Runs (code F.program) (some Point.splitHead) (env (encode b) (encode (a::as)) s)
        (env (encode z) .nil s) ((2*sa+6)+((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest)))))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h6) ht
    have hc : Runs (code F.program) (some Point.check) (env (encode b) (encode (a::as)) s)
        (env (encode z) .nil s) (1+((2*sa+6)+((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest))))))) :=
      Runs.step _ _ _ _ _ _ 1 (Effect.consBranch _ 1 _ _ (encode a) (encode as) rfl) hsh
    have h7 := (split10 (encode (a::as)) (encode b) .nil s).mono
      (show TreeFunction.size Data.nil+2*TreeFunction.size (encode (a::as))+4 ≤ 2*TreeFunction.size (encode (a::as))+5 by
        change 1+2*TreeFunction.size (encode (a::as))+4 ≤ 2*TreeFunction.size (encode (a::as))+5
        omega)
    have hl : Runs (code F.program) (some Point.loop) (env (encode (a::as,b)) .nil s)
        (env (encode z) .nil s) ((2*TreeFunction.size (encode (a::as))+6)+(1+((2*sa+6)+((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest)))))))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h7) hc
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try rfl
    simp only [cost,encode_list_cons,size_cons,sa,sr,rest]
    ring
end Fold

def fold {f : A×B → B} (F : Realizer f) : Realizer (fun ab : List A×B=>ab.1.foldl (fun b a=>f (a,b)) ab.2) where
  program := RegisterControl.compile (Fold.code F.program)
  cost := fun ab=>Fold.cost f F.cost ab.1 ab.2
  correct := fun ab s=>RegisterControl.compile_exec _ _ _ _ (Fold.runs F ab.1 ab.2 s)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def listCons : Realizer (fun ab : A×List A=>ab.1::ab.2) :=
  ⟨atom .halt,fun _=>1,fun _ _=>exec_atom .halt _ _ rfl⟩

def reverse : Realizer (List.reverse : List A → List A) :=
  (composition (pair identity (constant ([] : List A))) (fold listCons)).congr (by
    intro as
    change as.foldl (fun x y=>y::x) []=as.reverse
    simp)

def toBits : Realizer Nat.bits :=
  ⟨atom .halt,fun _=>1,fun _ _=>exec_atom .halt _ _ rfl⟩

def double : Realizer (fun n : ℕ=>2*n) :=
  (composition (pair identity identity) add).congr (fun value=>by
    change value+value=2*value
    omega)

def mulStepRealizer : Realizer mulStep := by
  let bitP : Realizer (fun x : Bool×(ℕ×ℕ)=>x.1) := first
  let nP : Realizer (fun x : Bool×(ℕ×ℕ)=>x.2.1) := composition second first
  let cP : Realizer (fun x : Bool×(ℕ×ℕ)=>x.2.2) := composition second second
  let vP:=choose bitP nP (constant 0)
  let sumP:=composition (pair (composition cP double) vP) add
  exact (pair nP sumP).congr (fun _=>rfl)

lemma mulStep_fold (A : List Bool) (n c : ℕ) :
    A.reverse.foldl (fun z b=>mulStep (b,z)) (n,c)=
      (n,c*2^A.length+StackAddition.value A*n) := by
  induction A generalizing c with
  | nil => simp [StackAddition.value]
  | cons b A ih =>
    simp only [List.reverse_cons,List.foldl_append,ih,List.foldl_cons,List.foldl_nil,List.length_cons]
    cases b <;> simp only [mulStep,Bool.false_eq_true,↓reduceIte,StackAddition.value,
      Bool.toNat_false,Bool.toNat_true,Nat.zero_add,pow_succ] <;> congr 1 <;> ring

def multiply : Realizer (fun ab : ℕ×ℕ=>ab.1*ab.2) := by
  let bitsP : Realizer (fun ab : ℕ×ℕ=>ab.1.bits.reverse) := composition (composition first toBits) reverse
  let startP : Realizer (fun ab : ℕ×ℕ=>(ab.2,0)) := pair second (constant 0)
  let foldP:=composition (pair bitsP startP) (fold mulStepRealizer)
  exact (composition foldP second).congr (by
    intro ab
    change (ab.1.bits.reverse.foldl (fun z b=>mulStep (b,z)) (ab.2,0)).2=ab.1*ab.2
    rw [mulStep_fold]
    simp [StackAddition.value_bits])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_BinarySubtract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackSubtract
open Turing MachineCost StackAddition

lemma digit_balance (c a b : Bool) :
    a.toNat+2*(borrow c a b).toNat=(digit c a b).toNat+b.toNat+c.toNat := by
  cases c <;> cases a <;> cases b <;> decide

lemma subDigits_balance (A B : List Bool) (c : Bool) :
    value A+2^(max A.length B.length)*(subDigits c A B).1.toNat=
      value (subDigits c A B).2+value B+c.toNat := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => simp [subDigits,value]
    | cons b B ih =>
      have hh:=ih (borrow c false b)
      have hd:=digit_balance c false b
      simp only [List.length_nil,Nat.zero_max,value] at hh
      simp only [subDigits,List.length_nil,List.length_cons,Nat.zero_max,value,pow_succ,
        Bool.toNat_false] at hd ⊢
      nlinarith
  | cons a A ih =>
    cases B with
    | nil =>
      have hh:=ih [] (borrow c a false)
      have hd:=digit_balance c a false
      simp only [List.length_nil,Nat.max_zero,value] at hh
      simp only [subDigits,List.length_nil,List.length_cons,Nat.max_zero,value,pow_succ,
        Bool.toNat_false] at hd ⊢
      nlinarith
    | cons b B =>
      have hh:=ih B (borrow c a b)
      have hd:=digit_balance c a b
      simp only [subDigits,List.length_cons,max_add_add_right,value,pow_succ]
      nlinarith

lemma value_lt (A : List Bool) : value A<2^A.length := by
  induction A with
  | nil => simp [value]
  | cons a A ih =>
    have ha : a.toNat≤1 := by cases a <;> decide
    simp only [value,List.length_cons,pow_succ]
    omega

lemma subDigits_correct (A B : List Bool) (c : Bool) (h : value B+c.toNat≤value A) :
    (subDigits c A B).1=false ∧ value (subDigits c A B).2=value A-value B-c.toNat := by
  have hh:=subDigits_balance A B c
  have hl:=value_lt (subDigits c A B).2
  rw [subDigits_length] at hl
  cases hc : (subDigits c A B).1 with
  | false => simp only [hc,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hh; exact ⟨rfl,by omega⟩
  | true => simp only [hc,Bool.toNat_true,Nat.mul_one] at hh; omega

end MatchingFPRAS.StackSubtract

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeSubtract
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

def sub (i j : R) (hij : i≠j) : Proc (K R) :=
  seq (decode i) (seq (decode j)
    (seq (reindex BinaryArithmeticProc.sub (pairEmbedding i j hij))
      (seq (normalize i) (seq (encode i) (atom (.push (.inl j) (fun _=>false) .halt))))))

theorem sub_bits_exec (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool)
    (hm : E i=bits A) (hn : E j=bits B) (hle : StackAddition.value B≤StackAddition.value A) :
    Exec (sub i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (StackAddition.value A-StackAddition.value B)) .nil))
      (9*(A.length+B.length)+20) := by
  let S:=(StackSubtract.subDigits false A B).2
  have h₁:=on_left TreeBits.decodeForward E i j hij (TreeData.encode (bits A)) (TreeData.encode (bits B)) A _
    (TreeBits.decodeForward_exec A [])
  have h₂:=on_right TreeBits.decodeForward E i j hij A (TreeData.encode (bits B)) B _
    (TreeBits.decodeForward_exec B [])
  have h₃:=on_pair BinaryArithmeticProc.sub E i j hij A B S [] _ (BinaryArithmeticProc.sub_exec A B)
  have h₄:=on_left BinaryNormalize.program E i j hij S [] (BinaryNormalize.normalize S) _
    (BinaryNormalize.exec S [])
  have h₅:=on_left TreeBits.encodeForward E i j hij (BinaryNormalize.normalize S) []
    (TreeData.encode (bits (BinaryNormalize.normalize S))) _ (TreeBits.encodeForward_exec _ [])
  have h₆ : Exec (atom (.push (.inl j) (fun _=>false) .halt))
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [])
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [false]) 1 := by
    apply exec_atom
    simp only [TM2.stepAux,rawPair_right]
    congr 1
    simp [rawPair]
  have hh:=h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  have hS : BinaryNormalize.normalize S=(StackAddition.value A-StackAddition.value B).bits := by
    rw [BinaryNormalize.normalize_bits]
    congr 1
    simpa only [Bool.toNat_false,Nat.add_zero,Nat.sub_zero] using
      (StackSubtract.subDigits_correct A B false (by simpa using hle)).2
  rw [hS] at hh
  have hstart : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    rw [←hm,←hn]
    exact rawPair_same E i j
  have hend : rawPair E i j (TreeData.encode (bits (StackAddition.value A-StackAddition.value B).bits)) [false]=
      encodeEnv (putPair E i j (nat (StackAddition.value A-StackAddition.value B)) .nil) := rawPair_encode E i j (nat (StackAddition.value A-StackAddition.value B)) .nil
  rw [hstart,hend] at hh
  apply hh.mono
  have hl:=StackSubtract.subDigits_length A B false
  have hl' := BinaryNormalize.normalize_length S
  rw [hS] at hl'
  dsimp only [S] at hl hl' ⊢
  omega

lemma sub_exec (E : Env R) (i j : R) (hij : i≠j) (m n : ℕ)
    (hi : E i=nat m) (hj : E j=nat n) (hle : n ≤ m) :
    Exec (sub i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (m-n)) .nil))
      (9*(m.bits.length+n.bits.length)+20) := by
  simpa only [StackAddition.value_bits] using sub_bits_exec E i j hij m.bits n.bits hi hj
    (by simpa only [StackAddition.value_bits] using hle)
end MatchingFPRAS.TreeArithmetic

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePartialChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]

def choosePartial (f : A → Bool) (g h : A → B) (F : Realizer f)
    (G H : Proc (K Reg)) (t u : A → ℕ)
    (hg : ∀ a s,f a=true → Exec G (encodeEnv (env (encode a) .nil s))
      (encodeEnv (env (encode (g a)) .nil s)) (t a))
    (hh : ∀ a s,f a=false → Exec H (encodeEnv (env (encode a) .nil s))
      (encodeEnv (env (encode (h a)) .nil s)) (u a)) :
    Realizer (fun a=>if f a then g a else h a) where
  program := seq (TreeFunction.copy 0 1 (by decide)) (seq (TreeFunction.cons 1 2 (by decide))
    (seq F.program (RegisterStructured.select 0
      (seq (TreeFunction.split 0 2 (by decide)) H)
      (seq (TreeFunction.split 0 2 (by decide)) G))))
  cost := fun a=>F.cost a+(if f a then t a else u a)+7*TreeFunction.size (encode a)+18
  correct := by
    intro a s
    have h1:=copy01 (encode a) .nil s
    have h2:=cons12 (encode a) (encode a) s
    have h3:=F.correct a (.cons (encode a) s)
    have h4:=split02 (encode (f a)) .nil (encode a) s
    have hs : TreeFunction.size (encode (f a)) ≤ 3 := by
      cases f a <;> simp [Codec.encode,bit]
    cases hf : f a
    · have h5:=hh a s hf
      have hh':=RegisterStructured.select_nil 0 _ (seq (TreeFunction.split 0 2 (by decide)) G)
        (env (encode (f a)) .nil (.cons (encode a) s)) (env (encode (h a)) .nil s) _
        (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,Bool.false_eq_true,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh'))).mono
      simp only [hf,size_nil]
      rw [hf] at hs
      omega
    · have h5:=hg a s hf
      have hh':=RegisterStructured.select_cons 0 (seq (TreeFunction.split 0 2 (by decide)) H) _
        (env (encode (f a)) .nil (.cons (encode a) s)) (env (encode (g a)) .nil s) _
        .nil .nil (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh'))).mono
      simp only [hf,size_nil]
      rw [hf] at hs
      omega

def subProgram : Proc (K Reg) := seq (TreeFunction.split 1 0 (by decide))
  (seq (TreeArithmetic.sub 1 0 (by decide))
    (seq (TreeFunction.copy 1 0 (by decide)) (TreeFunction.clear 1)))
def subCost (ab : ℕ×ℕ) : ℕ := 2*TreeFunction.size (nat ab.1)+
  9*(ab.1.bits.length+ab.2.bits.length)+4*TreeFunction.size (nat (ab.1-ab.2))+32
lemma subProgram_exec (a b : ℕ) (s : Data) (hab : b ≤ a) :
    Exec subProgram (encodeEnv (env (encode (a,b)) .nil s))
      (encodeEnv (env (nat (a-b)) .nil s)) (subCost (a,b)) := by
  have h1:=split10 (nat a) (nat b) .nil s
  have h2:=TreeArithmetic.sub_exec (env (nat b) (nat a) s) 1 0 (by decide) a b rfl rfl hab
  simp only [putPair,env_update0,env_update1] at h2
  have h3:=copy10 .nil (nat (a-b)) s
  have h4:=clear1 (nat (a-b)) (nat (a-b)) s
  apply (h1.seq (h2.seq (h3.seq h4))).mono
  simp only [size_nil,subCost]; omega

def subtract : Realizer (fun ab : ℕ×ℕ=>ab.1-ab.2) := by
  let Z : Realizer (fun _ : ℕ×ℕ=>0) := constant 0
  let P:=choosePartial (fun ab : ℕ×ℕ=>decide (ab.1<ab.2)) (fun _=>0) (fun ab=>ab.1-ab.2)
    less Z.program subProgram Z.cost subCost (fun a s _=>Z.correct a s)
    (fun a s h=>subProgram_exec a.1 a.2 s (by simpa only [decide_eq_false_iff_not,not_lt] using h))
  refine ⟨P.program,P.cost,?_⟩
  intro ab stack
  by_cases hlt : ab.1<ab.2
  · simpa [hlt,Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)] using P.correct ab stack
  · simpa [hlt] using P.correct ab stack
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeNatDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def digitValue : Realizer Bool.toNat :=
  (choose identity (constant 1) (constant 0)).congr (fun b=>by cases b <;> rfl)

def divStepRealizer : Realizer divStep := by
  let nP : Realizer (fun x : Bool×(ℕ×(ℕ×ℕ))=>x.2.1) := composition second first
  let qP : Realizer (fun x : Bool×(ℕ×(ℕ×ℕ))=>2*x.2.2.1) :=
    composition (composition (composition second second) first) double
  let rP : Realizer (fun x : Bool×(ℕ×(ℕ×ℕ))=>2*x.2.2.2+x.1.toNat) :=
    composition (pair (composition (composition (composition second second) second) double)
      (composition first digitValue)) add
  let lP := composition (pair rP nP) less
  let q1P := composition (pair qP (constant 1)) add
  let r1P := composition (pair rP nP) subtract
  exact (pair nP (choose lP (pair qP rP) (pair q1P r1P))).congr (by
    intro x; simp only [Function.comp_apply,divStep,decide_eq_true_eq])

lemma divFold_mass (A : List Bool) (n q r : ℕ) :
    n*(A.reverse.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.1+
      (A.reverse.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.2=
      (n*q+r)*2^A.length+StackAddition.value A := by
  induction A with
  | nil => simp [StackAddition.value]
  | cons b A ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    let z := A.reverse.foldl (fun z b=>divStep (b,z)) (n,q,r)
    have hz : z=(n,z.2.1,z.2.2) := by
      apply Prod.ext
      · exact divFold_first A.reverse n q r
      · rfl
    change n*(divStep (b,z)).2.1+(divStep (b,z)).2.2=_
    rw [hz,divStep_mass]
    change n*z.2.1+z.2.2=_ at ih
    rw [ih]
    simp only [StackAddition.value,List.length_cons,pow_succ]
    ring

lemma divFold_correct (m n : ℕ) (hn : 0<n) :
    (m.bits.reverse.foldl (fun z b=>divStep (b,z)) (n,0,0)).2=(m/n,m%n) := by
  have hm:=divFold_mass m.bits n 0 0
  have hr:=divFold_lt m.bits.reverse n 0 0 hn hn
  simp only [Nat.mul_zero,Nat.zero_add,Nat.zero_mul,StackAddition.value_bits] at hm
  have hu : m/n=(m.bits.reverse.foldl (fun z b=>divStep (b,z)) (n,0,0)).2.1 ∧
      m%n=(m.bits.reverse.foldl (fun z b=>divStep (b,z)) (n,0,0)).2.2 :=
    (Nat.div_mod_unique hn).2 ⟨by omega,hr⟩
  exact Prod.ext hu.1.symm hu.2.symm

def divCore : Realizer (fun ab : ℕ×ℕ=>
    (ab.1.bits.reverse.foldl (fun z b=>divStep (b,z)) (ab.2,0,0)).2) :=
  composition (composition (pair (composition (composition first toBits) reverse)
    (pair second (pair (constant 0) (constant 0)))) (fold divStepRealizer)) second

def division : Realizer (fun ab : ℕ×ℕ=>(ab.1/ab.2,ab.1%ab.2)) := by
  let posP : Realizer (fun ab : ℕ×ℕ=>decide (0<ab.2)) := composition (pair (constant 0) second) less
  let zeroP : Realizer (fun ab : ℕ×ℕ=>(0,ab.1)) := pair (constant 0) first
  exact (choose posP divCore zeroP).congr (by
    intro ab
    by_cases h : 0<ab.2
    · simp only [h,decide_true,↓reduceIte]
      exact divFold_correct ab.1 ab.2 h
    · have hn : ab.2=0 := by omega
      simp [hn])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {B : Type} [Codec B]

def predecessor : Realizer (fun n : ℕ=>n-1) := composition (pair identity (constant 1)) subtract

namespace Repeat
open RegisterControl (Instr Runs Effect)

def nextRealizer {f : ℕ×B → B} (F : Realizer f) : Realizer (next f) :=
  pair (composition first predecessor) F

def code (P : Proc (K Reg)) : Point → RegisterControl.Instr Reg Point
  | .loop => .call (TreeFunction.split 1 0 (by decide)) .check
  | .check => .branch 1 .halt .rebuild
  | .rebuild => .call (TreeFunction.cons 1 0 (by decide)) .body
  | .body => .call P .loop
  | .halt => .halt

def cost (f : ℕ×B → B) (t : ℕ×B → ℕ) : ℕ → B → ℕ
  | 0,_ => 10
  | n+1,b => t (n+1,b)+4*TreeFunction.size (nat (n+1))+12+cost f t n (f (n+1,b))

lemma runs {f : ℕ×B → B} (F : Realizer f) (n : ℕ) (b : B) (s : Data) :
    Runs (code (nextRealizer F).program) (some Point.loop) (env (encode (n,b)) .nil s)
      (env (encode (countDown f n b)) .nil s) (cost f (nextRealizer F).cost n b) := by
  induction n generalizing b with
  | zero =>
    have hh : Runs (code (nextRealizer F).program) (some Point.halt) (env (encode b) .nil s)
        (env (encode b) .nil s) 1 := Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
    have hc : Runs (code (nextRealizer F).program) (some Point.check) (env (encode b) .nil s)
        (env (encode b) .nil s) 2 := Runs.step _ _ _ _ _ 1 1 (Effect.nilBranch _ 1 _ _ rfl) hh
    have hs := split10 (nat 0) (encode b) .nil s
    change Exec _ _ _ 7 at hs
    exact Runs.step _ _ _ _ _ 2 8 (Effect.call _ _ _ _ 7 hs) hc
  | succ n ih =>
    have hr:=ih (f (n+1,b))
    have hb:=(nextRealizer F).correct (n+1,b) s
    have he : next f (n+1,b)=(n,f (n+1,b)) := by simp [next]
    change Exec _ _ (encodeEnv (env (encode (next f (n+1,b))) .nil s)) _ at hb
    rw [he] at hb
    let c := cost f (nextRealizer F).cost n (f (n+1,b))
    let t := (nextRealizer F).cost (n+1,b)
    let d := TreeFunction.size (nat (n+1))
    have hbody : Runs (code (nextRealizer F).program) (some Point.body) (env (encode (n+1,b)) .nil s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) ((t+1)+c) :=
      Runs.step _ _ _ _ _ c (t+1) (Effect.call _ _ _ _ t hb) hr
    have hcons:=cons10 (encode b) (nat (n+1)) s
    have hreb : Runs (code (nextRealizer F).program) (some Point.rebuild) (env (encode b) (nat (n+1)) s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) ((2*d+4)+((t+1)+c)) :=
      Runs.step _ _ _ _ _ _ (2*d+4) (Effect.call _ _ _ _ (2*d+3) hcons) hbody
    have hn : ∃ a z,nat (n+1)=.cons a z := by
      cases he : (n+1).bits with
      | nil =>
        have hv:=StackAddition.value_bits (n+1)
        rw [he] at hv
        simp [StackAddition.value] at hv
      | cons a z => exact ⟨bit a,bits z,by change bits (n+1).bits=Data.cons (bit a) (bits z); rw [he]; rfl⟩
    obtain ⟨a,z,ha⟩:=hn
    have hc : Runs (code (nextRealizer F).program) (some Point.check) (env (encode b) (nat (n+1)) s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) (1+((2*d+4)+((t+1)+c))) :=
      Runs.step _ _ _ _ _ _ 1 (Effect.consBranch _ 1 _ _ a z ha) hreb
    have hs:=split10 (nat (n+1)) (encode b) .nil s
    have hs' := hs.mono (show TreeFunction.size Data.nil+2*d+4 ≤ 2*d+5 by simp only [size_nil]; omega)
    have hh : Runs (code (nextRealizer F).program) (some Point.loop) (env (encode (n+1,b)) .nil s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) ((2*d+6)+(1+((2*d+4)+((t+1)+c)))) :=
      Runs.step _ _ _ _ _ _ (2*d+6) (Effect.call _ _ _ _ (2*d+5) hs') hc
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try rfl
    simp only [cost,d,t,c]
    omega
end Repeat

def iterateDown {f : ℕ×B → B} (F : Realizer f) : Realizer (fun nb : ℕ×B=>countDown f nb.1 nb.2) :=
  ⟨RegisterControl.compile (Repeat.code (Repeat.nextRealizer F).program),
    fun nb=>Repeat.cost f (Repeat.nextRealizer F).cost nb.1 nb.2,
    fun nb s=>RegisterControl.compile_exec _ _ _ _ (Repeat.runs F nb.1 nb.2 s)⟩

def rangeStepRealizer : Realizer rangeStep := composition (pair (composition first predecessor) second) listCons
def range : Realizer List.range :=
  (composition (pair identity (constant ([] : List ℕ))) (iterateDown rangeStepRealizer)).congr (by
    intro n; simp [countDown_range])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeNaturalComb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def successor : Realizer Nat.succ :=
  (composition (pair identity (constant 1)) add).congr (fun _=>rfl)

def quotient : Realizer (fun x : ℕ×ℕ=>x.1/x.2) := composition division first
def remainder : Realizer (fun x : ℕ×ℕ=>x.1%x.2) := composition division second

def factorial : Realizer Nat.factorial :=
  (composition (pair identity (constant 1))
    (iterateDown multiply)).congr (by
      intro n
      change countDown factStep n 1=_
      rw [fact_countDown,Nat.mul_one])

def natChoose : Realizer (fun x : ℕ×ℕ=>x.1.choose x.2) := by
  let Q := composition (pair (composition first factorial)
    (composition (pair (composition second factorial) (composition subtract factorial)) multiply)) quotient
  exact (choose (composition (pair second first) less) Q
    (choose (composition (pair first second) less) (constant 0) (constant 1))).congr (by
    intro x
    change (if decide (x.2<x.1) then _ else if decide (x.1<x.2) then 0 else 1)=x.1.choose x.2
    by_cases h : x.2<x.1
    · simp only [h,decide_true,↓reduceIte,Function.comp_apply]
      exact (Nat.choose_eq_factorial_div_factorial (Nat.le_of_lt h)).symm
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte]
      by_cases h' : x.1<x.2
      · simp [h',Nat.choose_eq_zero_of_lt h']
      · have e : x.1=x.2 := by omega
        simp [e])

def pairingNumber : Realizer UnitRefresh.pairingCount :=
  (composition (composition (pair range (constant (1,0)))
    (fold (pair (composition second second)
      (composition (pair (composition first successor) (composition second first)) multiply)))) first).congr (by
        intro n
        change ((List.range n).foldl (fun z i=>pairingStep (i,z)) (1,0)).1=_
        rw [pairing_range])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeListOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B X : Type} [Codec A] [Codec B] [Codec X]

def listCase (b : B) {g : A×List A → B} (G : Realizer g) :
    Realizer (fun as : List A=>match as with | []=>b | a::as=>g (a,as)) where
  program := RegisterStructured.select 0 (constant b (A:=List A)).program G.program
  cost := fun as=>3+match as with | []=>(constant b (A:=List A)).cost [] | a::as=>G.cost (a,as)
  correct := by
    intro as s
    cases as with
    | nil =>
      have hh:=RegisterStructured.select_nil 0 _ G.program (env (encode ([] : List A)) .nil s)
        (env (encode b) .nil s) _ rfl ((constant b (A:=List A)).correct [] s)
      exact hh.mono (by dsimp; omega)
    | cons a as =>
      have hh:=RegisterStructured.select_cons 0 (constant b (A:=List A)).program _
        (env (encode (a::as)) .nil s) (env (encode (g (a,as))) .nil s) _ (encode a) (encode as) rfl
        (G.correct (a,as) s)
      exact hh.mono (by dsimp; omega)

def head (d : A) : Realizer (fun as : List A=>as.headD d) :=
  (listCase d first).congr (by intro as; cases as <;> rfl)

def tail : Realizer (List.tail : List A → List A) := listCase [] second

def isEmpty : Realizer (List.isEmpty : List A → Bool) := listCase true (constant false)

omit [Codec A] [Codec B] [Codec X] in
lemma countDown_drop (n : ℕ) (as : List A) : countDown (dropStep (A:=A)) n as=as.drop n := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih =>
    rw [countDown,ih]
    exact List.drop_tail

def mapStepRealizer {g : X×A → B} (G : Realizer g) : Realizer (mapStep g) :=
  pair (composition second first)
    (composition (pair (composition (pair (composition second first) first) G)
      (composition second second)) listCons)

omit [Codec A] [Codec B] [Codec X] in
lemma mapStep_fold (g : X×A → B) (as : List A) (x : X) (bs : List B) :
    as.foldl (fun z a=>mapStep g (a,z)) (x,bs)=(x,(as.map (fun a=>g (x,a))).reverse++bs) := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
    change as.foldl _ (x,g (x,a)::bs)=_
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

def mapWith {g : X×A → B} (G : Realizer g) : Realizer (fun xas : X×List A=>xas.2.map (fun a=>g (xas.1,a))) :=
  (composition (composition (pair second (pair first (constant ([] : List B)))) (fold (mapStepRealizer G)))
    (composition second reverse)).congr (by
      intro xas
      change ((xas.2.foldl _ (xas.1,[])).2).reverse=_
      rw [mapStep_fold]
      simp)

def map {g : A → B} (G : Realizer g) : Realizer (List.map g) := by
  let S : Realizer (fun x : A×List B=>g x.1::x.2) := composition (pair (composition first G) second) listCons
  exact (composition (composition (pair identity (constant ([] : List B))) (fold S)) reverse).congr (by
    intro as
    change (as.foldl (fun bs a=>g a::bs) []).reverse=as.map g
    simp)

def listLength : Realizer (List.length : List A → ℕ) :=
  (composition (pair identity (constant 0))
    (fold (composition (pair second (constant 1)) add))).congr (by
      intro as
      change as.foldl (fun n (_ : A)=>n+1) 0=as.length
      have h : ∀ n,as.foldl (fun n (_ : A)=>n+1) n=n+as.length := by
        induction as with
        | nil => intro n; simp
        | cons a as ih => intro n; simp only [List.foldl_cons,ih,List.length_cons]; omega
      simpa only [Nat.zero_add] using h 0)

def append : Realizer (fun x : List A×List A=>x.1++x.2) :=
  (composition (pair (composition first reverse) second) (fold listCons)).congr (by
    intro x
    change x.1.reverse.foldl (fun bs a=>a::bs) x.2=x.1++x.2
    rw [List.foldl_flip_cons_eq_append',List.reverse_reverse])

def filter {f : A → Bool} (F : Realizer f) : Realizer (List.filter f) := by
  let S : Realizer (fun x : A×List A=>if f x.1 then x.1::x.2 else x.2) :=
    choose (composition first F) listCons second
  exact (composition (composition (pair identity (constant ([] : List A))) (fold S)) reverse).congr (by
    intro as
    change (as.foldl (fun bs a=>if f a then a::bs else bs) []).reverse=as.filter f
    have h : ∀ bs,as.foldl (fun bs a=>if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
      induction as with
      | nil => intro bs; rfl
      | cons a as ih =>
        intro bs
        cases hf : f a <;> simp [List.foldl_cons,hf,ih,List.append_assoc]
    rw [h]
    simp)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePredicate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]

def boolNot : Realizer Bool.not :=
  (choose identity (constant false) (constant true)).congr (by intro b; cases b <;> rfl)
def boolAnd : Realizer (fun x : Bool×Bool=>x.1 && x.2) :=
  (choose first second (constant false)).congr (by intro x; cases x.1 <;> rfl)
def natEqual : Realizer (fun x : ℕ×ℕ=>decide (x.1=x.2)) :=
  (choose less (constant false)
    (choose (composition (pair second first) less) (constant false) (constant true))).congr (by
    intro x
    change (if decide (x.1<x.2) then false else if decide (x.2<x.1) then false else true)=_
    by_cases h : x.1<x.2
    · simp [h,Nat.ne_of_lt h]
    · by_cases h' : x.2<x.1
      · simp [h,h',Ne.symm (Nat.ne_of_lt h')]
      · have e : x.1=x.2 := by omega
        simp [e])

def any : Realizer (fun bs : List Bool=>bs.any id) :=
  (composition (pair identity (constant false))
    (fold (choose first (constant true) second))).congr (by
      intro bs
      change bs.foldl (fun z b=>if b then true else z) false=bs.any id
      have h : ∀ z, bs.foldl (fun z b=>if b then true else z) z=(bs.any id || z) := by
        induction bs with
        | nil => intro z; rfl
        | cons b bs ih =>
          intro z
          simp only [List.foldl_cons,ih,List.any_cons]
          cases b <;> cases bs.any id <;> cases z <;> rfl
      rw [h]
      cases bs.any id <;> rfl)

def membership : Realizer (fun x : List ℕ×ℕ=>decide (x.2∈x.1)) :=
  (composition (composition (pair second first) (mapWith natEqual)) any).congr (by
    intro x
    simp only [Function.comp_apply,List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Function.comp_apply,decide_eq_true_eq,id_eq]
    constructor
    · rintro ⟨a,ha,e⟩; simpa [←e] using ha
    · intro h; exact ⟨x.2,h,rfl⟩)

def countTrue : Realizer (fun bs : List Bool=>(bs.filter id).length) :=
  composition (filter identity) listLength

def countWith {p : A×B → Bool} (P : Realizer p) :
    Realizer (fun x : A×List B=>(x.2.filter fun b=>p (x.1,b)).length) :=
  (composition (mapWith P) countTrue).congr (by
    intro x; simp only [Function.comp_apply,List.filter_map,List.length_map]; rfl)

def listSum : Realizer (List.sum : List ℕ → ℕ) :=
  (composition (pair identity (constant 0)) (fold add)).congr (by
    intro as
    change as.foldl (fun n a=>a+n) 0=as.sum
    have h : ∀ z,as.foldl (fun n a=>a+n) z=as.sum+z := by
      induction as with
      | nil => intro z; simp
      | cons a as ih => intro z; simp only [List.foldl_cons,ih,List.sum_cons]; omega
    simpa using h 0)

def listProd : Realizer (List.prod : List ℕ → ℕ) :=
  (composition (pair identity (constant 1)) (fold multiply)).congr (by
    intro as
    change as.foldl (fun n a=>a*n) 1=as.prod
    have h : ∀ z,as.foldl (fun n a=>a*n) z=as.prod*z := by
      induction as with
      | nil => intro z; simp
      | cons a as ih => intro z; simp only [List.foldl_cons,ih,List.prod_cons]; ring
    simpa using h 1)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def digits : Realizer Nat.bits where
  program := identity.program (A:=ℕ)
  cost := fun _=>1
  correct := fun a s=>identity.correct a s

def bitSize : Realizer Nat.size :=
  (composition digits listLength).congr (fun a=>Nat.size_eq_bits_len a)

def sortedPairRealizer : Realizer sortedPair :=
  (choose less (pair second first) identity).congr (fun x=>by simp [sortedPair])

def gcdStepRealizer : Realizer gcdStep :=
  (choose (composition (pair second (constant 0)) natEqual) identity (pair second remainder)).congr
    (fun x=>by simp only [gcdStep,Function.comp_apply,decide_eq_true_eq,id_eq])

def gcd : Realizer (fun x : ℕ×ℕ=>x.1.gcd x.2) :=
  (composition (composition (pair (composition (pair (composition first bitSize)
    (composition second bitSize)) add) sortedPairRealizer)
    (iterateDown (composition second gcdStepRealizer))) first).congr (by
      intro x
      change (countDown gcdIterStep (x.1.size+x.2.size) (sortedPair x)).1=x.1.gcd x.2
      rw [gcdIter_result _ _ (sortedPair_order x) (by rw [sortedPair_size]),sortedPair_gcd])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def repr (q : ℚ) : Fraction := (q.num.natAbs,q.den)

def normalizeRealizer : Realizer normalize := by
  let G := gcd
  let Q := pair (composition (pair first G) quotient) (composition (pair second G) quotient)
  exact (choose (composition (pair second (constant 0)) natEqual) (constant (0,1)) Q).congr
    (fun x=>by simp only [normalize,Function.comp_apply,decide_eq_true_eq])

def mulRealizer : Realizer mul :=
  composition (pair (composition (pair (composition first first) (composition second first)) multiply)
    (composition (pair (composition first second) (composition second second)) multiply)) normalizeRealizer
def addRealizer : Realizer add :=
  composition (pair (composition (pair
    (composition (pair (composition first first) (composition second second)) multiply)
    (composition (pair (composition second first) (composition first second)) multiply)) TreeTyped.add)
    (composition (pair (composition first second) (composition second second)) multiply)) normalizeRealizer
def divRealizer : Realizer div :=
  composition (pair (composition (pair (composition first first) (composition second second)) multiply)
    (composition (pair (composition first second) (composition second first)) multiply)) normalizeRealizer

def less (x : Fraction×Fraction) : Bool := decide (x.1.1*x.2.2<x.2.1*x.1.2)
def lessRealizer : Realizer less :=
  composition (pair (composition (pair (composition first first) (composition second second)) multiply)
    (composition (pair (composition second first) (composition first second)) multiply)) TreeTyped.less

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def weight (a : A) : ℕ := TreeFunction.size (encode a)
@[simp] lemma weight_prod (a : A) (b : B) : weight (a,b)=1+weight a+weight b := by simp [weight]; omega
@[simp] lemma weight_nil : weight ([] : List A)=1 := rfl
@[simp] lemma weight_cons (a : A) (as : List A) : weight (a::as)=1+weight a+weight as := by simp [weight]; omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

def contains [DecidableEq A] (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×List A=>decide (x.1∈x.2)) :=
  (composition (mapWith E) any).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_map,List.any_eq_true,id_eq,decide_eq_true_eq]
    constructor
    · rintro ⟨a,ha,he⟩; simpa [he] using ha
    · intro h; exact ⟨x.1,h,rfl⟩)
def dedupStepRealizer [DecidableEq A] (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (dedupStep (A:=A)) :=
  (choose (contains E) second listCons).congr (by intro x; simp [dedupStep])
omit [Codec A] in
lemma dedup_fold [DecidableEq A] (as : List A) :
    as.reverse.foldl (fun bs a=>dedupStep (a,bs)) []=as.dedup := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    exact (List.dedup_cons' a as).symm
def dedup [DecidableEq A] (E : Realizer (fun x : A×A=>decide (x.1=x.2))) : Realizer (List.dedup (α:=A)) :=
  (composition (pair reverse (constant [])) (fold (dedupStepRealizer E))).congr dedup_fold

variable (r : A → A → Prop) [DecidableRel r]
def insertStepRealizer (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) : Realizer (insertStep r) :=
  (pair (composition second first) (pair (composition (pair first (composition (composition second second) first)) listCons)
    (choose (composition (pair (composition second first) first) R)
      (composition (pair (composition second first) (composition (pair first (composition (composition second second) first)) listCons)) listCons)
      (composition (pair first (composition (composition second second) second)) listCons)))).congr (by intro x; simp [insertStep])
omit [Codec A] in
lemma insert_fold (as bs : List A) (a : A) :
    as.reverse.foldl (fun z b=>insertStep r (b,z)) (a,(bs,List.orderedInsert r a bs))=
      (a,(as++bs,List.orderedInsert r a (as++bs))) := by
  induction as with
  | nil => rfl
  | cons b as ih =>
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    rfl
def orderedInsert (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) :
    Realizer (fun x : A×List A=>List.orderedInsert r x.1 x.2) :=
  (composition (composition (pair (composition second reverse)
    (pair first (pair (constant []) (composition (pair first (constant [])) listCons))))
      (fold (insertStepRealizer r R))) (composition second second)).congr (by
        intro x
        change (x.2.reverse.foldl (fun z b=>insertStep r (b,z)) (x.1,([],[x.1]))).2.2=_
        have h:=insert_fold r x.2 [] x.1
        simpa only [List.append_nil,List.orderedInsert_nil] using congrArg (fun x=>x.2.2) h)

def insertionSort (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) :
    Realizer (List.insertionSort r) :=
  (composition (pair reverse (constant [])) (fold (orderedInsert r R))).congr (by
    intro as
    change as.reverse.foldl (fun bs a=>List.orderedInsert r a bs) []=as.insertionSort r
    rw [List.foldl_reverse]
    rfl)

variable [DecidableEq A]
def canonical (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) :
    Realizer (fun as : List A=>as.dedup.insertionSort r) := composition (dedup E) (insertionSort r R)
omit [Codec A] in
lemma canonical_eq_sort [IsTrans A r] [Std.Total r] [Std.Antisymm r] (as : List A) :
    as.dedup.insertionSort r=as.toFinset.sort r := by
  have hn:=(List.perm_insertionSort r as.dedup).nodup_iff.mpr (List.nodup_dedup as)
  have hh:=(List.toFinset_sort (r:=r) hn).mpr (List.pairwise_insertionSort r as.dedup)
  have he : (as.dedup.insertionSort r).toFinset=as.toFinset := by ext a; simp
  rw [he] at hh
  exact hh.symm
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def Realizer.fst {f : A → B×C} (F : Realizer f) : Realizer (fun a=>(f a).1) := composition F first
def Realizer.snd {f : A → B×C} (F : Realizer f) : Realizer (fun a=>(f a).2) := composition F second
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B]
def filterWith {f : A×B → Bool} (F : Realizer f) :
    Realizer (fun x : A×List B=>x.2.filter fun b=>f (x.1,b)) :=
  (composition (composition (mapWith (pair second F)) (filter second)) (map first)).congr (by
    intro x
    simp only [Function.comp_apply,List.filter_map,List.map_map]
    simp [Function.comp_def])
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

def totalFlagRealizer : Realizer totalFlag := composition (pair second first) membership
def privateFlagRealizer : Realizer privateFlag := composition
  (pair (composition (pair (composition second listLength) (constant 1)) natEqual) totalFlagRealizer) boolAnd
def sharedFlagRealizer : Realizer sharedFlag := composition
  (pair totalFlagRealizer (composition privateFlagRealizer boolNot)) boolAnd

def privateNumberRealizer : Realizer (fun x : Bags×ℕ=>privateNumber x.1 x.2) :=
  (composition (pair second first) (countWith privateFlagRealizer)).congr (fun _=>rfl)
def sharedNumberRealizer : Realizer (fun x : Bags×ℕ=>sharedNumber x.1 x.2) :=
  (composition (pair second first) (countWith sharedFlagRealizer)).congr (fun _=>rfl)
def totalNumberRealizer : Realizer (fun x : Bags×ℕ=>totalNumber x.1 x.2) :=
  (composition (pair second first) (countWith totalFlagRealizer)).congr (fun _=>rfl)
def trimRealizer : Realizer (fun x : Bags×ℕ=>trim x.1 x.2) :=
  composition (pair second first) (filterWith (composition totalFlagRealizer boolNot))

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

def Realizer.recode {f : C → D} (F : Realizer f) (i : A → C) (g : A → B)
    (hi : ∀ a,encode (i a)=encode a) (ho : ∀ a,encode (f (i a))=encode (g a)) : Realizer g where
  program := F.program
  cost := fun a=>F.cost (i a)
  correct := by
    intro a s
    have h:=F.correct (i a) s
    rw [hi,ho] at h
    exact h

instance finsetCodec [LinearOrder A] : Codec (Finset A) := ⟨fun s=>encode (s.sort (·≤·))⟩
@[simp] lemma encode_finset [LinearOrder A] (s : Finset A) : encode s=encode (s.sort (·≤·)) := rfl
@[simp] lemma weight_finset [LinearOrder A] (s : Finset A) : weight s=weight (s.sort (·≤·)) := rfl
variable [LinearOrder A]

def finsetList : Realizer (fun s : Finset A=>s.sort (·≤·)) :=
  (identity (A:=List A)).recode (fun s : Finset A=>s.sort (·≤·)) (fun s=>s.sort (·≤·)) (fun _=>rfl) (fun _=>rfl)

def listFinset (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (List.toFinset (α:=A)) :=
  (canonical (·≤·) E R).recode id List.toFinset (fun _=>rfl) (fun as=>by
    change encode (as.dedup.insertionSort (·≤·))=encode (as.toFinset.sort (·≤·))
    rw [canonical_eq_sort])

def finsetMember (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×Finset A=>decide (x.1∈x.2)) :=
  (contains E).recode (fun x=>(x.1,x.2.sort (·≤·))) _ (fun _=>rfl) (fun x=>by simp)

def finsetCard : Realizer (Finset.card (α:=A)) :=
  (composition finsetList listLength).congr (by intro s; simp)

def finsetUnion (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) :
    Realizer (fun x : Finset A×Finset A=>x.1∪x.2) :=
  (composition (composition (pair (composition first finsetList) (composition second finsetList)) append)
    (listFinset E R)).congr (by intro x; simp)

omit [Codec A] in
lemma sort_filter (p : A → Bool) (s : Finset A) :
    (s.sort (·≤·)).filter p=(s.filter fun a=>p a).sort (·≤·) := by
  have hh := (List.toFinset_sort (r:=(·≤·)) ((Finset.sort_nodup s (·≤·)).filter p)).mpr
    ((Finset.pairwise_sort s (·≤·)).filter p)
  simpa only [List.toFinset_filter,Finset.sort_toFinset] using hh.symm

def finsetFilterWith {p : B×A → Bool} (P : Realizer p) :
    Realizer (fun x : B×Finset A=>x.2.filter fun a=>p (x.1,a)) :=
  (filterWith P).recode (fun x=>(x.1,x.2.sort (·≤·))) _ (fun _=>rfl) (fun x=>by
    change encode ((x.2.sort (·≤·)).filter fun a=>p (x.1,a))=encode ((x.2.filter fun a=>p (x.1,a)).sort (·≤·))
    rw [sort_filter])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFiniteOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def all : Realizer (fun bs : List Bool=>bs.all id) :=
  (composition (composition (map boolNot) any) boolNot).congr (by
    intro bs
    change (!((bs.map Bool.not).any id))=bs.all id
    induction bs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp_all)

def pairEqual [DecidableEq A] [DecidableEq B]
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (F : Realizer (fun x : B×B=>decide (x.1=x.2))) :
    Realizer (fun x : (A×B)×(A×B)=>decide (x.1=x.2)) :=
  (composition (pair (composition (pair first.fst second.fst) E)
    (composition (pair first.snd second.snd) F)) boolAnd).congr (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,Prod.ext_iff])

def leNat : Realizer (fun x : ℕ×ℕ=>decide (x.1≤x.2)) :=
  (composition (composition (pair second first) less) boolNot).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq,not_lt])

variable [LinearOrder A]
def finsetAny {p : B×A → Bool} (P : Realizer p) :
    Realizer (fun x : B×Finset A=>decide (∃ a∈x.2,p (x.1,a)=true)) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith P)) any).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_map,List.any_eq_true,id_eq,decide_eq_true_eq,Finset.mem_sort])

def finsetAll {p : B×A → Bool} (P : Realizer p) :
    Realizer (fun x : B×Finset A=>decide (∀ a∈x.2,p (x.1,a)=true)) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith P)) all).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.all_map,List.all_eq_true,id_eq,decide_eq_true_eq,Finset.mem_sort])

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

def finsetErase (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×Finset A=>x.2.erase x.1) :=
  (finsetFilterWith (composition E boolNot)).congr (by
    intro x; ext a
    simp only [Function.comp_apply,Finset.mem_filter,Bool.not_eq_true',decide_eq_false_iff_not,Finset.mem_erase]
    tauto)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B] [LinearOrder A] [LinearOrder B]

def boolOr : Realizer (fun x : Bool×Bool=>x.1 || x.2) :=
  (choose first (constant true) second).congr (by intro x; cases x.1 <;> rfl)

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

def lexLe (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2)))
    (S : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (fun x : (A×B)×(A×B)=>decide (toLex x.1≤toLex x.2)) :=
  (composition (pair (composition (pair first.fst second.fst) R)
    (composition (pair (composition (composition (pair first.fst second.fst) E) boolNot)
      (composition (pair first.snd second.snd) S)) boolOr)) boolAnd).congr (by
        intro x
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',
          decide_eq_true_eq,decide_eq_false_iff_not,Prod.Lex.le_iff]
        rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
        dsimp only
        constructor
        · rintro ⟨h,h'⟩
          rcases lt_or_eq_of_le h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h,h'.resolve_left (not_not.mpr h)⟩
        · rintro (h|⟨h,h'⟩)
          · exact ⟨h.le,Or.inl (ne_of_lt h)⟩
          · exact ⟨h.le,Or.inr h'⟩)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFiniteCollections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
omit [Codec A] [Codec B] [Codec C] in
lemma fold_prepend (as : List (List A)) (bs : List A) :
    as.foldl (fun bs a=>a++bs) bs=as.reverse.flatten++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => simp [List.foldl_cons,ih,List.flatten_append,List.append_assoc]

def flatten : Realizer (List.flatten (α:=A)) :=
  (composition (pair reverse (constant ([] : List A))) (fold append)).congr (by
    intro as
    change as.reverse.foldl (fun bs a=>a++bs) []=as.flatten
    rw [fold_prepend,List.reverse_reverse,List.append_nil])

variable [LinearOrder A]
def finsetSingleton : Realizer (fun a : A=>({a} : Finset A)) :=
  (composition (pair identity (constant ([] : List A))) listCons).recode id
    (fun a=>({a} : Finset A)) (fun _=>rfl) (by intro a; simp only [Function.comp_apply,encode_finset,Finset.sort_singleton]; rfl)

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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B : Type} [Codec A] [Codec B]

variable {m n : A → ℕ} {f : A×(ℕ×ℕ) → B}
def grid (M : Realizer m) (N : Realizer n) (F : Realizer f) :
    Realizer (fun a=>ExecutableDP.tabulate f (a,(m a,n a))) := by
  let rowF : Realizer (fun x : (A×ℕ)×ℕ=>f (x.1.1,(x.1.2,x.2))) :=
    composition (pair first.fst (pair first.snd second)) F
  let row : Realizer (fun x : A×ℕ=>(List.range (n x.1+1)).map fun r=>f (x.1,(x.2,r))) :=
    composition (pair identity (composition (composition (composition first N) successor) range)) (mapWith rowF)
  exact composition (pair identity (composition M range)) (mapWith row)
def clipRealizer : Realizer clip :=
  (choose (composition (pair (composition second bitSize) first) leNat) second (constant 0)).congr (by
    intro x; simp only [clip,Function.comp_apply,decide_eq_true_eq])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeListMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type} [Codec A] [Codec B] [Codec X]

def minimum : Realizer (fun x : ℕ×ℕ=>min x.1 x.2) :=
  (choose less first second).congr (by intro x; simp only [decide_eq_true_eq]; split_ifs with h <;> omega)
def maximum : Realizer (fun x : ℕ×ℕ=>max x.1 x.2) :=
  (choose less second first).congr (by intro x; simp only [decide_eq_true_eq]; split_ifs with h <;> omega)

def listMinRealizer : Realizer listMin :=
  (fold minimum).congr (by intro x; dsimp only [listMin]; congr 1; funext a b; exact Nat.min_comm b a)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeCategorical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def sum (xs : List Fraction) : Fraction := xs.foldl (fun a b=>add (b,a)) (0,1)
def sumRealizer : Realizer sum :=
  (composition (pair (identity (A:=List Fraction)) (constant (0,1))) (fold addRealizer)).congr (fun _=>rfl)

def cumulativeFraction (x : List Fraction×ℕ) : Fraction := sum (x.1.take x.2)

end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.TreeTyped

def bitValue : Realizer StackAddition.value :=
  (composition (composition (pair (reverse (A:=Bool)) (constant (1,0)))
    (fold mulStepRealizer)) second).congr (by
      intro bs
      change (bs.reverse.foldl (fun z b=>mulStep (b,z)) (1,0)).2=_
      rw [mulStep_fold]
      simp)

def bitDenominatorRealizer : Realizer bitDenominator :=
  (composition (pair (identity (A:=List Bool)) (constant 1))
    (fold (composition second double))).congr (fun _=>rfl)
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction

def predicate (x : (List Fraction×Fraction)×ℕ) : Bool :=
  TreeFraction.less (x.1.2,cumulativeFraction (x.1.1,x.2+1))

def choose (x : List Fraction×Fraction) : ℕ :=
  listMin ((List.range x.1.length).filter (fun i=>predicate (x,i)),x.1.length)

def chooseBits (x : List Fraction×List Bool) : ℕ :=
  choose (x.1,(StackAddition.value x.2,bitDenominator x.2))
end MatchingFPRAS.ExecutableChoice

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFastLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

def minNat : Realizer (fun x : ℕ×ℕ=>min x.1 x.2) :=
  (choose leNat first second).congr (by intro x; simp only [decide_eq_true_eq]; exact (min_def x.1 x.2).symm)

def dropInit : Realizer (fun x : List A×ℕ=>(min x.2 x.1.length,x.1)) :=
  pair (composition (pair second (composition first listLength)) minNat) first

def dropFast : Realizer (fun x : List A×ℕ=>x.1.drop x.2) :=
  (composition dropInit (iterateDown (composition second tail))).congr (by
    intro x
    change countDown dropStep (min x.2 x.1.length) x.1=x.1.drop x.2
    rw [countDown_drop]
    by_cases h : x.2≤x.1.length
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega),List.drop_length,List.drop_eq_nil_of_le (by omega)])

def getDFast (d : A) : Realizer (fun x : List A×ℕ=>x.1.getD x.2 d) :=
  (composition dropFast (head d)).congr (by
    intro x
    simp only [Function.comp_apply, List.headD_eq_head?_getD, List.head?_drop,
      List.getD_eq_getElem?_getD])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreeChoiceCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

def takeFast : Realizer (fun x : List A×ℕ=>x.1.take x.2) :=
  (composition (composition (pair (composition first reverse)
    (composition (pair (composition first listLength) second) subtract)) dropFast) reverse).congr (by
      intro x
      change (x.1.reverse.drop (x.1.length-x.2)).reverse=x.1.take x.2
      rw [←List.reverse_take,List.reverse_reverse])
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def cumulativeFast : Realizer cumulativeFraction := composition takeFast sumRealizer
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction Polynomial

def predicateFast : Realizer predicate := by
  let C : Realizer (fun x : (List Fraction×Fraction)×ℕ=>cumulativeFraction (x.1.1,x.2+1)) :=
    (composition (pair first.fst (composition second successor)) cumulativeFast).congr (fun _=>rfl)
  exact (composition (pair first.snd C) lessRealizer).congr (fun _=>rfl)

def chooseFast : Realizer choose := by
  let rs : Realizer (fun x : List Fraction×Fraction=>List.range x.1.length) :=
    composition (composition first listLength) range
  let good:=composition (pair identity rs) (filterWith predicateFast)
  exact (composition (pair good (composition first listLength)) listMinRealizer).congr (fun _=>rfl)

def chooseBitsFast : Realizer chooseBits :=
  composition (pair first (pair (composition second bitValue) (composition second bitDenominatorRealizer))) chooseFast
end MatchingFPRAS.ExecutableChoice

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def maximum (x : Fraction×Fraction) : Fraction := if less x then x.2 else x.1
def minimum (x : Fraction×Fraction) : Fraction := if less x then x.1 else x.2
def maximumRealizer : Realizer maximum := (choose lessRealizer second first).congr (fun _=>rfl)
def minimumRealizer : Realizer minimum := (choose lessRealizer first second).congr (fun _=>rfl)
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableBottleneck
open TreeTyped TreeFraction Polynomial

abbrev Matrix := List (List Fraction)
def one : Fraction := (1,1)
def cell (x : Matrix×(ℕ×ℕ)) : Fraction := (x.1.getD x.2.1 []).getD x.2.2 one
def cellRealizer : Realizer cell := composition
  (pair (composition (pair first second.fst) (getDFast [])) second.snd) (getDFast one)
def squareRealizer {A B : Type} [Codec A] [Codec B] {n : A→ℕ} {f : A×(ℕ×ℕ)→B}
    (N : Realizer n) (F : Realizer f) : Realizer (fun a=>square (n a) a f) := by
  let rs:=composition N range
  let e:=composition (pair first.fst (pair first.snd second)) F
  let row:=composition (pair identity (composition first rs)) (mapWith e)
  exact composition (pair identity rs) (mapWith row)

def via (x : (Matrix×(ℕ×ℕ))×ℕ) : Fraction :=
  minimum (cell (x.1.1,(x.1.2.1,x.2)),cell (x.1.1,(x.2,x.1.2.2)))
def viaRealizer : Realizer via := composition (pair
  (composition (pair first.fst (pair first.snd.fst second)) cellRealizer)
  (composition (pair first.fst (pair second first.snd.snd)) cellRealizer)) minimumRealizer

def entry (x : Matrix×(ℕ×ℕ)) : Fraction :=
  if x.2.1=x.2.2 then one else
    ((List.range x.1.length).map fun c=>via (x,c)).foldl (fun z v=>maximum (v,z)) (cell x)
def entryRealizer : Realizer entry := by
  let vals:=composition (pair identity (composition (composition first listLength) range)) (mapWith viaRealizer)
  exact (choose (composition second natEqual) (constant one)
    (composition (pair vals cellRealizer) (fold maximumRealizer))).congr (by
      intro x; simp only [entry,Function.comp_apply,decide_eq_true_eq,id_eq])

def advance (M : Matrix) : Matrix := square M.length M entry
def advanceRealizer : Realizer advance := squareRealizer listLength entryRealizer

def seedEntry (x : Matrix×(ℕ×ℕ)) : Fraction := if x.2.1=x.2.2 then one
  else maximum (one,cell (x.1,(min x.2.1 x.2.2,max x.2.1 x.2.2)))
def seedEntryRealizer : Realizer seedEntry := by
  let inds : Realizer (fun x : Matrix×(ℕ×ℕ)=>if x.2.1<x.2.2 then x.2 else (x.2.2,x.2.1)) := (choose (composition second TreeTyped.less) second (pair second.snd second.fst)).congr (by intro x; simp only [Function.comp_apply,decide_eq_true_eq])
  exact (choose (composition second natEqual) (constant one)
    (composition (pair (constant one) (composition (pair first inds) cellRealizer)) maximumRealizer)).congr (by
      intro x
      simp only [seedEntry,Function.comp_apply,decide_eq_true_eq]
      split_ifs with h h'
      · rfl
      · rw [min_eq_left (le_of_lt h'),max_eq_right (le_of_lt h')]
      · rw [min_eq_right (le_of_not_gt h'),max_eq_left (le_of_not_gt h')])

def seed (M : Matrix) : Matrix := square M.length M seedEntry
def seedRealizer : Realizer seed := squareRealizer listLength seedEntryRealizer

def close (M : Matrix) : Matrix := M.foldl (fun z _=>advance z) (seed M)
def closeRealizer : Realizer close := composition (pair identity seedRealizer)
  (fold (composition second advanceRealizer))

end MatchingFPRAS.ExecutableBottleneck

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFractionExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

def sub (x : Fraction×Fraction) : Fraction :=
  normalize (x.1.1*x.2.2-x.2.1*x.1.2,x.1.2*x.2.2)
def subRealizer : Realizer sub := composition
  (pair (composition (pair (composition (pair first.fst second.snd) multiply)
    (composition (pair second.fst first.snd) multiply)) TreeTyped.subtract)
    (composition (pair first.snd second.snd) multiply)) normalizeRealizer
def productRealizer : Realizer product :=
  (composition (pair identity (constant (1,1))) (fold mulRealizer)).congr (fun _=>rfl)
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeOptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

abbrev Options (A : Type) := List (A×Fraction)
variable {A B C Ω : Type} [Codec A] [Codec B] [Codec C]

noncomputable def repr (e : Ω→A) (c : WeightedOptions Ω) : Options A :=
  List.ofFn (fun i=>(e (c.out i),TreeFraction.repr (c.mass i)))

def listSingleton : Realizer (fun a : A=>[a]) :=
  composition (pair identity (constant ([] : List A))) listCons

def pure (a : A) : Options A := [(a,(1,1))]
def pureRealizer : Realizer (pure (A:=A)) :=
  (composition (pair identity (constant (1,1))) listSingleton).congr (fun _=>rfl)

def scale (x : Fraction×Options A) : Options A := x.2.map fun a=>(a.1,mul (x.1,a.2))
def scaleRealizer : Realizer (scale (A:=A)) :=
  (mapWith (pair second.fst (composition (pair first second.snd) mulRealizer))).congr (fun _=>rfl)

def mix (x : Fraction×(Options A×Options A)) : Options A :=
  scale (x.1,x.2.1)++scale (sub ((1,1),x.1),x.2.2)
def mixRealizer : Realizer (mix (A:=A)) := composition
  (pair (composition (pair first second.fst) scaleRealizer)
    (composition (pair (composition (pair (constant (1,1)) first) subRealizer) second.snd) scaleRealizer)) append

def map (f : C×A→B) (x : C×Options A) : Options B := x.2.map fun a=>(f (x.1,a.1),a.2)
def mapRealizer {f : C×A→B} (F : Realizer f) : Realizer (map f) :=
  (mapWith (pair (composition (pair first second.fst) F) second.snd)).congr (fun _=>rfl)

def draw (d : A) (x : Options A×List Bool) : A :=
  (x.1.map Prod.fst).getD (ExecutableChoice.chooseBits (x.1.map Prod.snd,x.2)) d
def drawRealizer (d : A) : Realizer (draw d) := by
  let index : Realizer (fun x : Options A×List Bool=>
      ExecutableChoice.chooseBits (x.1.map Prod.snd,x.2)) :=
    (composition (pair (composition first (TreeTyped.map second)) second) ExecutableChoice.chooseBitsFast).congr (fun _=>rfl)
  exact (composition (pair (composition first (TreeTyped.map first)) index) (getDFast d)).congr (fun _=>rfl)

end MatchingFPRAS.ExecutableOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeOptionsFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

variable {A : Type} [Codec A] [LinearOrder A]

def uniform (s : Finset A) : Options A :=
  (s.sort (·≤·)).map fun a=>(a,TreeFraction.normalize (1,s.card))
def uniformRealizer : Realizer (uniform (A:=A)) :=
  (composition (pair (composition (pair (constant 1) finsetCard) normalizeRealizer) finsetList)
    (mapWith (pair second first))).congr (fun _=>rfl)

def neighbors (x : (A×Finset A)×ℕ) : Options A :=
  ((x.1.2.sort (·≤·)).map fun a=>(a,TreeFraction.normalize (1,x.2)))++
    [(x.1.1,sub ((1,1),TreeFraction.normalize (x.1.2.card,x.2)))]
def neighborsRealizer : Realizer (neighbors (A:=A)) := by
  let headOptions : Realizer (fun x : (A×Finset A)×ℕ=>
      (x.1.2.sort (·≤·)).map fun a=>(a,TreeFraction.normalize (1,x.2))) :=
    (composition (pair (composition (pair (constant 1) second) normalizeRealizer)
      (composition first.snd finsetList)) (mapWith (pair second first))).congr (fun _=>rfl)
  let tailOptions : Realizer (fun x : (A×Finset A)×ℕ=>
      [(x.1.1,sub ((1,1),TreeFraction.normalize (x.1.2.card,x.2)))]) :=
    (composition (pair first.fst (composition (pair (constant (1,1))
      (composition (pair (composition first.snd finsetCard) second) normalizeRealizer)) subRealizer)) listSingleton).congr (fun _=>rfl)
  exact (composition (pair headOptions tailOptions) append).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeReach
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A C : Type} [Codec A] [Codec C] [LinearOrder A]

namespace FiniteReach
variable (p : C×(A×A) → Bool)

variable {p}
def neighbor (P : Realizer p) :
    Realizer (fun x : (C×A)×Finset A=>decide (∃ a∈x.2,p (x.1.1,(a,x.1.2))=true)) :=
  finsetAny (composition (pair first.fst (pair second first.snd)) P)

def growRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (grow p) :=
  (composition (pair second (composition (pair (pair first.fst second) first.snd)
    (finsetFilterWith (composition (pair (pair first.fst second) first.snd) (neighbor P))))) (finsetUnion E R)).congr (by
      intro x; ext a; simp only [grow,Function.comp_apply,decide_eq_true_eq])

def sweepRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (sweep p) :=
  pair first (growRealizer P E R)
def reachRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (reach p) :=
  composition (composition (pair (composition first.snd finsetCard) identity)
    (iterateDown (composition second (sweepRealizer P E R)))) second

end FiniteReach
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeReachCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C : Type} [Codec A] [Codec B] [Codec C] [LinearOrder A] [LinearOrder B]
def finsetImageWith {f : C×A → B} (F : Realizer f)
    (E : Realizer (fun x : B×B=>decide (x.1=x.2)))
    (R : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (fun x : C×Finset A=>x.2.image (fun a=>f (x.1,a))) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith F)) (listFinset E R)).congr (by
    intro x; ext b
    simp only [Function.comp_apply,List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_image])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {A C : Type} [Codec A] [Codec C] [LinearOrder A]
attribute [local instance] Transport.Sparse.finsetOrder

variable (p : C×(A×A) → Bool)
variable {p}
def adjacentRealizer (P : Realizer p) (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (adjacent p) :=
  (composition (pair (composition (composition second E) boolNot)
    (composition (pair (composition (pair second.fst first.snd) (finsetMember E))
      (composition (pair (composition (pair second.snd first.snd) (finsetMember E))
        (composition (pair first.fst second) P)) boolAnd)) boolAnd)) boolAnd).congr (by
          intro x
          change (!decide (x.2.1=x.2.2) && _) = _
          apply Bool.eq_iff_iff.mpr
          simp only [adjacent, Function.comp_apply, Bool.and_eq_true,
            Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq])
def componentRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (component (p:=p)) :=
  composition (pair first.snd (composition
    (pair (pair (pair first.fst.fst first.snd) first.fst.snd) (composition second finsetSingleton))
    (FiniteReach.reachRealizer (adjacentRealizer P E) E R))) (finsetInter E)

def orderedSetEqual (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>@decide (x.1=x.2) (LinearOrder.toDecidableEq x.1 x.2)) :=
  (finsetEqual E).congr (by intro x; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq])
def allComponentsRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (allComponents (p:=p)) :=
  (composition (pair identity second) (finsetImageWith (componentRealizer P E R) (orderedSetEqual E) (colexLe E R))).congr (by
    intro x; ext a; simp only [Function.comp_apply,id_eq,allComponents,Finset.mem_image])
def discrepanciesRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (discrepancies (p:=p)) :=
  (composition (pair (composition second (finsetInter E))
    (composition (pair first (composition second (finsetUnion E R))) (allComponentsRealizer P E R)))
    (finsetFilterWith (composition (composition (pair second first) (finsetSubset E)) boolNot))).congr (by
      intro x
      simp only [discrepancies,Function.comp_apply,Bool.not_eq_true',decide_eq_false_iff_not])
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeCycleTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder
def exchangeRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (exchange (E:=E)) :=
  (composition (pair (composition (pair first.fst second) (finsetSDiff Eq))
    (composition (pair first.snd second) (finsetInter Eq))) (finsetUnion Eq Le)).congr (fun _=>rfl)

def cycleRealizer {p : C×(E×E)→Bool} (P : Realizer p)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (cycle p) :=
  (choose (composition (pair second (composition (pair first.fst
    (composition first.snd (finsetUnion Eq Le))) (allComponentsRealizer P Eq Le)))
      (finsetMember (orderedSetEqual Eq)))
    (pair (composition (pair first.snd second) (exchangeRealizer Eq Le))
      (composition (pair (pair first.snd.snd first.snd.fst) second) (exchangeRealizer Eq Le)))
    first.snd).congr (by intro x; simp only [Function.comp_apply,decide_eq_true_eq,cycle])

def cycleTable (p : C×(E×E)→Bool) (x : CycleInput C E) : Options (PairState E) :=
  if (discrepancies (p:=p) x).card=0 then pure x.2 else
    ExecutableOptions.map (cycle p) (x,uniform (discrepancies (p:=p) x))
def cycleTableRealizer {p : C×(E×E)→Bool} (P : Realizer p)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (cycleTable p) :=
  (choose (composition (pair (composition (discrepanciesRealizer P Eq Le) finsetCard) (constant 0)) natEqual)
    (composition second pureRealizer)
    (composition (pair identity (composition (discrepanciesRealizer P Eq Le) uniformRealizer))
      (mapRealizer (cycleRealizer P Eq Le)))).congr (by intro x; simp only [Function.comp_apply,decide_eq_true_eq,cycleTable,id_eq])
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRationalWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped TreeFraction

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder

def weight (w : C×E→Fraction) (x : C×Finset E) : Fraction :=
  product ((x.2.sort (·≤·)).map (fun e=>w (x.1,e)))
def weightRealizer {w : C×E→Fraction} (W : Realizer w) : Realizer (weight w) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith W)) productRealizer).congr (fun _=>rfl)

def pairWeight (w z : C×E→Fraction) (x : C×PairState E) : Fraction :=
  mul (weight w (x.1,x.2.1),weight z (x.1,x.2.2))
def pairWeightRealizer {w z : C×E→Fraction} (W : Realizer w) (Z : Realizer z) : Realizer (pairWeight w z) :=
  (composition (pair (composition (pair first second.fst) (weightRealizer W))
    (composition (pair first second.snd) (weightRealizer Z))) mulRealizer).congr (fun _=>rfl)
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSlotWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def fuelPowerRealizer : Realizer fuelPower := composition (mapWith first) productRealizer
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped TreeFraction

def tierBase (n : ℕ) : Fraction := add ((1,1),div ((1,1),(n*n,1)))
def tierBaseRealizer : Realizer tierBase := (composition (pair (constant (1,1))
  (composition (pair (constant (1,1)) (pair (composition (pair identity identity) multiply) (constant 1))) divRealizer)) addRealizer).congr (fun _=>rfl)

def tierPower (x : TierInput) : Fraction :=
  fuelPower (tierBase x.1.1,x.1.2.take (x.1.2.length-x.2))
def tierPowerRealizer : Realizer tierPower := (composition (pair (composition first.fst tierBaseRealizer)
  (composition (pair first.snd (composition (pair (composition first.snd listLength) second) subtract)) takeFast)) fuelPowerRealizer).congr (fun _=>rfl)

def slotWeight (x : TierInput×Fraction) : Fraction :=
  maximum (div ((1,1),tierPower x.1),minimum (tierPower x.1,x.2))
def slotWeightRealizer : Realizer slotWeight := by
  let P : Realizer (fun x : TierInput×Fraction=>tierPower x.1) := (composition first tierPowerRealizer).congr (fun _=>rfl)
  exact (composition (pair (composition (pair (constant (1,1)) P) divRealizer)
    (composition (pair P second) minimumRealizer)) maximumRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableEstimator
open TreeTyped TreeFraction

def mean (xs : List Fraction) : Fraction := div (sum xs,(xs.length,1))
def meanRealizer : Realizer mean := composition
  (pair sumRealizer (pair listLength (constant 1))) divRealizer

def ratio (x : Fraction×Fraction) : Fraction :=
  if less ((0,1),x.1) then div (x.2,x.1) else (1,1)
def ratioRealizer : Realizer ratio :=
  (choose (composition (pair (constant (0,1)) first) lessRealizer)
    (composition (pair second first) divRealizer) (constant (1,1))).congr (fun _=>rfl)

def upper (x : ℕ×(Fraction×Fraction)) : Fraction :=
  if less ((0,1),x.2.1) then
    maximum ((1,100000),minimum ((3,1),add (div (mul ((x.1,1),x.2.2),x.2.1),(1,100000))))
  else (1,1)
def upperRealizer : Realizer upper := by
  let q : Realizer (fun x : ℕ×(Fraction×Fraction)=>
      div (mul ((x.1,1),x.2.2),x.2.1)) :=
    (composition (pair (composition (pair (pair first (constant 1)) second.snd) mulRealizer) second.fst) divRealizer).congr (fun _=>rfl)
  exact (choose (composition (pair (constant (0,1)) second.fst) lessRealizer)
    (composition (pair (constant (1,100000)) (composition (pair (constant (3,1))
      (composition (pair q (constant (1,100000))) addRealizer)) minimumRealizer)) maximumRealizer)
    (constant (1,1))).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableEstimator

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

instance instCodecSumOfInhabited [Inhabited A] [Inhabited B] : Codec (A⊕B) := ⟨fun x=>encode (sumRep x)⟩

def inl [Inhabited A] [Inhabited B] : Realizer (Sum.inl : A→A⊕B) :=
  (pair (constant true) (pair identity (constant (default : B)))).recode id Sum.inl (fun _=>rfl) (fun _=>rfl)
def inr [Inhabited A] [Inhabited B] : Realizer (Sum.inr : B→A⊕B) :=
  (pair (constant false) (pair (constant (default : A)) identity)).recode id Sum.inr (fun _=>rfl) (fun _=>rfl)

def sumCases [Inhabited A] [Inhabited B] {f : C×A→D} {g : C×B→D}
    (F : Realizer f) (G : Realizer g) : Realizer (fun x : C×(A⊕B)=>Sum.elim (fun a=>f (x.1,a)) (fun b=>g (x.1,b)) x.2) :=
  (choose second.fst (composition (pair first second.snd.fst) F)
    (composition (pair first second.snd.snd) G)).recode
      (fun x : C×(A⊕B)=>(x.1,sumRep x.2))
      (fun x=>Sum.elim (fun a=>f (x.1,a)) (fun b=>g (x.1,b)) x.2)
      (fun _=>rfl) (by intro x; cases x.2 <;> rfl)

def sumEqual [Inhabited A] [Inhabited B] [DecidableEq A] [DecidableEq B]
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (F : Realizer (fun x : B×B=>decide (x.1=x.2))) :
    Realizer (fun x : (A⊕B)×(A⊕B)=>decide (x.1=x.2)) :=
  (sumCases (composition (pair second first) (sumCases E (constant false)))
    (composition (pair second first) (sumCases (constant false) F))).congr (by
      intro x; rcases x with ⟨x,y⟩; cases x <;> cases y <;> simp [eq_comm])

def sumLexLe [Inhabited A] [Inhabited B] [LinearOrder A] [LinearOrder B]
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2)))
    (S : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (fun x : (A⊕B)×(A⊕B)=>decide (toLex x.1≤toLex x.2)) :=
  (sumCases (composition (pair second first) (sumCases (composition (pair second first) R) (constant false)))
    (composition (pair second first) (sumCases (constant true) (composition (pair second first) S)))).congr (by
      intro x; rcases x with ⟨x,y⟩; cases x <;> cases y <;> simp)
instance instCodecOptionOfInhabited [Inhabited A] : Codec (Option A) := ⟨fun x=>encode (optionRep x)⟩
def some [Inhabited A] : Realizer (Option.some : A→Option A) :=
  (pair (constant true) identity).recode id Option.some (fun _=>rfl) (fun _=>rfl)

def optionCases [Inhabited A] {f : C→D} {g : C×A→D} (F : Realizer f) (G : Realizer g) :
    Realizer (fun x : C×Option A=>x.2.elim (f x.1) (fun a=>g (x.1,a))) :=
  (choose second.fst (composition (pair first second.snd) G) (composition first F)).recode
    (fun x : C×Option A=>(x.1,optionRep x.2))
    (fun x=>x.2.elim (f x.1) (fun a=>g (x.1,a))) (fun _=>rfl) (by intro x; cases x.2 <;> rfl)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]

def indexStepRealizer (E : Realizer (fun x : A×A=>decide (x.1=x.2))) : Realizer (indexStep (A:=A)) :=
  (pair second.fst (choose (composition (pair second.fst first) E) (constant 0)
    (composition second.snd successor))).congr (fun x=>by simp only [indexStep,Function.comp_apply,decide_eq_true_eq,Nat.succ_eq_add_one])

omit [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A] in
lemma indexStep_fold_reverse [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) :
    (xs.reverse.foldl (fun z x=>indexStep (x,z)) (a,0)).2=xs.idxOf a := by
  rw [List.foldl_reverse]
  have h : xs.foldr (fun x z=>indexStep (x,z)) (a,0)=(a,xs.idxOf a) := by
    induction xs with
    | nil=>simp
    | cons x xs ih=>
      rw [List.foldr_cons,ih]
      simp only [indexStep,List.idxOf_cons]
      by_cases he : a=x
      · subst x; simp
      · simp [he,beq_eq_false_iff_ne.mpr (Ne.symm he)]
  rw [h]

def indexOf (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×List A=>x.2.idxOf x.1) :=
  (composition (composition (pair (composition second reverse) (pair first (constant 0)))
    (fold (indexStepRealizer E))) second).congr (fun x=>indexStep_fold_reverse x.2 x.1)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Related2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumberedHierarchy

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ)

omit [Fintype V] [LinearOrder V] in
lemma cast_related [Fintype V] [LinearOrder V] (t : ℚ) (x y : V) :
    related B t x y ↔ Hierarchy.Related (fun x y=>(B x y:ℝ)) (t:ℝ) x y := by
  simp only [related,Hierarchy.Related,Rat.cast_le]

variable (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

lemma related_trans (_hsym : ∀ x y,B x y=B y x)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (t : ℚ) {x y z : V} (hxy : related B t x y) (hyz : related B t y z) :
    related B t x z := by
  rw [cast_related] at *
  exact Hierarchy.related_trans _ (triangular B htri) _ hxy hyz

include hsym htri in
lemma component_eq_iff (t : ℚ) (x y : V) : component B t x=component B t y ↔ related B t x y := by
  constructor
  · intro h
    have := component_self B t y
    rw [←h] at this
    simpa [component] using this
  · intro h
    ext z
    simp only [component,mem_filter,mem_univ,true_and]
    exact ⟨fun hx=>related_trans B hsym htri t (related_symm B hsym t h) hx,
      fun hy=>related_trans B hsym htri t h hy⟩

include hsym htri in
lemma root_eq_iff (t : ℚ) (x y : V) : root B t x=root B t y ↔ related B t x y := by
  constructor
  · intro h
    have hx := related_root B t x
    rw [h] at hx
    exact related_trans B hsym htri t hx (related_symm B hsym t (related_root B t y))
  · intro h
    unfold root
    congr 1
    exact (component_eq_iff B hsym htri t x y).mpr h

include hsym htri in
lemma root_idem (t : ℚ) (x : V) : root B t (root B t x)=root B t x :=
  (root_eq_iff B hsym htri t _ _).mpr (related_symm B hsym t (related_root B t x))

def classOf (t : ℚ) (x : V) : NumberedComponent B t := ⟨root B t x,root_idem B hsym htri t x⟩

def labelAt {H : ℕ} (k : Fin (H+1)) (x : V) : Label B H :=
  ⟨k,classOf B hsym htri _ x⟩

variable {E : Type*} [Fintype E] [DecidableEq E] (left right : E → V)

def edgeLabel (H : ℕ) (e : E) : Label B H :=
  labelAt B hsym htri (level H (B (left e) (right e))) (left e)

def bags (H : ℕ) (x : V) : Finset (Label B H) :=
  (univ.filter (fun e=>x=left e ∨ x=right e)).image (edgeLabel B hsym htri left right H)

end MatchingFPRAS.NumberedHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeDyadic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction Polynomial

def level (x : ℕ×Fraction) : ℕ := min x.1 ((x.2.1/x.2.2).size-1)
def levelRealizer : Realizer level := composition (pair first
  (composition (composition (composition second quotient) bitSize) predecessor)) minNat

def threshold (x : List Bool×ℕ) : Fraction := (bitDenominator (x.1.take x.2),1)
def thresholdRealizer : Realizer threshold := pair (composition takeFast bitDenominatorRealizer) (constant 1)
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneckCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableBottleneck
open TreeTyped TreeFraction

def matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) : Matrix :=
  List.ofFn fun i=>List.ofFn fun j=>TreeFraction.repr (w i j)
end MatchingFPRAS.ExecutableBottleneck

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHierarchyRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

abbrev RootInput := (Matrix×Fraction)×ℕ

def related (x : RootInput×ℕ) : Bool :=
  decide (x.1.2=x.2) || !(TreeFraction.less (cell (x.1.1.1,(x.1.2,x.2)),x.1.1.2))
def relatedRealizer : Realizer related :=
  composition (pair (composition (pair first.snd second) natEqual)
    (composition (composition (pair
      (composition (pair first.fst.fst (pair first.snd second)) cellRealizer) first.fst.snd)
        lessRealizer) boolNot)) boolOr

def component (x : RootInput) : List ℕ := (List.range x.1.1.length).filter (fun y=>related (x,y))
def componentRealizer : Realizer component := composition
  (pair identity (composition (composition first.fst listLength) range)) (filterWith relatedRealizer)

def root (x : RootInput) : ℕ := listMin (component x,x.1.1.length)
def rootRealizer : Realizer root := composition (pair componentRealizer
  (composition first.fst listLength)) listMinRealizer
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

abbrev HierarchyInput := Matrix×List Bool

def labelRoot (x : HierarchyInput×LabelKey) : ℕ :=
  root ((x.1.1,threshold (x.1.2,x.2.1)),x.2.2)
def labelRootRealizer : Realizer labelRoot := composition
  (pair (pair first.fst (composition (pair first.snd second.fst) thresholdRealizer)) second.snd) rootRealizer

def fixedRoot (x : HierarchyInput×LabelKey) : Bool := decide (labelRoot x=x.2.2)
def fixedRootRealizer : Realizer fixedRoot := composition (pair labelRootRealizer second.snd) natEqual

def labels (x : HierarchyInput) : List LabelKey :=
  ((List.range (x.2.length+1)).flatMap fun k=>(List.range x.1.length).map fun v=>(k,v)).filter fun l=>fixedRoot (x,l)
def labelsRealizer : Realizer labels := by
  let ks : Realizer (fun x : HierarchyInput=>List.range (x.2.length+1)) :=
    composition (composition (composition second listLength) successor) range
  let vs : Realizer (fun x : HierarchyInput=>List.range x.1.length) :=
    composition (composition first listLength) range
  let row : Realizer (fun x : HierarchyInput×ℕ=>(List.range x.1.1.length).map fun v=>(x.2,v)) :=
    composition (pair second (composition first vs)) (mapWith (pair first second))
  exact (composition (pair identity (composition (composition (pair identity ks) (mapWith row)) flatten))
    (filterWith fixedRootRealizer)).congr (fun _=>rfl)

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeParentTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck

def parentKey (x : HierarchyInput×LabelKey) : LabelKey :=
  (x.2.1-1,labelRoot (x.1,(x.2.1-1,x.2.2)))
def parentKeyRealizer : Realizer parentKey := by
  let p : Realizer (fun x : HierarchyInput×LabelKey=>(x.2.1-1,x.2.2)) := pair (composition second.fst predecessor) second.snd
  exact (pair (composition second.fst predecessor) (composition (pair first p) labelRootRealizer)).congr (fun _=>rfl)

def parentEntry (x : (HierarchyInput×List LabelKey)×LabelKey) : Bool×ℕ :=
  if x.2.1=0 then (false,0) else (true,x.1.2.idxOf (parentKey (x.1.1,x.2)))
def parentEntryRealizer : Realizer parentEntry :=
  (choose (composition (pair second.fst (constant 0)) natEqual) (constant (false,0))
    (pair (constant true) (composition (pair (composition (pair first.fst second) parentKeyRealizer) first.snd)
      (indexOf (pairEqual natEqual natEqual))))).congr (fun x=>by simp only [parentEntry,Function.comp_apply,decide_eq_true_eq])

def parents (x : HierarchyInput) : ExecutableDP.Parents :=
  (labels x).map fun l=>parentEntry ((x,labels x),l)
def parentsRealizer : Realizer parents := composition (pair (pair identity labelsRealizer) labelsRealizer) (mapWith parentEntryRealizer)

def ranks (x : HierarchyInput) : List ℕ := (labels x).map Prod.fst
def ranksRealizer : Realizer ranks := composition labelsRealizer (map first)
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

abbrev BagInput := HierarchyInput×List (ℕ×ℕ)

def edgeKey (x : HierarchyInput×(ℕ×ℕ)) : LabelKey :=
  let k:=level (x.1.2.length,cell (x.1.1,x.2))
  (k,labelRoot (x.1,(k,x.2.1)))
def edgeKeyRealizer : Realizer edgeKey := by
  let k : Realizer (fun x : HierarchyInput×(ℕ×ℕ)=>level (x.1.2.length,cell (x.1.1,x.2))) :=
    composition (pair (composition first.snd listLength) (composition (pair first.fst second) cellRealizer)) levelRealizer
  exact (pair k (composition (pair first (pair k second.fst)) labelRootRealizer)).congr (fun _=>rfl)
def incidentRealizer : Realizer incident :=
  (composition (pair (composition (pair first second.fst) natEqual)
    (composition (pair first second.snd) natEqual)) boolOr).congr (fun _=>by simp only [incident,Bool.decide_or,Function.comp_apply])

def edgeIndex (x : (HierarchyInput×List LabelKey)×(ℕ×ℕ)) : ℕ :=
  x.1.2.idxOf (edgeKey (x.1.1,x.2))
def edgeIndexRealizer : Realizer edgeIndex := composition
  (pair (composition (pair first.fst second) edgeKeyRealizer) first.snd) (indexOf (pairEqual natEqual natEqual))

def bag (x : BagInput×ℕ) : List ℕ :=
  ((x.1.2.filter fun e=>incident (x.2,e)).map fun e=>edgeIndex ((x.1.1,labels x.1.1),e)).dedup
def bagRealizer : Realizer bag :=
  (composition (composition (pair (pair first.fst (composition first.fst labelsRealizer))
    (composition (pair second first.snd) (filterWith incidentRealizer))) (mapWith edgeIndexRealizer)) (dedup natEqual)).congr (fun _=>rfl)

def bagTable (x : BagInput) : ExecutableDP.Bags := (List.range x.1.1.length).map fun v=>bag (x,v)
def bagTableRealizer : Realizer bagTable := composition
  (pair identity (composition (composition first.fst listLength) range)) (mapWith bagRealizer)

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeNumberedCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]
instance (priority := 100) codec : Codec A := ⟨fun a=>encode (index a)⟩

def equal : Realizer (fun x : A×A=>decide (x.1=x.2)) :=
  natEqual.recode (fun x : A×A=>(index x.1,index x.2)) _ (fun _=>rfl) (fun x=>by
    simp only [(index_injective (A:=A)).eq_iff])
def lessEqual : Realizer (fun x : A×A=>decide (x.1≤x.2)) :=
  leNat.recode (fun x : A×A=>(index x.1,index x.2)) _ (fun _=>rfl) (fun x=>by
    simp only [index_le])
@[simp] lemma equal_program : (equal (A:=A)).program=natEqual.program := rfl
@[simp] lemma lessEqual_program : (lessEqual (A:=A)).program=leNat.program := rfl

end MatchingFPRAS.TreeTyped.Numbered

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
attribute [local instance] NumberedHierarchy.labelOrder
variable (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→V)
    (es : List (ℕ×ℕ))
    (hes : ∀ p,p∈es ↔ ∃ e,(index (left e),index (right e))=p)

noncomputable def arbitraryNumberedBags (v : V) :
    Finset (Fin (Fintype.card (Label B xs.length))) :=
  (NumberedHierarchy.bags B hsym htri left right xs.length v).map
    (UnitRefresh.orderedEnum (Label B xs.length)).symm.toEmbedding

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeQuad
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B]

def listProduct : Realizer (fun x : List A×List B=>x.1.product x.2) :=
  (composition (composition (pair second first)
    (mapWith (composition (pair second first) (mapWith (pair first second))))) flatten).congr (fun _=>rfl)
omit [Codec A] [Codec B] in
lemma quadList_ofFn (q : Quad A) : quadList q=List.ofFn (quadFn q) := by
  simp [quadList,quadFn,List.ofFn_succ]
def quadListRealizer : Realizer (quadList (A:=A)) :=
  (composition (pair first.fst (composition (pair first.snd
    (composition (pair second.fst (composition (pair second.snd (constant ([] : List A))) listCons)) listCons)) listCons)) listCons).congr (fun _=>rfl)
def quadsRealizer : Realizer (quads (A:=A)) :=
  (composition (pair (composition (pair identity identity) listProduct)
    (composition (pair identity identity) listProduct)) listProduct).congr (fun _=>rfl)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped Polynomial Enlargement RealGeometry

abbrev RawReal := RawLogical×ℕ
abbrev RawVertex := ℕ⊕RawReal

def logicalEdges (vs : List ℕ) : List RawLogical :=
  (vs.product vs).filter (fun e=>decide (e.1<e.2))
def logicalEdgesRealizer : Realizer logicalEdges :=
  (composition (composition (pair identity identity) listProduct) (filter less)).congr (fun _=>rfl)
def internalCountRealizer : Realizer internalCount :=
  (composition (pair (constant 4) (composition second listLength)) multiply).congr (fun _=>rfl)

def realEdges (x : GeometryInput) : List RawReal :=
  (logicalEdges x.1).product (List.range (internalCount x+1))
def realEdgesRealizer : Realizer realEdges := (composition
  (pair (composition first logicalEdgesRealizer)
    (composition (composition internalCountRealizer successor) range)) listProduct).congr (fun _=>rfl)

def vertices (x : GeometryInput) : List RawVertex :=
  x.1.map Sum.inl ++ ((logicalEdges x.1).product (List.range (internalCount x))).map Sum.inr
def verticesRealizer : Realizer vertices := (composition (pair
  (composition first (map inl))
  (composition (composition (pair (composition first logicalEdgesRealizer)
    (composition internalCountRealizer range)) listProduct) (map inr))) append).congr (fun _=>rfl)

def position (x : ℕ×RawReal) : RawVertex :=
  if x.2.2=0 then .inl x.2.1.1
  else if x.2.2=x.1+1 then .inl x.2.1.2
  else .inr (x.2.1,x.2.2-1)
def atRealizer : Realizer position :=
  (choose (composition (pair second.snd (constant 0)) natEqual)
    (composition second.fst.fst inl)
    (choose (composition (pair second.snd (composition first successor)) natEqual)
      (composition second.fst.snd inl)
      (composition (pair second.fst (composition second.snd predecessor)) inr))).congr (by
        intro x; simp [position])

def left (x : GeometryInput×RawReal) : RawVertex := position (internalCount x.1,x.2)
def right (x : GeometryInput×RawReal) : RawVertex := position (internalCount x.1,(x.2.1,x.2.2+1))
def leftRealizer : Realizer left := (composition (pair (composition first internalCountRealizer) second) atRealizer).congr (fun _=>rfl)
def rightRealizer : Realizer right := (composition (pair (composition first internalCountRealizer)
  (pair second.fst (composition second.snd successor))) atRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFastChoose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

def fastChoose : Realizer (fun x : ℕ×ℕ=>x.1.choose x.2) :=
  (choose (composition (pair second first) leNat) natChoose (constant 0)).congr (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq]
    split_ifs with h
    · rfl
    · exact (Nat.choose_eq_zero_of_lt (by omega)).symm)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastDPEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

def readFast : Realizer read :=
  composition (pair (composition (pair first second.fst) (getDFast [])) second.snd) (getDFast 0)
def contextFast : Realizer context := by
  let bl : Realizer (fun x : RawCtx=>(x.1.1,x.2.1)) := pair first.fst second.fst
  let p := composition bl privateNumberRealizer
  let q := composition bl sharedNumberRealizer
  let r := composition bl totalNumberRealizer
  exact (pair (composition (pair first.snd second.fst) (getDFast (false,0)))
    (pair second.fst (pair second.snd (pair p (pair q r))))).congr (fun _=>rfl)
def rawTermRealizer : Realizer rawTerm := by
  let raw : Realizer (fun x : (RawCtx×ℕ)×ℕ=>x.1.1) := first.fst
  let c := composition raw contextFast
  let r : Realizer (fun x : (RawCtx×ℕ)×ℕ=>x.1.2) := first.snd
  let k : Realizer (fun x : (RawCtx×ℕ)×ℕ=>x.2) := second
  let s := c.snd.snd.snd.snd.fst
  let u := c.snd.snd.snd.fst
  let t := c.snd.snd.fst
  let l := c.snd.fst
  let p := c.fst.snd
  let ch := composition (pair s k) fastChoose
  let L := composition (pair t (pair l (composition (pair u k) add))) readFast
  let R := composition (pair t (pair p (composition (pair (composition (pair s k) subtract) r) add))) readFast
  exact (composition (pair (composition (pair ch L) multiply) R) multiply).congr (fun _=>rfl)
def rawEntryRealizer : Realizer rawEntry := by
  let raw : Realizer (fun x : RawCtx×(ℕ×ℕ)=>x.1) := first
  let c := composition raw contextFast
  let a : Realizer (fun x : RawCtx×(ℕ×ℕ)=>x.2.1) := second.fst
  let r : Realizer (fun x : RawCtx×(ℕ×ℕ)=>x.2.2) := second.snd
  let l := c.snd.fst
  let rd := composition (pair c.snd.snd.fst (pair a r)) readFast
  let al := composition (pair a l) natEqual
  let ap := composition (pair a c.fst.snd) natEqual
  let ks := composition (composition c.snd.snd.snd.snd.fst successor) range
  let sm := composition (composition (pair (pair raw r) ks) (mapWith rawTermRealizer)) listSum
  let rt := composition (pair c.snd.snd.fst (pair l c.snd.snd.snd.snd.snd)) readFast
  exact (choose c.fst.fst (choose al (constant 1) (choose ap sm rd)) (choose al rt rd)).congr (by
    intro x; simp only [rawEntry,entry,rawTerm,Function.comp_apply,decide_eq_true_eq])
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeClippedDP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

def nVerticesRealizer : Realizer nVertices := composition first.fst listLength
def nLabelsRealizer : Realizer nLabels := composition first.snd listLength
def nPlanRealizer : Realizer nPlan := composition second listLength
def BInitialRealizer : Realizer BInitial := composition (pair nVerticesRealizer nLabelsRealizer) multiply
def capBitsRealizer : Realizer capBits := by
  let b:= BInitialRealizer
  let q:= composition (pair b b) multiply
  let v:= composition (pair q nLabelsRealizer) multiply
  let w:= composition (pair nVerticesRealizer nPlanRealizer) multiply
  exact (composition (composition (pair w v) add) successor).congr (by intro o; simp only [capBits,pow_two]; rfl)
def initialEntryRealizer : Realizer initialEntry :=
  composition (composition (pair second.snd (composition first BInitialRealizer)) minNat) pairingNumber
def initialFast : Realizer (fun o : CountInput=>initial (nLabels o,BInitial o)) :=
  (grid nLabelsRealizer BInitialRealizer initialEntryRealizer).congr (by
    intro o
    unfold tabulate initial initialEntry
    apply List.map_congr_left
    intro a _row_mem
    apply List.map_congr_left
    intro r hr
    have hh : r≤BInitial o := by have :=List.mem_range.mp hr; dsimp only at this; omega
    simp only [Nat.min_eq_left hh])
def updateRowsRealizer : Realizer updateRows := composition first.fst nLabelsRealizer
def updateColumnsRealizer : Realizer updateColumns :=
  composition (pair (composition first.fst nVerticesRealizer)
    (composition (pair second (composition first.fst nPlanRealizer)) minNat)) multiply
def cappedEntryRealizer : Realizer cappedEntry :=
  (composition (pair (composition first.fst.fst capBitsRealizer)
    (composition (pair first.fst.snd second) rawEntryRealizer)) clipRealizer).congr (fun _=>rfl)
def cappedUpdateRealizer : Realizer cappedUpdate := grid updateRowsRealizer updateColumnsRealizer cappedEntryRealizer

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeClippedRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

def cappedStepRealizer : Realizer cappedStep := by
  let o : Realizer (fun x : ℕ×CappedState=>x.2.1) := second.fst
  let st : Realizer (fun x : ℕ×CappedState=>x.2.2) := second.snd
  let rem := composition st.fst predecessor
  let bs := composition (pair st.snd.fst first) trimRealizer
  let inp := pair (pair o (pair (pair st.snd.fst o.fst.snd) (pair first st.snd.snd))) rem
  exact (pair o (pair rem (pair bs (composition inp cappedUpdateRealizer)))).congr (fun _=>rfl)

def finishFast : Realizer (fun x : CountInput×Table=>finish (x.2,nLabels x.1)) :=
  composition (composition (pair second (composition (composition first nLabelsRealizer) range))
    (mapWith (composition (pair first (pair second (constant 0))) readFast))) listProd
def cappedCountRealizer : Realizer cappedCount := by
  let init : Realizer (fun o : CountInput=>(o.2,(o,(o.2.length,(o.1.1,initial (nLabels o,BInitial o)))))) :=
    pair second (pair identity (pair nPlanRealizer (pair first.fst initialFast)))
  exact (composition (pair identity (composition (composition init (fold cappedStepRealizer)) second.snd.snd)) finishFast).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

def skipRealizer : Realizer skip := (choose less first (composition first successor)).congr (fun _=>by simp [skip])

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP TreeFraction

def decodeIndexRealizer : Realizer decodeIndex := division

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

def skipFast : Realizer skip := skipRealizer

def residualFast : Realizer residual := by
  let p : Realizer (fun x : (Bags×ℕ)×ℕ=>(x.1.1,skip (x.2,x.1.2))) :=
    pair first.fst (composition (pair second first.snd) skipFast)
  let n : Realizer (fun x : Bags×ℕ=>x.1.length-2) := composition (pair (composition first listLength) (constant 2)) subtract
  exact (composition (pair identity (composition n range))
    (mapWith (composition p (getDFast ([] : Bag))))).congr (fun _=>rfl)

def validFast : Realizer valid := by
  let bs : Realizer (fun x : Context×(ℕ×ℕ)=>x.1.1.1) := first.fst.fst
  let b : Realizer (fun x : Context×(ℕ×ℕ)=>x.2.1) := second.fst
  let c : Realizer (fun x : Context×(ℕ×ℕ)=>x.2.2) := second.snd
  let a := composition (composition bs listLength) predecessor
  let ba := composition (pair bs a) (getDFast ([] : Bag))
  let bb := composition (pair bs b) (getDFast ([] : Bag))
  let p := composition (composition (pair b a) natEqual) boolNot
  let q := composition (pair ba c) membership
  let r := composition (pair bb c) membership
  exact (composition (pair (composition (pair p q) boolAnd) r) boolAnd).congr (by intro x; simp [valid])
def fastBranchRealizer : Realizer fastBranch :=
  (composition (pair (pair (composition (pair first.fst.fst second) residualFast) first.fst.snd)
    first.snd) cappedCountRealizer).congr (fun _=>rfl)
def fastEdgeCountRealizer : Realizer fastEdgeCount :=
  (choose validFast (composition (pair first second.fst) fastBranchRealizer) (constant 0)).congr (fun _=>rfl)

def fastProbability (x : Context×ℕ) : TreeFraction.Fraction :=
  (fastEdgeCount (x.1,decodeIndex (x.2,x.1.1.2.length)),cappedCount x.1)
def fastProbabilityRealizer : Realizer fastProbability := by
  let m : Realizer (fun x : Context×ℕ=>x.1.1.2.length) := composition first.fst.snd listLength
  let bc := composition (pair second m) decodeIndexRealizer
  exact (pair (composition (pair first bc) fastEdgeCountRealizer)
    (composition first cappedCountRealizer)).congr (fun _=>rfl)

def fastProbabilities (x : Context) : List TreeFraction.Fraction :=
  (List.range (x.1.1.length*x.1.2.length)).map (fun i=>fastProbability (x,i))
def fastProbabilitiesRealizer : Realizer fastProbabilities := by
  let n : Realizer (fun x : Context=>x.1.1.length) := composition first.fst listLength
  let m : Realizer (fun x : Context=>x.1.2.length) := composition first.snd listLength
  exact (composition (pair identity (composition (composition (pair n m) multiply) range))
    (mapWith fastProbabilityRealizer)).congr (fun _=>rfl)

def fastDraw (x : Context×List Bool) : ℕ×ℕ :=
  decodeIndex (ExecutableChoice.chooseBits (fastProbabilities x.1,x.2),x.1.1.2.length)
def fastDrawRealizer : Realizer fastDraw :=
  (composition (pair (composition (pair (composition first fastProbabilitiesRealizer) second)
      ExecutableChoice.chooseBitsFast) (composition first.fst.snd listLength)) decodeIndexRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitAssemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

def unskipRealizer : Realizer unskip :=
  (choose less first (composition first predecessor)).congr (fun _=>by simp [unskip])

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCappedAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

def assembleAtFast : Realizer assembleAt := by
  let n : Realizer (fun x : (Frame×Result)×ℕ=>x.1.1.1) := first.fst.fst
  let b : Realizer (fun x : (Frame×Result)×ℕ=>x.1.1.2.1) := first.fst.snd.fst
  let c : Realizer (fun x : (Frame×Result)×ℕ=>x.1.1.2.2) := first.fst.snd.snd
  let i : Realizer (fun x : (Frame×Result)×ℕ=>x.2) := second
  let a := composition n successor
  let j := composition (pair i b) unskipRealizer
  let z := composition (pair first.snd j) (getDFast (0,0))
  let r := pair (composition (pair z.fst b) skipFast) z.snd
  exact (choose (composition (pair i a) natEqual) (pair b c)
    (choose (composition (pair i b) natEqual) (pair a c) r)).congr (by intro x; simp [assembleAt])
def capacityRealizer : Realizer capacity :=
  (composition (pair (composition (pair (composition first.fst listLength)
    (composition first.snd listLength)) add) (constant 2)) add).congr (fun _=>rfl)
def clippedAtRealizer : Realizer clippedAt := by
  let r : Realizer (fun x : (Context×(Frame×Result))×ℕ=>assembleAt (x.1.2,x.2)) := (composition (pair first.snd second) assembleAtFast).congr (fun _=>rfl)
  let cap : Realizer (fun x : (Context×(Frame×Result))×ℕ=>capacity x.1.1) := (composition first.fst capacityRealizer).congr (fun _=>rfl)
  exact (pair (composition (pair r.fst cap) minNat) (composition (pair r.snd cap) minNat)).congr (fun _=>rfl)
def clippedAssembleRealizer : Realizer clippedAssemble := by
  let n : Realizer (fun x : Context×(Frame×Result)=>x.2.1.1+2) := (composition (pair second.fst.fst (constant 2)) add).congr (fun _=>rfl)
  let m : Realizer (fun x : Context×(Frame×Result)=>x.1.1.1.length+2) := (composition (pair (composition first.fst.fst listLength) (constant 2)) add).congr (fun _=>rfl)
  let rs := composition (composition (pair n m) minNat) range
  exact (composition (pair identity rs) (mapWith clippedAtRealizer)).congr (fun _=>rfl)
def assemblyFoldStepRealizer : Realizer assemblyFoldStep :=
  (pair second.fst (composition (pair second.fst (pair first second.snd)) clippedAssembleRealizer)).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

def fastSelected (x : Context×Bits) : ℕ×ℕ := fastDraw (x.1,x.2.getD (x.1.1.1.length-1) [])
def fastSelectedRealizer : Realizer fastSelected := by
  let n : Realizer (fun x : Context×Bits=>x.1.1.1.length-1) := composition (composition first.fst.fst listLength) predecessor
  exact (composition (pair first (composition (pair second n) (getDFast []))) fastDrawRealizer).congr (fun _=>rfl)

def nextContextFast : Realizer nextContext :=
  (pair (pair (composition (pair first.fst.fst second.fst) residualFast) first.fst.snd) first.snd).congr (fun _=>rfl)

def fastStep (x : State) : State :=
  if 2≤x.1.1.1.length then
    let c:=fastSelected (x.1,x.2.1)
    (nextContext (x.1,c),(x.2.1,(x.1.1.1.length-2,c)::x.2.2))
  else x
def fastStepRealizer : Realizer fastStep := by
  let n : Realizer (fun x : State=>x.1.1.1.length) := composition first.fst.fst listLength
  let c : Realizer (fun x : State=>fastSelected (x.1,x.2.1)) := (composition (f:=fun x : State=>(x.1,x.2.1)) (pair first second.fst) fastSelectedRealizer).congr (fun _=>rfl)
  let ctx := composition (pair first c) nextContextFast
  let k := composition (pair n (constant 2)) subtract
  let fs := composition (pair (pair k c) second.snd) listCons
  let r := pair ctx (pair second.fst fs)
  exact (choose (composition (composition (pair n (constant 2)) less) boolNot) r identity).congr (by
    intro x; simp [fastStep,Nat.succ_le_iff])

def fastDescend (a : Context×Bits) : State :=
  countDown (fun y : ℕ×State=>fastStep y.2) a.1.1.1.length (a.1,(a.2,[]))
def fastDescendRealizer : Realizer fastDescend :=
  (composition (pair (composition first.fst.fst listLength) (pair first (pair second (constant ([] : List Frame)))))
    (iterateDown (composition second fastStepRealizer))).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_AdaptiveLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.Counting.scheduleDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Adaptive
open scoped Classical

structure Parameters (G : GraphInput) where
  hn : 2 ≤ G.n
  even : Even G.n
  K : ℕ
  epsilon : ℚ
  epsilon_pos : 0<epsilon
  epsilon_lt_one : epsilon<1
  schedule : Counting.scheduleAdmissible G.n epsilon K

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_1_r3b7075_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
structure Layer (p : Parameters G) (j : ℕ) where
  Ω : Type
  finite : Fintype Ω
  law : @Law Ω finite
  state : Ω → ScaleState G j
  ratios : Ω → Fin j → ℝ
  ratios_nonneg : ∀ x i,0 ≤ ratios x i

attribute [instance] Layer.finite

end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

def fastRawSample (cap : Context) : ℕ → Context → Bits → Result
  | 0,_,_ => []
  | f+1,x,bits => if 2≤x.1.1.length then
      let c:=fastSelected (x,bits)
      clippedAssemble (cap,((x.1.1.length-2,c),fastRawSample cap f (nextContext (x,c)) bits))
    else []
lemma fastDescend_unwind (cap : Context) (f : ℕ) (x : Context) (bs : Bits) (fs : List Frame) :
    unwindClipped cap (countDown (fun y : ℕ×State=>fastStep y.2) f (x,(bs,fs))).2.2 []=
      unwindClipped cap fs (fastRawSample cap f x bs) := by
  induction f generalizing x bs fs with
  | zero => rfl
  | succ f ih =>
    rw [countDown]
    by_cases h : 2≤x.1.1.length
    · have he : fastStep (x,(bs,fs))=(nextContext (x,fastSelected (x,bs)),(bs,(x.1.1.length-2,fastSelected (x,bs))::fs)) := by simp only [fastStep,h,↓reduceIte]
      rw [he,ih]
      simp only [fastRawSample,h,↓reduceIte]
      rfl
    · have he : fastStep (x,(bs,fs))=(x,(bs,fs)) := by simp only [fastStep,h,↓reduceIte]
      rw [he,ih]
      simp only [fastRawSample,h,↓reduceIte]
      have hz : fastRawSample cap f x bs=[] := by cases f <;> simp [fastRawSample,h]
      rw [hz]

def fastSample (x : Context×Bits) : Result := fastRawSample x.1 x.1.1.1.length x.1 x.2
def fastSampleRealizer : Realizer fastSample :=
  (composition (composition (pair fastDescendRealizer.snd.snd (pair first (constant ([] : Result))))
    (fold assemblyFoldStepRealizer)) second).congr (by
      intro x
      exact (fastDescend_unwind x.1 _ _ _ []).trans rfl)

open UnitRefresh.Materialized

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Polynomial

def orderedRealizer : Realizer ordered := (choose less identity (pair second first)).congr (by intro x; simp [ordered])
def rowKeyRealizer : Realizer rowKey := (pair
  (composition (pair second (composition (getDFast (0,0)) first)) orderedRealizer)
  (composition (getDFast (0,0)) second)).congr (fun _=>rfl)
def entryIndexRealizer : Realizer entryIndex := composition
  (pair (composition (pair first.snd second) rowKeyRealizer) first.fst)
  (indexOf (pairEqual (pairEqual natEqual natEqual) natEqual))
def matchingRealizer : Realizer matching := (composition
  (composition (pair identity (composition (composition second listLength) range))
    (mapWith entryIndexRealizer)) (listFinset natEqual leNat)).congr (fun _=>rfl)

section Source
open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)}
def key (e : BagEdge bags) : Key := ((e.val.val.1.inf.val,e.val.val.1.sup.val),e.val.val.2.val)
def catalog (bags : Fin n→Finset (Fin m)) : List Key :=
  List.ofFn (fun i=>key (orderedEnum (BagEdge bags) i))
end Source

def refresh (x : Input) : Finset ℕ := matching (x.1.1,fastSample (x.1.2,x.2))
def refreshRealizer : Realizer refresh := composition
  (pair first.fst (composition (pair first.snd second) fastSampleRealizer)) matchingRealizer

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped ExecutableDP ExecutableSource Polynomial

def sharedKeyRealizer : Realizer sharedKey := (composition (pair
  (composition (pair (composition (pair first second.fst.fst) (getDFast [])) second.snd) membership)
  (composition (pair (composition (pair first second.fst.snd) (getDFast [])) second.snd) membership))
  boolAnd).congr (by intro x; simp [sharedKey])

def storedCatalog (x : Bags×List ℕ) : List Key :=
  ((logicalEdges (List.range x.1.length)).product x.2).filter (fun e=>sharedKey (x.1,e))
def storedCatalogRealizer : Realizer storedCatalog := (composition (pair first
  (composition (pair (composition (composition (composition first listLength) range)
    logicalEdgesRealizer) second) listProduct)) (filterWith sharedKeyRealizer)).congr (fun _=>rfl)

open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
local instance (priority := 2000) instLTSym2OfLinearOrder_solutions {V : Type} [LinearOrder V] : LT (Sym2 V) := Transport.sym2Order.toLT
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshNumbered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
local instance (priority := 2000) instLTSym2OfLinearOrder_solutions_1 {V : Type} [LinearOrder V] : LT (Sym2 V) := Transport.sym2Order.toLT
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
def sourceKey (e : BagEdge bags) : Key :=
  ((Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup),Numbered.index e.val.val.2)
def sourceCatalog (bags : V→Finset L) : List Key :=
  List.ofFn (fun i=>sourceKey (orderedEnum (BagEdge bags) i))
omit [Fintype V] [Fintype L] [LinearOrder L] in
lemma edge_inf_lt_sup (e : BagEdge bags) : e.val.val.1.inf<e.val.val.1.sup := by
  apply lt_of_le_of_ne e.val.val.1.inf_le_sup
  intro h
  apply e.val.property
  rw [←Sym2.sortEquiv.symm_apply_apply e.val.val.1]
  change s(e.val.val.1.inf,e.val.val.1.sup).IsDiag
  rw [h]
  exact Sym2.mk_isDiag_iff.mpr rfl

def downEdge (e : BagEdge bags) : BagEdge (numberedBags bags) :=
  ⟨⟨(s((orderedEnum V).symm e.val.val.1.inf,(orderedEnum V).symm e.val.val.1.sup),
    (orderedEnum L).symm e.val.val.2),by
      rw [Sym2.mk_isDiag_iff]
      exact fun h=>(ne_of_lt (edge_inf_lt_sup e)) ((orderedEnum V).symm.injective h)⟩,by
    intro i hi
    rcases Sym2.mem_iff.mp hi with rfl|rfl
    · rw [mem_numberedBags]
      simpa only [ColoredEdge.color,Equiv.apply_symm_apply] using e.property _ (source_inf_mem _)
    · rw [mem_numberedBags]
      simpa only [ColoredEdge.color,Equiv.apply_symm_apply] using e.property _ (source_sup_mem _)⟩

def upEdge (e : BagEdge (numberedBags bags)) : BagEdge bags :=
  ⟨⟨(s(orderedEnum V e.val.val.1.inf,orderedEnum V e.val.val.1.sup),
    orderedEnum L e.val.val.2),by
      rw [Sym2.mk_isDiag_iff]
      exact fun h=>(ne_of_lt (edge_inf_lt_sup e)) ((orderedEnum V).injective h)⟩,by
    intro i hi
    rcases Sym2.mem_iff.mp hi with rfl|rfl
    · exact (mem_numberedBags bags _ _).mp (e.property _ (sym_inf_mem _))
    · exact (mem_numberedBags bags _ _).mp (e.property _ (sym_sup_mem _))⟩
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeRankPlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableDP Polynomial

def rankLeRealizer : Realizer (fun x : (ℕ×ℕ)×(ℕ×ℕ)=>decide (rankLe x.1 x.2)) :=
  (composition (pair (composition (pair second.fst first.fst) less)
    (composition (pair (composition (pair first.fst second.fst) natEqual)
      (composition (pair first.snd second.snd) leNat)) boolAnd)) boolOr).congr (by
        intro x
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
        rfl)
def rankEntriesRealizer : Realizer rankEntries := (composition (pair identity (composition listLength range))
  (mapWith (pair (getDFast 0) second))).congr (fun _=>rfl)
def rankPlanRealizer : Realizer rankPlan := composition (composition rankEntriesRealizer (insertionSort rankLe rankLeRealizer)) (map second)
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableRefresh NumberedHierarchy

def labelIndices (x : HierarchyInput) : List ℕ := List.range (labels x).length
def labelIndicesRealizer : Realizer labelIndices := (composition
  labelsRealizer (composition listLength range)).congr (fun _=>rfl)

def refreshTables (x : BagInput) : InitialInput :=
  let a:=bagTable x
  (storedCatalog (a,labelIndices x.1),((a,parents x.1),rankPlan (ranks x.1)))
def refreshTablesRealizer : Realizer refreshTables := (pair
  (composition (pair bagTableRealizer (composition first labelIndicesRealizer)) storedCatalogRealizer)
  (pair (pair bagTableRealizer (composition first parentsRealizer))
    (composition (composition first ranksRealizer) rankPlanRealizer))).congr (fun _=>rfl)

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

open Turing

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeStateTable
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A : Type} [Codec I] [Codec A] [DecidableEq I] [Inhabited I]
def lookupRealizer (d : A) (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (lookup (I:=I) d) := by
  let P : Realizer (fun x : I×(I×A)=>decide (x.2.1=x.1)) := composition (pair second.fst first) E
  let F := composition (pair second first) (filterWith P)

  let H : Realizer (fun x : I×List (I×A)=>((x.2.headD (x.1,d)).2)) :=
    (composition (choose (composition second isEmpty) (pair first (constant d))
      (composition second (head (default,d)))) second).congr (by
        intro x; rcases x with ⟨i,as⟩; cases as <;> rfl)
  exact (composition (pair second F) H).congr (fun _=>rfl)
def setStateRealizer (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (setState (I:=I) (A:=A)) :=
  (composition (pair second first) (mapWith (pair second.fst
    (choose (composition (pair second.fst first.fst) E) first.snd second.snd)))).congr (by
      intro x; simp only [setState,Function.comp_apply,decide_eq_true_eq])
def setPairRealizer (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (setPair (I:=I) (A:=A)) :=
  (composition (pair (composition (pair first (pair second.fst.fst second.snd.fst)) (setStateRealizer E))
    (pair second.fst.snd second.snd.snd)) (setStateRealizer E)).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder Polynomial

abbrev State := Matrix×Vector

def ratio (x : (Matrix×ℕ)×(ℕ×Fraction)) : Fraction :=
  div (cell (x.1.1,(x.1.2,x.2.1)),x.2.2)
def ratioRealizer : Realizer ratio := composition (pair
  (composition (pair first.fst (pair first.snd second.fst)) cellRealizer)
  second.snd) divRealizer

def rowMax (x : State×ℕ) : Fraction :=
  ((x.1.2.filter (fun z=>decide (z.1≠x.2))).map (fun z=>ratio ((x.1.1,x.2),z))).foldl
    (fun a b=>maximum (b,a)) (0,1)
def rowMaxRealizer : Realizer rowMax := by
  let neq : Realizer (fun z : ℕ×(ℕ×Fraction)=>decide (z.2.1≠z.1)) :=
    (composition (composition (pair second.fst first) natEqual) boolNot).congr (by intro x; simp)
  let vs : Realizer (fun x : State×ℕ=>x.1.2.filter (fun z=>decide (z.1≠x.2))) :=
    composition (pair second first.snd) (filterWith neq)
  let vals : Realizer (fun x : State×ℕ=>(x.1.2.filter (fun z=>decide (z.1≠x.2))).map (fun z=>ratio ((x.1.1,x.2),z))) :=
    composition (pair (pair first.fst second) vs) (mapWith ratioRealizer)
  exact (composition (pair vals (constant (0,1))) (fold maximumRealizer)).congr (fun _=>rfl)

def step (x : ℕ×State) : State :=
  (x.2.1,setState (x.2.2,(x.1,rowMax (x.2,x.1))))
def stepRealizer : Realizer step :=
  pair second.fst (composition (pair second.snd (pair first
    (composition (pair second first) rowMaxRealizer))) (setStateRealizer natEqual))

def initial (M : Matrix) : State := (M,(List.range M.length).map fun i=>(i,(2,1)))
def initialRealizer : Realizer initial :=
  pair identity (composition (composition listLength range) (map (pair identity (constant (2,1)))))

def scale (M : Matrix) : Vector :=
  ((List.range M.length).foldl (fun s i=>step (i,s)) (initial M)).2
def scaleRealizer : Realizer scale :=
  composition (composition (pair (composition listLength range) initialRealizer) (fold stepRealizer)) second
end MatchingFPRAS.ExecutableScaling

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeScalingCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder

variable {n : ℕ}
def vectorRep (v : Fin n→ℚ) : Vector := List.ofFn fun j=>(j.val,TreeFraction.repr (v j))

end MatchingFPRAS.ExecutableScaling

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Polynomial

abbrev ProfileData := List Bool×(Fraction×(Fraction×(Fraction×Fraction)))
def profile (x : ProfileData×ℕ) : Fraction :=
  let p:=x.1.1.length
  let v:=x.1.2
  if x.2<2*p then maximum (v.1,div (v.2.1,threshold (x.1.1++x.1.1,x.2/2)))
  else if x.2=2*p then v.2.2.2
  else maximum (v.1,div (v.2.2.1,threshold (x.1.1++x.1.1,(4*p-x.2)/2)))
def profileRealizer : Realizer profile := by
  let p : Realizer (fun x : ProfileData×ℕ=>x.1.1.length) := composition first.fst listLength
  let twoP := composition (pair (constant 2) p) multiply
  let fourP := composition (pair (constant 4) p) multiply
  let fuel : Realizer (fun x : ProfileData×ℕ=>x.1.1++x.1.1) := composition (pair first.fst first.fst) append
  let lpow := composition (pair fuel (composition (pair second (constant 2)) quotient)) thresholdRealizer
  let rpow := composition (pair fuel (composition (pair (composition (pair fourP second) subtract) (constant 2)) quotient)) thresholdRealizer
  exact (choose (composition (pair second twoP) less)
    (composition (pair first.snd.fst (composition (pair first.snd.snd.fst lpow) divRealizer)) maximumRealizer)
    (choose (composition (pair second twoP) natEqual) first.snd.snd.snd.snd
      (composition (pair first.snd.fst (composition (pair first.snd.snd.snd.fst rpow) divRealizer)) maximumRealizer))).congr (by intro x; simp [profile])

def height (x : Matrix×ℕ) : Fraction :=
  ExecutableScaling.rowMax ((x.1,(List.range x.1.length).map (fun i=>(i,(1,1)))),x.2)
def heightRealizer : Realizer height :=
  composition (pair (pair first (composition (composition (composition first listLength) range)
      (map (pair identity (constant (1,1)))))) second) ExecutableScaling.rowMaxRealizer

def maxHeight (M : Matrix) : Fraction :=
  ((List.range M.length).map (fun i=>height (M,i))).foldl (fun a b=>maximum (b,a)) (0,1)
def maxHeightRealizer : Realizer maxHeight := (composition
  (pair (composition (pair identity (composition listLength range)) (mapWith heightRealizer)) (constant (0,1)))
  (fold maximumRealizer)).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Polynomial Enlargement RealGeometry

abbrev PathData := (Matrix×Matrix)×List Bool

def path (x : PathData×RawReal) : Fraction :=
  profile ((x.1.2,(cell (x.1.1.2,x.2.1),
    (height (x.1.1.2,x.2.1.1),(height (x.1.1.2,x.2.1.2),cell (x.1.1.1,x.2.1))))),x.2.2)
def pathRealizer : Realizer path :=
  (composition (pair (pair first.snd (pair
    (composition (pair first.fst.snd second.fst) cellRealizer)
    (pair (composition (pair first.fst.snd second.fst.fst) heightRealizer)
      (pair (composition (pair first.fst.snd second.fst.snd) heightRealizer)
        (composition (pair first.fst.fst second.fst) cellRealizer))))) second.snd) profileRealizer).congr (fun _=>rfl)

def vertexEqual : Realizer (fun x : RawVertex×RawVertex=>decide (x.1=x.2)) :=
  sumEqual natEqual (pairEqual (pairEqual natEqual natEqual) natEqual)

def sameEnds (x : (RawVertex×RawVertex)×(RawVertex×RawVertex)) : Bool :=
  decide ((x.1.1=x.2.1 ∧ x.1.2=x.2.2) ∨ (x.1.1=x.2.2 ∧ x.1.2=x.2.1))
def sameEndsRealizer : Realizer sameEnds :=
  (composition (pair
    (composition (pair (composition (pair first.fst second.fst) vertexEqual)
      (composition (pair first.snd second.snd) vertexEqual)) boolAnd)
    (composition (pair (composition (pair first.fst second.snd) vertexEqual)
      (composition (pair first.snd second.fst) vertexEqual)) boolAnd)) boolOr).congr (by
        intro x; simp [sameEnds])

abbrev WeightedEdge := (RawVertex×RawVertex)×Fraction
abbrev PathTableInput := PathData×List ℕ

def pathRow (x : PathTableInput×RawReal) : WeightedEdge :=
  ((left ((x.1.2,x.1.1.2),x.2),right ((x.1.2,x.1.1.2),x.2)),path (x.1.1,x.2))
def pathRowRealizer : Realizer pathRow :=
  (pair (pair (composition (pair (pair first.snd first.fst.snd) second) leftRealizer)
    (composition (pair (pair first.snd first.fst.snd) second) rightRealizer))
      (composition (pair first.fst second) pathRealizer)).congr (fun _=>rfl)

def pathTable (x : PathTableInput) : List WeightedEdge :=
  (realEdges (x.2,x.1.2)).map (fun e=>pathRow (x,e))
def pathTableRealizer : Realizer pathTable :=
  (composition (pair identity (composition (pair second first.snd) realEdgesRealizer)) (mapWith pathRowRealizer)).congr (fun _=>rfl)

def contribution (x : (RawVertex×RawVertex)×WeightedEdge) : Fraction :=
  if sameEnds (x.1,x.2.1) then x.2.2 else (0,1)
def contributionRealizer : Realizer contribution :=
  (choose (composition (pair first second.fst) sameEndsRealizer) second.snd (constant (0,1))).congr (fun _=>rfl)

def activity (x : List WeightedEdge×(RawVertex×RawVertex)) : Fraction :=
  sum (x.1.map (fun e=>contribution (x.2,e)))
def activityRealizer : Realizer activity :=
  (composition (composition (pair second first) (mapWith contributionRealizer)) sumRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

abbrev MatrixInput := List WeightedEdge×List RawVertex

def activityRow (x : MatrixInput×RawVertex) : List Fraction :=
  x.1.2.map (fun y=>activity (x.1.1,(x.2,y)))
def activityRowRealizer : Realizer activityRow := (composition
  (pair (pair first.fst second) first.snd)
  (mapWith (composition (pair first.fst (pair first.snd second)) activityRealizer))).congr (fun _=>rfl)

def activityMatrix (x : MatrixInput) : Matrix := x.2.map (fun v=>activityRow (x,v))
def activityMatrixRealizer : Realizer activityMatrix := composition (pair identity second) (mapWith activityRowRealizer)

def materialize (x : PathTableInput) : Matrix := activityMatrix (pathTable x,vertices (x.2,x.1.2))
def materializeRealizer : Realizer materialize := (composition (pair pathTableRealizer
  (composition (pair second first.snd) verticesRealizer)) activityMatrixRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBuild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

abbrev BuildInput := (Matrix×List Bool)×List Nat

def prepare (x : BuildInput) : PathTableInput := (((x.1.1,close x.1.1),x.1.2),x.2)
def prepareRealizer : Realizer prepare := (pair (pair (pair first.fst
  (composition first.fst closeRealizer)) first.snd) second).congr (fun _=>rfl)

def buildMatrix (x : BuildInput) : Matrix := materialize (prepare x)
def buildMatrixRealizer : Realizer buildMatrix := composition prepareRealizer materializeRealizer

def buildClosure (x : BuildInput) : Matrix := close (buildMatrix x)
def buildClosureRealizer : Realizer buildClosure := composition buildMatrixRealizer closeRealizer
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagBuild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
local instance instBEqRawVertex : BEq RawVertex := ⟨fun a b=>decide (a=b)⟩
local instance instLawfulBEqRawVertex : LawfulBEq RawVertex where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl

def endpointEntry (x : (GeometryInput×List RawVertex)×RawReal) : ℕ×ℕ :=
  (x.1.2.idxOf (left (x.1.1,x.2)),x.1.2.idxOf (right (x.1.1,x.2)))
def endpointEntryRealizer : Realizer endpointEntry := (pair
  (composition (pair (composition (pair first.fst second) leftRealizer) first.snd) (indexOf vertexEqual))
  (composition (pair (composition (pair first.fst second) rightRealizer) first.snd) (indexOf vertexEqual))).congr (fun _=>rfl)

def endpointList (x : GeometryInput) : List (ℕ×ℕ) :=
  (realEdges x).map (fun e=>endpointEntry ((x,vertices x),e))
def endpointListRealizer : Realizer endpointList := composition
  (pair (pair identity verticesRealizer) realEdgesRealizer) (mapWith endpointEntryRealizer)

abbrev BagBuildInput := BuildInput×List Bool
def buildBags (x : BagBuildInput) : ExecutableDP.Bags :=
  bagTable ((buildClosure x.1,x.2),endpointList (x.1.2,x.1.1.2))
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

def hierarchyFuel (x : Matrix×List Bool) : List Bool :=
  x.2.take (ExecutableHierarchy.level (x.2.length,maxHeight (close x.1)))
def hierarchyFuelRealizer : Realizer hierarchyFuel := (composition
  (pair second (composition (pair (composition second listLength)
    (composition (composition first closeRealizer) maxHeightRealizer)) levelRealizer)) takeFast).congr (fun _=>rfl)

attribute [local instance] NumberedHierarchy.labelOrder
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

def setupHierarchy (x : BagBuildInput) : BagInput :=
  ((buildClosure x.1,hierarchyFuel (x.1.1.1,x.2)),endpointList (x.1.2,x.1.1.2))
def setupHierarchyRealizer : Realizer setupHierarchy := (pair
  (pair (composition first buildClosureRealizer)
    (composition (pair first.fst.fst second) hierarchyFuelRealizer))
  (composition (pair first.snd first.fst.snd) endpointListRealizer)).congr (fun _=>rfl)

def sourceTables (x : BagBuildInput) : ExecutableRefresh.InitialInput :=
  refreshTables (setupHierarchy x)
def sourceTablesRealizer : Realizer sourceTables := composition setupHierarchyRealizer refreshTablesRealizer

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def coloredKey (x : HierarchyInput×(ℕ×ℕ)) : Key :=
  ((min x.2.1 x.2.2,max x.2.1 x.2.2),edgeIndex ((x.1,labels x.1),x.2))
def coloredKeyRealizer : Realizer coloredKey := (pair
  (pair (composition second TreeTyped.minimum) (composition second TreeTyped.maximum))
  (composition (pair (pair first (composition first labelsRealizer)) second) edgeIndexRealizer)).congr (fun _=>rfl)

def sourceRealKey (x : BagBuildInput×RawReal) : Key :=
  coloredKey ((setupHierarchy x.1).1,
    endpointEntry (((x.1.1.2,x.1.1.1.2),vertices (x.1.1.2,x.1.1.1.2)),x.2))
def sourceRealKeyRealizer : Realizer sourceRealKey := (composition
  (pair (composition first setupHierarchyRealizer).fst
    (composition (pair (pair (pair first.fst.snd first.fst.fst.snd)
      (composition (pair first.fst.snd first.fst.fst.snd) verticesRealizer)) second) endpointEntryRealizer)) coloredKeyRealizer).congr (fun _=>rfl)

def sourceRealIndex (x : BagBuildInput×RawReal) : ℕ :=
  (sourceTables x.1).1.idxOf (sourceRealKey x)
def keyLookup {A : Type} [Codec A] {f : A→Key} {g : A→List Key}
    (F : Realizer f) (G : Realizer g) : Realizer (fun x=>(g x).idxOf (f x)) :=
  composition (pair F G) (indexOf (pairEqual (pairEqual natEqual natEqual) natEqual))
def sourceRealIndexRealizer : Realizer sourceRealIndex :=
  keyLookup sourceRealKeyRealizer (composition (first (A:=BagBuildInput) (B:=RawReal)) sourceTablesRealizer).fst

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def coloredRow (x : BagBuildInput×RawReal) : Key×Fraction :=
  (sourceRealKey x,path ((prepare x.1.1).1,x.2))
def coloredRowRealizer : Realizer coloredRow := (pair sourceRealKeyRealizer
  (composition (pair (composition first.fst prepareRealizer).fst second) pathRealizer)).congr (fun _=>rfl)

def coloredRows (x : BagBuildInput) : List (Key×Fraction) :=
  (realEdges (x.1.2,x.1.1.2)).map (fun e=>coloredRow (x,e))
def coloredRowsRealizer : Realizer coloredRows := composition (pair identity
  (composition (pair first.snd first.fst.snd) realEdgesRealizer)) (mapWith coloredRowRealizer)

def colorContribution (x : Key×(Key×Fraction)) : Fraction :=
  if x.1=x.2.1 then x.2.2 else (0,1)
def colorContributionRealizer : Realizer colorContribution := (choose
  (composition (pair first second.fst) (pairEqual (pairEqual natEqual natEqual) natEqual)) second.snd
  (constant ((0,1) : Fraction))).congr (by intro x; simp only [colorContribution,Function.comp_apply,decide_eq_true_eq])

def realPart (x : BagBuildInput×Key) : Fraction :=
  sum ((coloredRows x.1).map (fun row=>colorContribution (x.2,row)))
def realPartRealizer : Realizer realPart := composition
  (composition (pair second (composition first coloredRowsRealizer)) (mapWith colorContributionRealizer)) sumRealizer
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePhantom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def sourceRanks (x : BagBuildInput) : List ℕ := ranks (setupHierarchy x).1
def sourceRanksRealizer : Realizer sourceRanks := composition setupHierarchyRealizer.fst ranksRealizer

def sourceRank (x : BagBuildInput×Key) : ℕ := (sourceRanks x.1).getD x.2.2 0
def sourceRankRealizer : Realizer sourceRank := composition
  (pair (composition first sourceRanksRealizer) second.snd) (getDFast 0)

def phantomHeight (x : BagBuildInput×Key) : Fraction := threshold (x.1.2,sourceRank x)
def phantomHeightRealizer : Realizer phantomHeight := composition
  (pair first.snd sourceRankRealizer) thresholdRealizer

def sourceBagWeight (x : (BagBuildInput×ℕ)×Key) : Fraction :=
  TreeFraction.add (realPart (x.1.1,x.2),
    TreeFraction.div (phantomHeight (x.1.1,x.2),(x.1.2,1)))
def sourceBagWeightRealizer : Realizer sourceBagWeight := (composition
  (pair (composition (pair first.fst second) realPartRealizer)
    (composition (pair (composition (pair first.fst second) phantomHeightRealizer)
      (pair first.snd (constant 1))) divRealizer)) addRealizer).congr (fun _=>rfl)

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeWeightTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def sourceWeights (x : BagBuildInput×ℕ) : List Fraction :=
  (sourceTables x.1).1.map (fun key=>sourceBagWeight (x,key))
def rowsWith {A B C : Type} [Codec A] [Codec B] [Codec C]
    {f : A×B→C} {g : A→List B} (F : Realizer f) (G : Realizer g) :
    Realizer (fun x=>(g x).map (fun b=>f (x,b))) :=
  composition (pair identity G) (mapWith F)
def sourceWeightsRealizer : Realizer sourceWeights := rowsWith sourceBagWeightRealizer
  (composition (first (A:=BagBuildInput) (B:=ℕ)) sourceTablesRealizer).fst

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeReweight
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder Enlargement RealGeometry

abbrev ReweightData := (Matrix×Matrix)×List Bool

def rawReweight (x : ReweightData×RawReal) : Fraction :=
  if x.2.2=2*x.1.2.length then div (cell (x.1.1.2,x.2.1),cell (x.1.1.1,x.2.1)) else (1,1)
def rawReweightRealizer : Realizer rawReweight :=
  (choose (composition (pair second.snd (composition
      (pair (constant 2) (composition first.snd listLength)) multiply)) natEqual)
    (composition (pair (composition (pair first.fst.snd second.fst) cellRealizer)
      (composition (pair first.fst.fst second.fst) cellRealizer)) divRealizer)
    (constant (1,1))).congr (by intro x; simp only [rawReweight,Function.comp_apply,decide_eq_true_eq])

variable {C E : Type} [Codec C] [Codec E] [DecidableEq E] [Inhabited E]
def reweightRow (color : C×RawReal→E) (x : (C×ReweightData)×RawReal) : E×Fraction :=
  (color (x.1.1,x.2),rawReweight (x.1.2,x.2))
def reweightRowRealizer {color : C×RawReal→E} (F : Realizer color) : Realizer (reweightRow color) :=
  (pair (composition (pair first.fst second) F)
    (composition (pair first.snd second) rawReweightRealizer)).congr (fun _=>rfl)

def reweightTable (color : C×RawReal→E) (x : (C×ReweightData)×List RawReal) : List (E×Fraction) :=
  x.2.map (fun r=>reweightRow color (x.1,r))
def reweightTableRealizer {color : C×RawReal→E} (F : Realizer color) : Realizer (reweightTable color) :=
  mapWith (reweightRowRealizer F)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeOptionsAccept
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

variable {A C Ω : Type} [Codec A] [Codec C]

def accept (p : C×A→Fraction) (x : (C×A)×Options A) : Options A :=
  (x.2.map fun a=>(a.1,mul (a.2,p (x.1.1,a.1))))++
    (x.2.map fun a=>(x.1.2,mul (a.2,sub ((1,1),p (x.1.1,a.1)))))
def acceptRealizer {p : C×A→Fraction} (P : Realizer p) : Realizer (accept p) := by
  let probability : Realizer (fun x : (C×A)×(A×Fraction)=>p (x.1.1,x.2.1)) :=
    composition (pair first.fst second.fst) P
  let yes := pair second.fst (composition (pair second.snd probability) mulRealizer)
  let no := pair first.snd (composition (pair second.snd
    (composition (pair (constant (1,1)) probability) subRealizer)) mulRealizer)
  exact (composition (pair (mapWith yes) (mapWith no)) append).congr (fun _=>rfl)

def metropolisProbability (w : C×A→Fraction) (x : (C×A)×A) : Fraction :=
  minimum ((1,1),div (w (x.1.1,x.2),w x.1))
def metropolisProbabilityRealizer {w : C×A→Fraction} (W : Realizer w) :
    Realizer (metropolisProbability w) :=
  (composition (pair (constant (1,1)) (composition (pair (composition (pair first.fst second) W)
    (composition first W)) divRealizer)) minimumRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeQuadDistinct
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A : Type} [Codec A] [LinearOrder A]
def listNodup (Eq : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (Le : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (fun xs : List A=>decide xs.Nodup) :=
  (composition (pair (composition (listFinset Eq Le) finsetCard) listLength) natEqual).congr (by
    intro xs
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,decide_eq_true_eq]
    exact Multiset.toFinset_card_eq_card_iff_nodup (m:= (xs : Multiset A)))

def quadInjective (Eq : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (Le : Realizer (fun x : A×A=>decide (x.1≤x.2))) :
    Realizer (fun q : Quad A=>decide (Function.Injective (quadFn q))) :=
  (composition quadListRealizer (listNodup Eq Le)).congr (by
    intro q
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,decide_eq_true_eq,quadList_ofFn,List.nodup_ofFn])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeSwitchValid
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]

def switchValidRealizer {p : C×(E×(V×V))→Bool} (P : Realizer p)
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (switchValid p) := by
  let V0 : Realizer (fun x : SwitchInput C E V=>x.2.1.1.1) := second.fst.fst.fst
  let V1 : Realizer (fun x : SwitchInput C E V=>x.2.1.1.2) := second.fst.fst.snd
  let V2 : Realizer (fun x : SwitchInput C E V=>x.2.1.2.1) := second.fst.snd.fst
  let V3 : Realizer (fun x : SwitchInput C E V=>x.2.1.2.2) := second.fst.snd.snd
  let E0 : Realizer (fun x : SwitchInput C E V=>x.2.2.1.1) := second.snd.fst.fst
  let E1 : Realizer (fun x : SwitchInput C E V=>x.2.2.1.2) := second.snd.fst.snd
  let E2 : Realizer (fun x : SwitchInput C E V=>x.2.2.2.1) := second.snd.snd.fst
  let E3 : Realizer (fun x : SwitchInput C E V=>x.2.2.2.2) := second.snd.snd.snd
  let T0 := composition (pair first.fst (pair E0 (pair V0 V1))) P
  let T1 := composition (pair first.fst (pair E1 (pair V1 V2))) P
  let T2 := composition (pair first.fst (pair E2 (pair V2 V3))) P
  let T3 := composition (pair first.fst (pair E3 (pair V3 V0))) P
  let allFits := composition (pair (composition (pair T0 T1) boolAnd) (composition (pair T2 T3) boolAnd)) boolAnd
  let distinctEdges := composition (composition (pair E0 E2) EqE) boolNot
  let membership := composition (pair (composition (pair E0 first.snd) (finsetMember EqE))
    (composition (pair E2 first.snd) (finsetMember EqE))) boolAnd
  exact (composition (pair (composition second.fst (quadInjective EqV LeV))
    (composition (pair allFits (composition (pair distinctEdges membership) boolAnd)) boolAnd)) boolAnd).congr (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,
        decide_eq_true_eq,switchValid]
      apply and_congr_right'
      apply and_congr_left'
      constructor
      · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ i
        fin_cases i <;> assumption
      · intro h
        exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩)
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeSwitchRaw
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def pairSetRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (pairSet (E:=E)) :=
  (composition (pair first (composition second finsetSingleton)) (finsetInsert Eq Le)).congr (fun _=>rfl)
def switchEditRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (switchEdit (E:=E)) :=
  (composition (pair (composition (pair first (composition (pair second.fst.fst second.snd.fst)
    (pairSetRealizer Eq Le))) (finsetSDiff Eq))
    (composition (pair second.fst.snd second.snd.snd) (pairSetRealizer Eq Le))) (finsetUnion Eq Le)).congr (fun _=>rfl)
def switchListRealizer {p : C×(E×(V×V))→Bool} (P : Realizer p)
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (switchList p) :=
  (composition (pair (pair first.fst second)
    (composition (pair (composition (composition first.snd.fst finsetList) quadsRealizer)
      (composition (composition first.snd.snd finsetList) quadsRealizer)) listProduct))
    (filterWith (switchValidRealizer P EqE EqV LeV))).congr (fun _=>rfl)

def switchRawRealizer {p : C×(E×(V×V))→Bool} (P : Realizer p)
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (LeE : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (switchRaw p) :=
  (composition (composition (pair second (switchListRealizer P EqE EqV LeV))
    (mapWith (composition (pair first second.snd) (switchEditRealizer EqE LeE))))
    (listFinset (orderedSetEqual EqE) (colexLe EqE LeE))).congr (by
      intro x; ext a; simp only [Function.comp_apply, List.mem_toFinset, switchRaw])
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeMatchingCheck
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]

def matchingCheckRealizer {p : C×(E×V)→Bool} (P : Realizer p) :
    Realizer (matchingCheck p) := by
  let incident : Realizer (fun x : (C×V)×E=>p (x.1.1,(x.2,x.1.2))) :=
    composition (pair first.fst (pair second first.snd)) P
  let degree : Realizer (fun x : (C×Finset E)×V=>
      (x.1.2.filter (fun e=>p (x.1.1,(e,x.2))=true)).card) :=
    (composition (composition (pair (pair first.fst second) first.snd)
      (finsetFilterWith incident)) finsetCard).congr (fun _=>rfl)
  exact (composition (pair (pair first.fst second) first.snd)
    (finsetAll (composition (pair degree (constant 1)) natEqual))).congr (by
      intro x; simp only [Function.comp_apply,decide_eq_true_eq]; rfl)
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCertify
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def certifyRealizer {p : C×(E×V)→Bool} (P : Realizer p) : Realizer (certify p) :=
  (finsetFilterWith (matchingCheckRealizer P)).congr (fun _=>rfl)
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColorRaw
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder

def colorRawRealizer {p : C×(E×E)→Bool} (P : Realizer p)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (colorRaw p) := by
  let choices : Realizer (fun x : ((C×Finset E)×Finset E)×E=>
      x.1.1.2.filter (fun f=>p (x.1.1.1,(f,x.2))=true)) :=
    (composition (pair (pair first.fst.fst second) first.fst.snd)
      (finsetFilterWith (composition (pair first.fst (pair second first.snd)) P))).congr (fun _=>rfl)
  let edit : Realizer (fun x : (((C×Finset E)×Finset E)×E)×E=>
      insert x.2 (x.1.1.2.erase x.1.2)) :=
    (composition (pair second (composition (pair first.snd first.fst.snd) (finsetErase Eq))) (finsetInsert Eq Le)).congr (fun _=>rfl)
  let neighbors : Realizer (fun x : ((C×Finset E)×Finset E)×E=>
      (x.1.1.2.filter (fun f=>p (x.1.1.1,(f,x.2))=true)).image fun f=>insert f (x.1.2.erase x.2)) :=
    (composition (pair identity choices) (finsetImageWith edit (orderedSetEqual Eq) (colexLe Eq Le))).congr (by
      intro x; ext a; simp only [Function.comp_apply,id_eq,Finset.mem_image])
  exact (composition (pair identity second)
    (finsetBiUnion neighbors (orderedSetEqual Eq) (colexLe Eq Le))).congr (by
      intro x; ext a; simp only [Function.comp_apply,id_eq,colorRaw,Finset.mem_biUnion,Finset.mem_image])
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseNeighbors
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def colorTable (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (x : TableInput C E V) : Options (Finset E) :=
  neighbors ((x.2,(certify p ((x.1.1,x.1.2.1),colorRaw q ((x.1.1,x.1.2.2),x.2))).erase x.2),x.1.2.1.card)
def colorTableRealizer {p : C×(E×V)→Bool} {q : C×(E×E)→Bool}
    (P : Realizer p) (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (colorTable p q) :=
  (composition (pair (pair second (composition (pair second (composition
    (pair (pair first.fst first.snd.fst) (composition (pair (pair first.fst first.snd.snd) second)
      (colorRawRealizer Q Eq Le))) (certifyRealizer P))) (finsetErase (orderedSetEqual Eq))))
    (composition first.snd.fst finsetCard)) neighborsRealizer).congr (by
      intro x
      apply congrArg neighbors
      dsimp only [Function.comp_apply]
      congr 2
      ext b
      simp only [Finset.mem_erase])
def degreeRealizer : Realizer degree := by
  let half : Realizer (fun n : ℕ=>n/2) := composition (pair identity (constant 2)) quotient
  let chooseTwo : Realizer (fun n : ℕ=>n.choose 2) :=
    (composition (pair (composition (pair identity (composition (pair identity (constant 1)) subtract)) multiply)
      (constant 2)) quotient).congr (fun n=>Nat.choose_two_right n |>.symm)
  exact (composition (pair (constant 8) (composition half chooseTwo)) multiply).congr (fun _=>rfl)

def switchTable (p : C×(E×V)→Bool) (q : C×(E×(V×V))→Bool) (x : TableInput C E V) : Options (Finset E) :=
  neighbors ((x.2,(certify p ((x.1.1,x.1.2.1),switchRaw q x)).erase x.2),degree x.1.2.1.card)
def switchTableRealizer {p : C×(E×V)→Bool} {q : C×(E×(V×V))→Bool}
    (P : Realizer p) (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (switchTable p q) :=
  (composition (pair (pair second (composition (pair second (composition
    (pair (pair first.fst first.snd.fst) (switchRawRealizer Q Eq Le EqV LeV)) (certifyRealizer P)))
    (finsetErase (orderedSetEqual Eq))))
    (composition (composition first.snd.fst finsetCard) degreeRealizer)) neighborsRealizer).congr (by
      intro x
      apply congrArg neighbors
      dsimp only [Function.comp_apply]
      congr 2
      ext b
      simp only [Finset.mem_erase])
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePairTable
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def pairTable (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (x : PairInput C E V) : Options (PairState E) :=
  mix ((1,3),(ExecutableOptions.map (fun y : Finset E×Finset E=>(y.2,y.1))
    (x.2.2,switchTable p r (x.1,x.2.1)),
    mix ((1,2),(ExecutableOptions.map (fun y : Finset E×Finset E=>(y.2,y.1))
      (x.2.2,colorTable p q (x.1,x.2.1)),cycleTable t ((x.1.1,x.1.2.2),x.2)))))
def pairTableRealizer {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} (P : Realizer p) (Q : Realizer q) (R : Realizer r) (T : Realizer t)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (pairTable p q r t) :=
  (composition (pair (constant (1,3)) (pair
    (composition (pair second.snd (composition (pair first second.fst) (switchTableRealizer P R Eq Le EqV LeV)))
      (mapRealizer (pair second first)))
    (composition (pair (constant (1,2)) (pair
      (composition (pair second.snd (composition (pair first second.fst) (colorTableRealizer P Q Eq Le)))
        (mapRealizer (pair second first)))
      (composition (pair (pair first.fst first.snd.snd) second) (cycleTableRealizer T Eq Le)))) mixRealizer)))
    mixRealizer).congr (fun _=>rfl)
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePairStep
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions TreeFraction

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def pairStepTable (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (w z : C×E→Fraction) (x : PairInput C E V) : Options (PairState E) :=
  accept (metropolisProbability (pairWeight w z)) (((x.1.1,x.2),x.2),pairTable p q r t x)
def pairStepRealizer {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} {w z : C×E→Fraction}
    (P : Realizer p) (Q : Realizer q) (R : Realizer r) (T : Realizer t) (W : Realizer w) (Z : Realizer z)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (pairStepTable p q r t w z) :=
  (composition (pair (pair (pair first.fst second) second) (pairTableRealizer P Q R T Eq Le EqV LeV))
    (acceptRealizer (metropolisProbabilityRealizer (pairWeightRealizer W Z)))).congr (fun _=>rfl)

def pairDraw (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (w z : C×E→Fraction) (x : PairInput C E V×List Bool) : PairState E :=
  draw (∅,∅) (pairStepTable p q r t w z x.1,x.2)
def pairDrawRealizer {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} {w z : C×E→Fraction}
    (P : Realizer p) (Q : Realizer q) (R : Realizer r) (T : Realizer t) (W : Realizer w) (Z : Realizer z)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (pairDraw p q r t w z) :=
  (composition (pair (composition first (pairStepRealizer P Q R T W Z Eq Le EqV LeV)) second)
    (drawRealizer (∅,∅))).congr (fun _=>rfl)
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeFraction TreeTyped.SparseProgram

abbrev Context := List (ℕ×ℕ)×(List Fraction×List Fraction)
def endpoints (x : Context×ℕ) : ℕ×ℕ := x.1.1.getD x.2 (0,0)
def endpointsRealizer : Realizer endpoints := composition (pair first.fst second) (getDFast (0,0))
def incidentRealizer : Realizer incident := (composition (pair
  (composition (pair first.fst second) natEqual) (composition (pair first.snd second) natEqual))
  boolOr).congr (by intro x; simp [incident])
def sameRealizer : Realizer same := (composition (pair
  (composition (pair (composition (pair first.fst second.fst) natEqual)
    (composition (pair first.snd second.snd) natEqual)) boolAnd)
  (composition (pair (composition (pair first.fst second.snd) natEqual)
    (composition (pair first.snd second.fst) natEqual)) boolAnd)) boolOr).congr
    (by intro x; simp [same])
def adjacentRealizer : Realizer adjacent := composition (pair
  (composition (pair first second.fst) incidentRealizer)
  (composition (pair first second.snd) incidentRealizer)) boolOr

def p (x : Context×(ℕ×ℕ)) : Bool := incident (endpoints (x.1,x.2.1),x.2.2)
def q (x : Context×(ℕ×ℕ)) : Bool := same (endpoints (x.1,x.2.1),endpoints (x.1,x.2.2))
def r (x : Context×(ℕ×(ℕ×ℕ))) : Bool := same (endpoints (x.1,x.2.1),x.2.2)
def t (x : Context×(ℕ×ℕ)) : Bool := adjacent (endpoints (x.1,x.2.1),endpoints (x.1,x.2.2))
def u (x : Context×ℕ) : Fraction := x.1.2.1.getD x.2 (0,1)
def v (x : Context×ℕ) : Fraction := x.1.2.2.getD x.2 (0,1)
def pRealizer : Realizer p := composition (pair (composition (pair first second.fst) endpointsRealizer) second.snd) incidentRealizer
def qRealizer : Realizer q := composition (pair (composition (pair first second.fst) endpointsRealizer)
  (composition (pair first second.snd) endpointsRealizer)) sameRealizer
def rRealizer : Realizer r := composition (pair (composition (pair first second.fst) endpointsRealizer) second.snd) sameRealizer
def tRealizer : Realizer t := composition (pair (composition (pair first second.fst) endpointsRealizer)
  (composition (pair first second.snd) endpointsRealizer)) adjacentRealizer
def uRealizer : Realizer u := composition (pair first.snd.fst second) (getDFast (0,1))
def vRealizer : Realizer v := composition (pair first.snd.snd second) (getDFast (0,1))

def draw := pairDraw p q r t u v
def drawRealizer : Realizer draw := pairDrawRealizer pRealizer qRealizer rRealizer tRealizer
  uRealizer vRealizer natEqual leNat natEqual leNat
end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPairCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeFraction TreeTyped.SparseProgram TreeTyped.Numbered

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
def contextRep (ends : E→Sym2 V) (w z : E→ℚ) : Context :=
  (List.ofFn (fun i=>endpointRep (ends (UnitRefresh.orderedEnum E i))),
    (List.ofFn (fun i=>TreeFraction.repr (w (UnitRefresh.orderedEnum E i))),
     List.ofFn (fun i=>TreeFraction.repr (z (UnitRefresh.orderedEnum E i)))))
end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPairUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeFraction TreeTyped.SparseProgram TreeTyped.Numbered

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
def typedP (x : Context×(E×V)) : Bool := p (x.1,(index x.2.1,index x.2.2))
def typedQ (x : Context×(E×E)) : Bool := q (x.1,(index x.2.1,index x.2.2))
def typedR (x : Context×(E×(V×V))) : Bool := r (x.1,(index x.2.1,(index x.2.2.1,index x.2.2.2)))
def typedT (x : Context×(E×E)) : Bool := t (x.1,(index x.2.1,index x.2.2))
def typedU (x : Context×E) : Fraction := u (x.1,index x.2)
def typedV (x : Context×E) : Fraction := v (x.1,index x.2)
def typedPRealizer : Realizer (typedP (E:=E) (V:=V)) := pRealizer.recode
  (fun x : Context×(E×V)=>(x.1,(index x.2.1,index x.2.2))) _ (fun _=>rfl) (fun _=>rfl)
def typedQRealizer : Realizer (typedQ (E:=E)) := qRealizer.recode
  (fun x : Context×(E×E)=>(x.1,(index x.2.1,index x.2.2))) _ (fun _=>rfl) (fun _=>rfl)
def typedRRealizer : Realizer (typedR (E:=E) (V:=V)) := rRealizer.recode
  (fun x : Context×(E×(V×V))=>(x.1,(index x.2.1,(index x.2.2.1,index x.2.2.2)))) _ (fun _=>rfl) (fun _=>rfl)
def typedTRealizer : Realizer (typedT (E:=E)) := tRealizer.recode
  (fun x : Context×(E×E)=>(x.1,(index x.2.1,index x.2.2))) _ (fun _=>rfl) (fun _=>rfl)
def typedURealizer : Realizer (typedU (E:=E)) := uRealizer.recode
  (fun x : Context×E=>(x.1,index x.2)) _ (fun _=>rfl) (fun _=>rfl)
def typedVRealizer : Realizer (typedV (E:=E)) := vRealizer.recode
  (fun x : Context×E=>(x.1,index x.2)) _ (fun _=>rfl) (fun _=>rfl)

def typedDraw := pairDraw (typedP (E:=E) (V:=V)) typedQ typedR typedT typedU typedV
def typedDrawRealizer : Realizer (typedDraw (E:=E) (V:=V)) :=
  pairDrawRealizer typedPRealizer typedQRealizer typedRRealizer typedTRealizer
    typedURealizer typedVRealizer Numbered.equal Numbered.lessEqual Numbered.equal Numbered.lessEqual
end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPairPost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeTyped.SparseProgram TreeTyped.Numbered Turing

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
def numericInput (x : PairInput Context E V×List Bool) : PairInput Context ℕ ℕ×List Bool :=
  (((x.1.1.1,(Numbered.set x.1.1.2.1,Numbered.set x.1.1.2.2)),
    (Numbered.set x.1.2.1,Numbered.set x.1.2.2)),x.2)
end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeStateNormalize
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E : Type} [Codec I] [Codec E] [DecidableEq I] [Inhabited I] [LinearOrder E]
def normalizeStateRealizer (Eq : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (normalizeState (I:=I) (E:=E)) :=
  (composition (pair identity first.fst) (mapWith (pair second
    (composition (pair (composition (pair first.snd second) (lookupRealizer ∅ Eq)) first.fst.snd)
      (finsetInter EqE))))).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLocalSampler
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A B C : Type} [Codec I] [Codec A] [Codec B] [Codec C]
variable [DecidableEq I] [Inhabited I] [Inhabited A]
def localPairRealizer {p : LocalPairInput C I A B→A×A} (P : Realizer p)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (localPair p) := by
  let a : Realizer (fun x : LocalContext C I A B×(I×I)=>lookup default (x.1.2.1,x.2.1)) :=
    (composition (pair first.snd.fst second.fst) (lookupRealizer (default : A) E)).congr (fun _=>rfl)
  let b : Realizer (fun x : LocalContext C I A B×(I×I)=>lookup default (x.1.2.1,x.2.2)) :=
    (composition (pair first.snd.fst second.snd) (lookupRealizer (default : A) E)).congr (fun _=>rfl)
  exact (composition (pair first.snd.fst (pair second
    (composition (pair (pair first.fst second) (pair (pair a b) first.snd.snd)) P)))
      (setPairRealizer E)).congr (fun _=>rfl)
def localRefreshRealizer {r : LocalRefreshInput C I B→A} (R : Realizer r)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (localRefresh r) :=
  (composition (pair first.snd.fst (pair second
    (composition (pair (pair first.fst second) first.snd.snd) R))) (setStateRealizer E)).congr (fun _=>rfl)
attribute [local instance] OAI.MatchingFPRAS.ExecutableLadder.treeLocalSamplerUpdateInhabited
def localSamplerRealizer {p : LocalPairInput C I A B→A×A} {r : LocalRefreshInput C I B→A}
    (P : Realizer p) (R : Realizer r) (E : Realizer (fun x : I×I=>decide (x.1=x.2))) :
    Realizer (localSampler p r) :=
  (optionCases second.fst (sumCases (localPairRealizer P E) (localRefreshRealizer R E))).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScanChoice
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped ExecutableOptions

variable {I C : Type} [Codec I] [Codec C] [Inhabited I] [LinearOrder I]
attribute [local instance] Transport.prodOrder Transport.sumOrder

def updateListRealizer {g : C×(I×I)→Bool} (G : Realizer g) : Realizer (updateList g) := by
  let xs : Realizer (fun x : ScanSetup C I=>x.2.1.sort (·≤·)) := (composition second.fst finsetList).congr (fun _=>rfl)
  let ps := composition (pair xs xs) listProduct
  let good := composition (pair first ps) (filterWith G)
  exact (composition (pair (composition good (TreeTyped.map inl))
    (composition (composition second.snd finsetList) (TreeTyped.map inr))) append).congr (fun _=>rfl)

def updateEqual (E : Realizer (fun x : I×I=>decide (x.1=x.2))) :
    Realizer (fun x : Replica.Update I×Replica.Update I=>@decide (x.1=x.2) (LinearOrder.toDecidableEq x.1 x.2)) :=
  (sumEqual (pairEqual E E) E).congr (by
    intro x; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq])

def updateSetRealizer {g : C×(I×I)→Bool} (G : Realizer g)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (R : Realizer (fun x : I×I=>decide (x.1≤x.2))) :
    Realizer (fun x=> (updateList g x).toFinset) :=
  (composition (updateListRealizer G)
    (listFinset (updateEqual E) (sumLexLe (lexLe E R R) R))).congr (by intro x; ext a; simp)

def scanChoice (g : C×(I×I)→Bool) (x : ScanSetup C I) : Options (Option (Replica.Update I)) :=
  mix ((1,2),(pure none,ExecutableOptions.map (fun x : Bool×Replica.Update I=>Option.some x.2)
    (false,uniform (updateList g x).toFinset)))
attribute [local instance] OAI.MatchingFPRAS.ExecutableLadder.instInhabitedUpdate
def scanChoiceRealizer {g : C×(I×I)→Bool} (G : Realizer g)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (R : Realizer (fun x : I×I=>decide (x.1≤x.2))) : Realizer (scanChoice g) :=
  (composition (pair (constant (1,2)) (pair (composition (constant none) pureRealizer)
    (composition (pair (constant false) (composition (updateSetRealizer G E R) uniformRealizer))
      (mapRealizer (composition second TreeTyped.some))))) mixRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScan
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped ExecutableOptions

variable {I A B C : Type} [Codec I] [Codec A] [Codec B] [Codec C]
variable [LinearOrder I] [Inhabited I] [Inhabited A]
attribute [local instance] Transport.prodOrder Transport.sumOrder

def scan (g : C×(I×I)→Bool) (p : LocalPairInput C I A B→A×A)
    (r : LocalRefreshInput C I B→A) (x : ScanInput C I A B) : StateTable I A :=
  localSampler p r ((x.1.1.1,(x.1.2,x.2.2)),draw none (scanChoice g x.1.1,x.2.1))
attribute [local instance] OAI.MatchingFPRAS.ExecutableLadder.treeScanUpdateInhabited
def scanRealizer {g : C×(I×I)→Bool} {p : LocalPairInput C I A B→A×A}
    {r : LocalRefreshInput C I B→A} (G : Realizer g) (P : Realizer p) (R : Realizer r)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (L : Realizer (fun x : I×I=>decide (x.1≤x.2))) : Realizer (scan g p r) :=
  (composition (pair (pair first.fst.fst (pair first.snd second.snd))
    (composition (pair (composition first.fst (scanChoiceRealizer G E L)) second.fst) (drawRealizer none)))
    (localSamplerRealizer P R E)).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScanRun
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E B C : Type} [Codec I] [Codec E] [Codec B] [Codec C]
variable [LinearOrder I] [Inhabited I] [LinearOrder E]
attribute [local instance] Transport.prodOrder Transport.sumOrder

def runStep (g : C×(I×I)→Bool) (p : LocalPairInput C I (Finset E) B→Finset E×Finset E)
    (r : LocalRefreshInput C I B→Finset E) (x : (List Bool×B)×RunState C I E) : RunState C I E :=
  (x.2.1,normalizeState (x.2.1.2,scan g p r ((x.2.1.1,x.2.2),x.1)))
def runStepRealizer {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} (G : Realizer g) (P : Realizer p) (R : Realizer r)
    (Eq : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (Le : Realizer (fun x : I×I=>decide (x.1≤x.2)))
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (runStep g p r) :=
  (pair second.fst (composition (pair second.fst.snd
    (composition (pair (pair second.fst.fst second.snd) first) (scanRealizer G P R Eq Le)))
    (normalizeStateRealizer Eq EqE))).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeNumericLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder

abbrev PairSetup := (List (ℕ×ℕ)×List (List Fraction))×(Finset ℕ×Finset ℕ)
abbrev Context := (PairSetup×RefreshSetup)×List (List ℕ)

def row (x : Context×ℕ) : List Fraction := x.1.1.1.1.2.getD x.2 []

def guide (x : Context×(ℕ×ℕ)) : Bool := decide (x.2.2∈x.1.2.getD x.2.1 [])

def pairContext (x : Context×(ℕ×ℕ)) : ExecutablePair.Context :=
  (x.1.1.1.1.1,(row (x.1,x.2.1),row (x.1,x.2.2)))

def pairDraw (x : LocalPairInput Context ℕ (Finset ℕ) Bits) : Finset ℕ×Finset ℕ :=
  ExecutablePair.draw ((((pairContext x.1,x.1.1.1.1.2),x.2.1)),x.2.2.1)

def refresh (x : LocalRefreshInput Context ℕ Bits) : Finset ℕ :=
  ExecutableRefresh.refresh (x.1.1.1.2,x.2.2)

abbrev Input := List (List Bool×Bits)×(RunSetup Context ℕ ℕ×StateTable ℕ (Finset ℕ))
def execute (x : Input) : RunSetup Context ℕ ℕ×StateTable ℕ (Finset ℕ) :=
  x.1.foldl (fun z b=>runStep guide pairDraw refresh (b,z)) x.2
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeTierWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
abbrev TierData := (ℕ×List Bool)×(List Bool×List Fraction)

def slotCount (x : TierData) : ℕ := (x.1.2.length+1)*x.2.1.length

def slots (x : TierData) : List ℕ := List.range (slotCount x)

def weightRow (x : TierData×ℕ) : List Fraction :=
  x.1.2.2.map (fun w=>slotWeight ((x.1.1,x.2/x.1.2.1.length),w))

def weightRows (x : TierData) : List (List Fraction) := (slots x).map (fun i=>weightRow (x,i))
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeGuideTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

def slotUniverse (x : TierData) : Finset ℕ := (slots x).toFinset

def guideTest (x : (TierData×ℕ)×ℕ) : Bool :=
  decide (x.1.2/x.1.1.2.1.length<x.1.1.1.2.length ∧
    x.2/x.1.1.2.1.length=x.1.2/x.1.1.2.1.length+1)

def guideSet (x : TierData×ℕ) : Finset ℕ := (slotUniverse x.1).filter (fun j=>guideTest (x,j))

def guideRows (x : TierData) : List (List ℕ) := (slots x).map (fun i=>(guideSet (x,i)).sort (·≤·))

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePrepareLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

abbrev Prepared := (TierData×(List (ℕ×ℕ)×(Finset ℕ×Finset ℕ)))×RefreshSetup

def prepareContext (x : Prepared) : Context :=
  ((((x.1.2.1,weightRows x.1.1),x.1.2.2),x.2),guideRows x.1.1)

def baseTest (x : TierData×ℕ) : Bool := decide (x.2/x.1.2.1.length=x.1.1.2.length)

def baseSet (x : TierData) : Finset ℕ := (slotUniverse x).filter fun i=>baseTest (x,i)

def prepareSetup (x : Prepared) : RunSetup Context ℕ ℕ :=
  ((prepareContext x,(slotUniverse x.1.1,baseSet x.1.1)),(slots x.1.1,x.1.2.2.2))

def prepareState (x : Prepared×Finset ℕ) : RunState Context ℕ ℕ :=
  (prepareSetup x.1,(slots x.1.1.1).map (fun i=>(i,x.2)))

abbrev PreparedInput := List (List Bool×Bits)×(Prepared×Finset ℕ)
def preparedRun (x : PreparedInput) : RunState Context ℕ ℕ := execute (x.1,prepareState x.2)

def preparedTop (x : PreparedInput) : Finset ℕ := lookup ∅ ((preparedRun x).2,0)
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def sourceVertices (x : BagBuildInput) : List RawVertex := vertices (x.1.2,x.1.1.2)
def sourceVerticesRealizer : Realizer sourceVertices := composition
  (pair first.snd first.fst.snd) verticesRealizer

def sourceEdgeData (x : BagBuildInput) : List (ℕ×ℕ)×(Finset ℕ×Finset ℕ) :=
  (((sourceTables x).1.map Prod.fst),(rangeFromList (sourceVertices x),rangeFromList (sourceTables x).1))

abbrev GeneratedInput := (BagBuildInput×ℕ)×(List Bool×List Bool)
def generatedTier (x : GeneratedInput) : TierData :=
  (((sourceVertices x.1.1).length,x.2.1),(x.2.2,sourceWeights x.1))
def generatedTierRealizer : Realizer generatedTier := (pair
  (pair (composition (composition first.fst sourceVerticesRealizer) listLength) second.fst)
  (pair second.snd (composition first sourceWeightsRealizer))).congr (fun _=>rfl)

def generatedPrepared (x : GeneratedInput) : Prepared :=
  ((generatedTier x,sourceEdgeData x.1.1),sourceTables x.1.1)

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def evenTest : Realizer (fun n : ℕ=>decide (n%2=0)) :=
  composition (pair (composition (pair identity (constant 2)) remainder) (constant 0)) natEqual
def mateIndexRealizer : Realizer mateIndex := (choose evenTest
  (composition (pair identity (constant 1)) TreeTyped.add)
  (composition (pair identity (constant 1)) subtract)).congr (by intro n; simp only [mateIndex,Function.comp_apply,id_eq,decide_eq_true_eq])

def startSelected (e : RawReal) : Bool :=
  Subdivision.alternating (decide (mateIndex e.1.1=e.1.2)) e.2
def startSelectedRealizer : Realizer startSelected :=
  (choose (composition second evenTest)
    (composition (pair (composition first.fst mateIndexRealizer) first.snd) natEqual)
    (composition (composition (pair (composition first.fst mateIndexRealizer) first.snd) natEqual) boolNot)).congr
    (by intro e; simp only [startSelected,Subdivision.alternating,Function.comp_apply,decide_eq_true_eq])

def exactStart (x : BagBuildInput) : Finset ℕ :=
  (((realEdges (x.1.2,x.1.1.2)).filter startSelected).map
    (fun e=>sourceRealIndex (x,e))).toFinset
def exactStartRealizer : Realizer exactStart := (composition
  (composition (pair identity (composition (composition
    (pair first.snd first.fst.snd) realEdgesRealizer) (filter startSelectedRealizer)))
    (mapWith sourceRealIndexRealizer)) (listFinset natEqual leNat)).congr (fun _=>rfl)

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeMarking
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped TreeFraction ExecutableOptions ExecutableLadder

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]

def markEdge (g : C×E→Options ℕ) (x : (C×StateTable E (List Bool))×E) : E×ℕ :=
  (x.2,draw 0 (g (x.1.1,x.2),lookup [] (x.1.2,x.2)))
def markEdgeRealizer {g : C×E→Options ℕ} (G : Realizer g)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (markEdge g) :=
  (pair second (composition (pair (composition (pair first.fst second) G)
    (composition (pair first.snd second) (lookupRealizer [] Eq))) (drawRealizer 0))).congr (fun _=>rfl)

def assign (g : C×E→Options ℕ) (x : MarkInput C E) : Marks E :=
  (x.2.sort (·≤·)).map (fun e=>markEdge g (x.1,e))
def assignRealizer {g : C×E→Options ℕ} (G : Realizer g)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (assign g) :=
  composition (pair first (composition second finsetList)) (mapWith (markEdgeRealizer G Eq))
end MatchingFPRAS.ExecutableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeNumericMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder ExecutableMarking ExecutableOptions TreeTyped.Numbered UnitRefresh

abbrev Tables := List (Options ℕ)
def table (x : Tables×ℕ) : Options ℕ := x.1.getD x.2 []
def assign (x : MarkInput Tables ℕ) : Marks ℕ := ExecutableMarking.assign table x
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeProbe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def centralKey (x : BagBuildInput×RawLogical) : Key :=
  sourceRealKey (x.1,(x.2,2*x.1.1.1.2.length))
def centralKeyRealizer : Realizer centralKey := (composition
  (pair first (pair second (composition (pair (constant 2) (composition first.fst.fst.snd listLength)) multiply)))
  sourceRealKeyRealizer).congr (fun _=>rfl)

def centralKeys (x : BagBuildInput) : List Key :=
  (logicalEdges x.1.2).map (fun e=>centralKey (x,e))
def centralKeysRealizer : Realizer centralKeys := (rowsWith centralKeyRealizer
  (composition (first (A:=BuildInput) (B:=List Bool)).snd logicalEdgesRealizer)).congr (fun _=>rfl)

def isCentral (x : BagBuildInput×Key) : Bool := decide (x.2∈centralKeys x.1)

def probePart (x : (BagBuildInput×ℕ)×Key) : Fraction :=
  if isCentral (x.1.1,x.2) then TreeFraction.div ((1,1),(x.1.2,1)) else (0,1)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMarkTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry ExecutableOptions

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

abbrev MarkRowInput := (BagBuildInput×ℕ)×Key
def phantomPart (x : MarkRowInput) : Fraction :=
  TreeFraction.div (phantomHeight (x.1.1,x.2),(x.1.2,1))
def phantomPartRealizer : Realizer phantomPart := (composition
  (pair (composition (pair first.fst second) phantomHeightRealizer) (pair first.snd (constant 1))) divRealizer).congr (fun _=>rfl)

def markPortions (x : MarkRowInput) : Fraction×(Fraction×Fraction) :=
  (realPart (x.1.1,x.2),(TreeFraction.sub (phantomPart x,probePart x),probePart x))

def threeOptions (x : Fraction×(Fraction×Fraction)) : Options ℕ :=
  [(0,x.1),(1,x.2.1),(2,x.2.2)]

def sourceMarkRow (x : MarkRowInput) : Options ℕ :=
  (threeOptions (markPortions x)).map (fun a=>(a.1,TreeFraction.div (a.2,sourceBagWeight x)))

def sourceMarks (x : BagBuildInput×ℕ) : NumericMarking.Tables :=
  (sourceTables x.1).1.map (fun key=>sourceMarkRow (x,key))

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePreparedMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder

abbrev SampleContext := (Prepared×Finset ℕ)×Tables
abbrev SampleInput := SampleContext×SampleBits

def sample (x : SampleInput) : ExecutableMarking.Marks ℕ :=
  assign ((x.1.2,x.2.2),preparedTop (x.2.1,x.1.1))

open Replica.Ladder Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def generatedContext (x : GeneratedInput) : SampleContext :=
  ((generatedPrepared x,exactStart x.1.1),sourceMarks x.1)

def generatedMarked (x : GeneratedInput×SampleBits) : ExecutableMarking.Marks ℕ :=
  NumericMarking.sample (generatedContext x.1,x.2)

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeObservables
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped TreeFraction

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]

def zeroMarksRealizer : Realizer (zeroMarks (E:=E)) :=
  (composition (map (composition (pair second (constant 0)) natEqual)) all).congr (by
    intro xs; simp only [zeroMarks,Function.comp_def,List.all_map,Function.id_def])
def probeExpectedRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) :
    Realizer (probeExpected (E:=E)) :=
  (choose (composition (pair second.fst first) Eq) (constant 2) (constant 0)).congr (by
    intro x; simp only [probeExpected,Function.comp_apply,decide_eq_true_eq])
def probeFlagRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (probeFlag (E:=E)) :=
  (composition (pair (composition (mapWith (composition (pair second.fst first) Eq)) any)
    (composition (mapWith (composition (pair second.snd (probeExpectedRealizer Eq)) natEqual)) all)) boolAnd).congr (by
      intro x; simp only [probeFlag,Function.comp_def,List.any_map,List.all_map,Function.id_def])

def weighted (q : C×E→Fraction) (x : C×Marks E) : Fraction :=
  product (x.2.map (fun z=>q (x.1,z.1)))
def weightedRealizer {q : C×E→Fraction} (Q : Realizer q) : Realizer (weighted q) :=
  (composition (mapWith (composition (pair first second.fst) Q)) productRealizer).congr (fun _=>rfl)

def observableA (x : Marks E) : Fraction := if zeroMarks x then (1,1) else (0,1)
def observableARealizer : Realizer (observableA (E:=E)) :=
  (choose zeroMarksRealizer (constant (1,1)) (constant (0,1))).congr (fun _=>rfl)

def observableD (q : C×E→Fraction) (x : C×Marks E) : Fraction :=
  if zeroMarks x.2 then weighted q x else (0,1)
def observableDRealizer {q : C×E→Fraction} (Q : Realizer q) : Realizer (observableD q) :=
  (choose (composition second zeroMarksRealizer) (weightedRealizer Q) (constant (0,1))).congr (fun _=>rfl)
def eraseMarkRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (eraseMark (E:=E)) :=
  (filterWith (composition (composition (pair second.fst first) Eq) boolNot)).congr (by
    intro x; simp only [eraseMark,Function.comp_apply,decide_not])

def observableProbe (q : C×E→Fraction) (x : C×(E×Marks E)) : Fraction :=
  if probeFlag x.2 then weighted q (x.1,eraseMark x.2) else (0,1)
def observableProbeRealizer {q : C×E→Fraction} (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (observableProbe q) :=
  (choose (composition second (probeFlagRealizer Eq))
    (composition (pair first (composition second (eraseMarkRealizer Eq))) (weightedRealizer Q)) (constant (0,1))).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericStatistics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics

variable {E : Type} [Fintype E] [LinearOrder E]

abbrev Reweights := List (ℕ×Fraction)
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeReweightTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry ExecutableLadder

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
abbrev SourceReweightInput := BagBuildInput×Matrix

def sourceReweightData (x : SourceReweightInput) : ReweightData :=
  ((x.1.1.1.1,x.2),x.1.1.1.2)
def sourceReweightDataRealizer : Realizer sourceReweightData := (pair
  (pair first.fst.fst.fst second) first.fst.fst.snd).congr (fun _=>rfl)

def sourceReweightRows (x : SourceReweightInput) : List (Key×Fraction) :=
  reweightTable sourceRealKey ((x.1,sourceReweightData x),realEdges (x.1.1.2,x.1.1.1.2))
def sourceReweightRowsRealizer : Realizer sourceReweightRows := (composition
  (pair (pair first sourceReweightDataRealizer)
    (composition (pair first.fst.snd first.fst.fst.snd) realEdgesRealizer))
  (reweightTableRealizer sourceRealKeyRealizer)).congr (fun _=>rfl)

def sourceReweightValue (x : SourceReweightInput×Key) : Fraction :=
  lookup (1,1) (sourceReweightRows x.1,x.2)
def sourceReweightValueRealizer : Realizer sourceReweightValue := (composition
  (pair (composition first sourceReweightRowsRealizer) second)
  (lookupRealizer (1,1) (pairEqual (pairEqual natEqual natEqual) natEqual))).congr (fun _=>rfl)

def sourceReweightEntry (x : SourceReweightInput×Key) : ℕ×Fraction :=
  ((sourceTables x.1.1).1.idxOf x.2,sourceReweightValue x)
def sourceReweightEntryRealizer : Realizer sourceReweightEntry := (pair
  (keyLookup second (composition first.fst sourceTablesRealizer).fst)
  sourceReweightValueRealizer).congr (fun _=>rfl)

def sourceReweights (x : SourceReweightInput) : NumericMarking.Reweights :=
  (sourceTables x.1).1.map (fun key=>sourceReweightEntry (x,key))
def sourceReweightsRealizer : Realizer sourceReweights := rowsWith sourceReweightEntryRealizer
  (composition (first (A:=BagBuildInput) (B:=Matrix)) sourceTablesRealizer).fst

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeAdaptiveArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableAdaptive
open TreeTyped TreeFraction ExecutableBottleneck ExecutableScaling ExecutableEstimator ExecutableLadder

def orderedPairRealizer : Realizer orderedPair := (choose less identity (pair second first)).congr (by
  intro x; simp [orderedPair])

def probeValue (x : ProbeTable×(ℕ×ℕ)) : Fraction :=
  if x.2.1=x.2.2 then (0,1) else lookup (0,1) (x.1,orderedPair x.2)
def probeValueRealizer : Realizer probeValue := (choose (composition second natEqual) (constant (0,1))
  (composition (pair first (composition second orderedPairRealizer))
     (lookupRealizer (0,1) (pairEqual natEqual natEqual)))).congr (by intro x; simp [probeValue])

def estimateCell (x : MatrixData×(ℕ×ℕ)) : Fraction :=
  upper (x.1.1.1,(x.1.1.2,probeValue (x.1.2,x.2)))
def estimateCellRealizer : Realizer estimateCell := (composition
  (pair first.fst.fst (pair first.fst.snd (composition (pair first.snd second) probeValueRealizer))) upperRealizer).congr (fun _=>rfl)

def estimateRow (x : (MatrixData×List ℕ)×ℕ) : List Fraction :=
  x.1.2.map (fun j=>estimateCell (x.1.1,(x.2,j)))
def estimateRowRealizer : Realizer estimateRow := (composition
  (pair (pair first.fst second) first.snd)
  (mapWith (composition (pair first.fst (pair first.snd second)) estimateCellRealizer))).congr (fun _=>rfl)

def estimateMatrix (x : MatrixData×List ℕ) : Matrix := x.2.map (fun i=>estimateRow (x,i))
def estimateMatrixRealizer : Realizer estimateMatrix := composition (pair identity second) (mapWith estimateRowRealizer)

def multiplyVector (x : Vector×Vector) : Vector :=
  x.1.map (fun z=>(z.1,mul (z.2,lookup (1,1) (x.2,z.1))))
def multiplyVectorRealizer : Realizer multiplyVector := (composition (pair second first)
  (mapWith (pair second.fst (composition (pair second.snd
    (composition (pair first second.fst) (lookupRealizer (1,1) natEqual))) mulRealizer)))).congr (fun _=>rfl)

def updateVector (x : Matrix×Vector) : Vector := multiplyVector (x.2,scale x.1)
def updateVectorRealizer : Realizer updateVector := (composition
  (pair (second : Realizer (Prod.snd : Matrix×Vector→Vector))
    (composition (first : Realizer (Prod.fst : Matrix×Vector→Matrix)) scaleRealizer)) multiplyVectorRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableAdaptive

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def tableIndex (x : BagBuildInput×Key) : ℕ := (sourceTables x.1).1.idxOf x.2
def tableIndexRealizer : Realizer tableIndex := keyLookup second
  (composition (first (A:=BagBuildInput) (B:=Key)) sourceTablesRealizer).fst

abbrev GeneratedStageData := GeneratedInput×Matrix
def generatedReweightArg : Realizer (fun x : GeneratedStageData=>(x.1.1.1,x.2)) :=
  (pair (first (A:=GeneratedInput) (B:=Matrix)).fst.fst second).congr (fun _=>rfl)

def generatedReweights (x : GeneratedStageData) : Reweights := sourceReweights (x.1.1.1,x.2)
def generatedReweightsRealizer : Realizer generatedReweights :=
  (composition generatedReweightArg sourceReweightsRealizer).congr (fun _=>rfl)

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBindings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder ExecutableLadder NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def centralIndexArg : Realizer (fun x : BagBuildInput×RawLogical=>(x.1,centralKey x)) :=
  (TreeTyped.pair (first (A:=BagBuildInput) (B:=RawLogical)) centralKeyRealizer).congr (fun _=>rfl)
def centralIndex (x : BagBuildInput×RawLogical) : ℕ := tableIndex (x.1,centralKey x)
def centralIndexRealizer : Realizer centralIndex :=
  (composition (f:=fun x : BagBuildInput×RawLogical=>(x.1,centralKey x)) (g:=tableIndex)
    centralIndexArg tableIndexRealizer).congr (by intro x; simp only [Function.comp_apply,centralIndex])
def centralBinding (x : BagBuildInput×RawLogical) : RawLogical×ℕ :=
  (x.2,centralIndex x)
def centralBindingRealizer : Realizer centralBinding :=
  (TreeTyped.pair (second (A:=BagBuildInput) (B:=RawLogical)) centralIndexRealizer).congr (fun _=>rfl)

abbrev GeneratedUpdateConfig := (BagBuildInput×ℕ)×ExecutableScaling.Vector
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev GeneratedUpdateData := GeneratedStageData×Vector
abbrev GeneratedUpdateInput := GeneratedUpdateData×List SampleBits

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def applyFirst {f : A→C} (F : Realizer f) : Realizer (fun x : A×B=>f x.1) :=
  composition first F
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableMarking ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev GeneratedCertificateInput := GeneratedStageData×SampleBits
def certificateSampleArg (x : GeneratedCertificateInput) : GeneratedInput×SampleBits := (x.1.1,x.2)
def certificateSampleArgRealizer : Realizer certificateSampleArg :=
  (TreeTyped.pair (first (A:=GeneratedStageData) (B:=SampleBits)).fst second).congr (fun _=>rfl)
def certificateSample (x : GeneratedCertificateInput) : ExecutableMarking.Marks ℕ := generatedMarked (certificateSampleArg x)
def certificateReweights (x : GeneratedCertificateInput) : Reweights := generatedReweights x.1
def certificateReweightsRealizer : Realizer certificateReweights :=
  applyFirst (B:=SampleBits) generatedReweightsRealizer
def certificateArgs (x : GeneratedCertificateInput) : Reweights×ExecutableMarking.Marks ℕ :=
  (certificateReweights x,certificateSample x)

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStageActivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableAdaptive
open TreeTyped TreeFraction ExecutableBottleneck ExecutableScaling ExecutableLadder ExecutableSource

def coolingRealizer : Realizer cooling := (composition (pair (constant (1,1))
  (composition (pair (constant (1,1)) (composition (pair (constant (1,1))
    (pair identity (constant 1))) divRealizer)) addRealizer)) divRealizer).congr (fun _=>rfl)
def cellDataRealizer : Realizer cellData := (pair
  (pair first.fst.snd (composition (pair (composition (composition first.fst.fst listLength) coolingRealizer)
    first.snd) fuelPowerRealizer)) second).congr (fun _=>rfl)

def rawCell (x : CellData×RawLogical) : Fraction :=
  if orderedPair x.2∈x.1.1.1 then (1,1) else x.1.1.2
def rawCellRealizer : Realizer rawCell := (choose
  (composition (pair (composition second orderedPairRealizer) first.fst.fst)
    (contains (pairEqual natEqual natEqual))) (constant (1,1)) first.fst.snd).congr (by
      intro x; simp [rawCell])

def stageCell (x : CellData×RawLogical) : Fraction :=
  mul (mul (rawCell x,lookup (1,1) (x.1.2,x.2.1)),lookup (1,1) (x.1.2,x.2.2))
def stageCellRealizer : Realizer stageCell := (composition
  (pair (composition (pair rawCellRealizer (composition (pair first.snd second.fst)
      (lookupRealizer (1,1) natEqual))) mulRealizer)
    (composition (pair first.snd second.snd) (lookupRealizer (1,1) natEqual))) mulRealizer).congr (fun _=>rfl)

def stageRow (x : (CellData×List ℕ)×ℕ) : List Fraction :=
  x.1.2.map (fun j=>stageCell (x.1.1,(x.2,j)))
def stageRowRealizer : Realizer stageRow := (composition (pair (pair first.fst second) first.snd)
  (mapWith (composition (pair first.fst (pair first.snd second)) stageCellRealizer))).congr (fun _=>rfl)

def stageMatrix (x : ActivityData) : Matrix :=
  x.1.1.1.map (fun i=>stageRow ((cellData x,x.1.1.1),i))
def stageMatrixRealizer : Realizer stageMatrix := (composition
  (pair (pair cellDataRealizer first.fst.fst) first.fst.fst) (mapWith stageRowRealizer)).congr (fun _=>rfl)

noncomputable def graphRep (G : GraphInput) : GraphData :=
  (List.range G.n,G.edges.toList.map (fun e=>(e.1.val,e.2.val)))
end MatchingFPRAS.ExecutableAdaptive

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS

namespace ExecutableInput
open TreeTyped TreeFunction

def tooSparseRealizer : Realizer tooSparse :=
  (composition (TreeTyped.pair (composition (TreeTyped.pair
    (composition second listLength) (composition second listLength)) add) first) less).congr (by
      intro x
      simp only [Function.comp_apply,tooSparse,two_mul])

open Turing

end ExecutableInput
end MatchingFPRAS

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev SparseStageData := ((GraphData×List Bool)×StageControls)×Vector
abbrev SparseStageInput := SparseStageData×List SampleBits

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev CertificateMatrixInput := GraphData×Vector

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end


