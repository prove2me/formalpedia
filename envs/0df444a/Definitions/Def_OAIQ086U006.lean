-- Prove2me | Definitions.Def_OAIQ086U006
-- name    : OAIQ086U006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:27:09.744853+00:00
-- url     : https://prove2.me/theorems/1eb1fa4f-3230-4d6d-ab3b-ba5777c301a4
-- title:
--   Definitions bundle OAIQ086U006 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1076 declarations of OpenAI's Lean: 424 definitions, 12 inductive types or structures, 5 instances and 635 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Explicit.MachineProductFinish.finishInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.alphabetInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.inPolynomialTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.initializeInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.powerExit`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.powerInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.powersInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.prepareInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.seedBridge`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.seedInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeaders.steps`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeadersRead.afterAlphabet`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeadersRead.afterVertices`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeadersRead.headersInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeadersRead.inputTapes`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeadersRead.rawHeadersInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeadersRead.rawResultTapes`, `OAI.UniqueGamesTheorem.Explicit.MachineProductHeadersRead.resultTapes`, `OAI.UniqueGamesTheorem.Explicit.MachineProductLoop.BaseReady`, `OAI.UniqueGamesTheorem.Explicit.MachineProductLoop.bodyBound`, `OAI.UniqueGamesTheorem.Explicit.MachineProductProgram.resetAt`, `OAI.UniqueGamesTheorem.Explicit.MachineProductRuntime.Input`, `OAI.UniqueGamesTheorem.Explicit.MachineProductRuntime.certify`, `OAI.UniqueGamesTheorem.Explicit.MachineProductRuntime.compose`, `OAI.UniqueGamesTheorem.Explicit.MachineProductRuntime.computation`, `OAI.UniqueGamesTheorem.Explicit.MachineProductRuntime.construct`, `OAI.UniqueGamesTheorem.Explicit.MachineProductRuntime.outputInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductRuntime.prefixInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineProductRuntime.timePolynomial`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge.SingleAddress.addressEdge`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge.SingleAddress.outputInstance`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge.SingleAddress.tableOutput`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge.computableInPolyTime`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge.doubledComputableInPolyTime`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge.output`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitFinish.completePrefix`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitFinish.finishStartInTime`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitFinish.timePolynomial`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitProgram.machine`, `OAI.UniqueGamesTheorem.Explicit.MachineSingleOrbitProgram.program` and 396 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Foundations_ValueLemmas`, `UniqueGames_Games_ProductLemmas`, `UniqueGames_Games_ProductMachineSemantics`, `UniqueGames_Games_SubdivisionEncoding`, `UniqueGames_Games_SubdivisionTarget`, `UniqueGames_Games_UniformTarget`, `UniqueGames_Machines_GraphCounterStartLemmas`, `UniqueGames_Machines_MachineProductFieldLemmas`, `UniqueGames_Machines_MachineProductHeadersFrameLemmas`, `UniqueGames_Machines_MachineProductProgram`, `UniqueGames_Machines_MachineProductRuntime`, `UniqueGames_Machines_MachineProductSeed`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineSingleOrbitBridgeLemmas`, `UniqueGames_Machines_MachineSingleOrbitFinishLemmas`, `UniqueGames_Machines_MachineSingleOrbitProgramLemmas`, `UniqueGames_Machines_MachineSubdivisionBody`, `UniqueGames_Machines_MachineSubdivisionBodySpecLemmas`, `UniqueGames_Machines_MachineSubdivisionDynamicRowsLemmas`, `UniqueGames_Machines_MachineSubdivisionTableRead`, `UniqueGames_Machines_MachineTupleOdometer`, `UniqueGames_Machines_MachineUniformRun`, `UniqueGames_PCP_SourceContextClear`, `UniqueGames_PCP_SourceFieldArrayLemmas`, `UniqueGames_PCP_SourceHeaderCounts`, `UniqueGames_PCP_SourceHonestLemmas`, `UniqueGames_PCP_SourceLoopInitLemmas`, `UniqueGames_PCP_SourceOccurrences`, `UniqueGames_PCP_SourceQueryLoopLemmas`, `UniqueGames_PCP_SourceQueryOrderLemmas`, `UniqueGames_PCP_SourceSignaturePrepareLemmas`, `UniqueGames_Reduction_AddressMachineInitial`, `UniqueGames_Reduction_AddressMachineLoopLemmas`, `UniqueGames_Reduction_AddressMachineSpace`, `UniqueGames_Reduction_AddressOdometerSchedule`, `UniqueGames_Reduction_AddressOutcomeSpecs`, `UniqueGames_Reduction_AddressOutputSize`, `UniqueGames_Reduction_AddressTupleBody`, `UniqueGames_Reduction_AddressTupleBudget`, `UniqueGames_Reduction_AddressTupleCleanupLemmas`, `UniqueGames_Reduction_AddressTuplePolynomialLemmas`, `UniqueGames_Reduction_CanonicalBodyTemplateLemmas`, `UniqueGames_Reduction_CloneMachineModelLemmas`, `UniqueGames_Reduction_EncodingLemmas`, `UniqueGames_Reduction_FixedOutcomes`, `UniqueGames_Reduction_MachineAddressEdgeLemmas`, `UniqueGames_Reduction_MachineAddressHeaders`, `UniqueGames_Reduction_MachineFieldTemplate`, `UniqueGames_Reduction_MachineTemplateAddress`, `UniqueGames_Reduction_OutputTranslationsLemmas`, `UniqueGames_Reduction_SourceEquationLookupLemmas`, `UniqueGames_Repetition_CollisionLemmas`, `UniqueGames_Repetition_RoundingKernel`, `UniqueGames_Repetition_RoundingSampling`, `UniqueGames_Repetition_RoundingThresholdLemmas`, `UniqueGames_Repetition_TensorAlgebraLemmas`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`; the bundles `OAIQ086U003` and `OAIQ086U004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ086U010` and `OAIQ086U011`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U003
import Definitions.Def_OAIQ086U004

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem value_le_one (G : Game Q₁ Q₂ A₁ A₂) : G.value ≤ 1 :=
  (G.value_le_iff 1).2 G.success_le_one

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_GraphCounterStartLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOdometerInit
open Turing

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

variable (tape : Tape k → K) (distinct : Function.Injective tape)
  (labels : Label k → Λ) (exit : Option Λ)
  (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
  (atProgram : ∀l, program (labels l) = statement tape labels exit l)

def digitInTime (j : Fin k) (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : base (tape (.current j)) = [])
    (hremaining : base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.seed j)),(ambient,none),base⟩
      (some ⟨some (labelAt labels (j.val+1)),(ambient,none),digitOutput tape j m base⟩)
      (2*m+6) := by
  have hrc : tape .radix ≠ tape (.current j) := distinct.ne (by simp)
  have hrr : tape .radix ≠ tape (.remaining j) := distinct.ne (by simp)
  have hrs : tape .radix ≠ tape .scratch := distinct.ne (by simp)
  have hsc : tape .scratch ≠ tape (.current j) := distinct.ne (by simp)
  have hrsc : tape (.remaining j) ≠ tape .scratch := distinct.ne (by simp)
  have hrcc : tape (.remaining j) ≠ tape (.current j) := distinct.ne (by simp)
  let seeded := Function.update base (tape (.current j)) (encodeWord 0)
  have seedRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.seed j)),(ambient,none),base⟩
      (some ⟨some (labels (.copyOut j)),(ambient,none),seeded⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labels (.seed j))) (ambient,none) base) = _
    rw [atProgram]
    simp [statement,TM2.stepAux,seeded,hcurrent,encodeWord]
  have copiedRun := MachineCopy.copyInTime (tape .radix) (tape (.remaining j)) (tape .scratch)
    hrr hrs hrsc false (labels (.copyOut j)) (labels (.copyBack j))
    (some (labels (.trim j))) program (atProgram (.copyOut j)) (atProgram (.copyBack j))
    seeded (by simpa [seeded,hsc] using hscratch) ambient none
  let copied := Function.update seeded (tape (.remaining j)) (encodeWord m)
  have he : Function.update seeded (tape (.remaining j))
      (seeded (tape .radix) ++ seeded (tape (.remaining j))) = copied := by
    simp [copied,seeded,hradix,hremaining,hrc,hrcc]
  rw [he] at copiedRun
  have trimRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.trim j)),(ambient,none),copied⟩
      (some ⟨some (labelAt labels (j.val+1)),(ambient,none),digitOutput tape j m base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labels (.trim j))) (ambient,none) copied) = _
    have hm' : m = (m-1)+1 := by omega
    have tail : (encodeWord m).tail = encodeWord (m-1) := by
      conv_lhs => rw [hm']
      simp [encodeWord,List.replicate_succ]
    rw [atProgram]
    simp [statement,TM2.stepAux,copied,seeded,digitOutput,tail]
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seedRun copiedRun) trimRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hs : seeded (tape .radix) = encodeWord m := by simpa [seeded,hrc] using hradix
  rw [hs,encodeWord_length]
  omega

/-- Place the actual finite initialization prefix inside an ambient program. -/
def prefixInTime (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : ∀j, base (tape (.current j)) = [])
    (hremaining : ∀j, base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) (r : Nat) (hr : r ≤ k) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels 0),(ambient,none),base⟩
      (some ⟨some (labelAt labels r),(ambient,none),stageTapes tape m base r⟩)
      (r*(2*m+6)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hrk : r < k := by omega
    let j : Fin k := ⟨r,hrk⟩
    let before := stageTapes tape m base r
    have one := digitInTime tape distinct labels exit program atProgram j m hm before
      (by dsimp only [before]; rw [stageTapes_frame tape _ _ _ _
          (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))]; exact hradix)
      (by simp [before,stageTapes_current tape distinct,j,hcurrent])
      (by simp [before,stageTapes_remaining tape distinct,j,hremaining])
      (by dsimp only [before]; rw [stageTapes_frame tape _ _ _ _
          (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))]; exact hscratch)
      ambient
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt labels r),(ambient,none),before⟩
        (some ⟨some (labelAt labels (r+1)),(ambient,none),stageTapes tape m base (r+1)⟩)
        (2*m+6) := by
      simpa only [labelAt,dite_eq_left hrk,j,stageTapes,before] using one
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using joined

/-- Complete actual initialization, including width zero and the optional
continuation. The radix, scratch, ambient state and unrelated tapes survive. -/
def initializeInTime (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : ∀j, base (tape (.current j)) = [])
    (hremaining : ∀j, base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels 0),(ambient,none),base⟩
      (some ⟨exit,(ambient,none),stageTapes tape m base k⟩)
      (k*(2*m+6)+1) := by
  have initializedPrefix := prefixInTime tape distinct labels exit program atProgram m hm base
    hradix hcurrent hremaining hscratch ambient k (le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels k),(ambient,none),stageTapes tape m base k⟩
      (some ⟨exit,(ambient,none),stageTapes tape m base k⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labelAt labels k)) (ambient,none) _) = _
    simp only [labelAt,Nat.lt_irrefl,↓reduceDIte]
    rw [atProgram]
    cases exit <;> rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ initializedPrefix doneRun

end UniqueGamesTheorem.Foundations.Complexity.MachineOdometerInit

/-!
A concrete sequential composition of two finite TM2 programs. The first output
is transferred to a temporary stack and then to the second input. Both loops
execute actual transitions and reset their shared register on exit. Static
renaming changes neither a stack word nor the number of executed transitions.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.sourceIndexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
The independent graph product in the last step of the reduction.

Edges are tuples of actual base edges.  The endpoint maps remain injective,
the edge law is exactly uniform, and the associated game agrees with ordinary
parallel repetition for every pair of local strategies, including strategies
depending on their whole question tuples.  Only the completeness lower bound
uses coordinatewise strategies; no repetition soundness bound is assumed here.
-/

/-!
The actual ordered full-table instance of the final independent product.
Caller-supplied coordinate numberings are used explicitly. Edges are emitted in
increasing mixed-radix address, with division/remainder decoding; the two vertex
blocks and the entire permutation table use the same coordinate convention.
-/

/-!
Machine-friendly product numbering on the common global vertex base.
Both endpoints use the same radix, so the machine needs neither a right-side
subtraction nor a final offset. Mixed-side tuples are isolated vertices. For a
positive repetition count the first coordinate supplies a total bipartition.
-/

namespace UniqueGamesTheorem.Explicit.ProductPaddedOutput

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

namespace Embedded

variable {L R E : Type*} {q N M : ℕ}

theorem render_get (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (i : Fin (render G vertices edges hM).constraints.length) :
    (render G vertices edges hM).constraints[i] =
      row G vertices edges ⟨i.val, by simpa using i.isLt⟩ := by
  change (List.ofFn (row G vertices edges))[i.val]'(by simpa using i.isLt) = _
  exact List.getElem_ofFn (by simpa using i.isLt)

def simpleBipartite (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (side : Fin N → Bool)
    (leftSide : ∀ x, side (vertices (Sum.inl x)) = false)
    (rightSide : ∀ y, side (vertices (Sum.inr y)) = true) :
    SimpleBipartite (render G vertices edges hM) where
  side := side
  sourceSide i := by simp only [render_get, row, leftSide]
  targetSide i := by simp only [render_get, row, rightSide]
  endpoints_injective := by
    intro i j hij
    have hi : i.val < M := by simpa using i.isLt
    have hj : j.val < M := by simpa using j.isLt
    have hrows :
        ((row G vertices edges ⟨i.val, hi⟩).source,
          (row G vertices edges ⟨i.val, hi⟩).target) =
        ((row G vertices edges ⟨j.val, hj⟩).source,
          (row G vertices edges ⟨j.val, hj⟩).target) := by
      simpa only [render_get] using! hij
    have he : edges ⟨i.val, hi⟩ = edges ⟨j.val, hj⟩ := by
      apply G.simple
      apply Prod.ext
      · exact Sum.inl.inj (vertices.injective (congrArg Prod.fst hrows))
      · exact Sum.inr.inj (vertices.injective (congrArg Prod.snd hrows))
    exact Fin.ext (congrArg (fun k : Fin M => k.val) (edges.injective he))

variable [Fintype L] [Fintype R] [Fintype E]

omit [Fintype L] [Fintype R] in
theorem count (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (labeling : Fin N → Fin q) :
    countSatisfied labeling (render G vertices edges hM).constraints =
      G.satisfiedCount (fun x => labeling (vertices (Sum.inl x)))
        (fun y => labeling (vertices (Sum.inr y))) := by
  classical
  change countSatisfied labeling (List.ofFn (row G vertices edges)) = _
  rw [Integration.GapSemantics.countSatisfied_ofFn]
  unfold BipartiteGame.satisfiedCount
  apply Fintype.sum_equiv edges
  intro i
  simp [row, Constraint.satisfied, fullTable]

omit [Fintype L] [Fintype R] in
@[simp] theorem extendLabelings_left [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) (x : L) :
    extendLabelings vertices left right (vertices (Sum.inl x)) = left x := by
  exact vertices.injective.extend_apply _ _ _

omit [Fintype L] [Fintype R] in
@[simp] theorem extendLabelings_right [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) (y : R) :
    extendLabelings vertices left right (vertices (Sum.inr y)) = right y := by
  exact vertices.injective.extend_apply _ _ _

theorem maxSatisfied [Nonempty (Fin q)] (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    Integration.InstanceValue.maxSatisfied (render G vertices edges hM) = G.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    erw [count]
    exact G.satisfiedCount_le_maxSatisfied _ _
  · obtain ⟨left, right, hmax⟩ := G.maxSatisfied_attained
    have hcount := count G vertices edges hM (extendLabelings vertices left right)
    simp only [extendLabelings_left, extendLabelings_right, hmax] at hcount
    rw [← hcount]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied
      (render G vertices edges hM) (extendLabelings vertices left right)

theorem value [Nonempty (Fin q)] (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    Integration.InstanceValue.value (render G vertices edges hM) = G.value := by
  unfold Integration.InstanceValue.value BipartiteGame.value
  rw [maxSatisfied, render_length]
  have hc : M = Fintype.card E := by simpa using Fintype.card_congr edges
  rw [hc]

end Embedded

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

local instance instNonemptyFinLengthConstraintVerticesConstraints : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩

def side (t : ℕ) (ht : 0 < t) (v : Fin (H.vertices ^ t)) : Bool :=
  presentation.side (finFunctionFinEquiv.symm v ⟨0, ht⟩)

theorem outputRow_images (t : ℕ) (ht : 0 < t)
    (i : Fin (H.constraints.length ^ t)) (a : Fin (q ^ t)) :
    (outputRow H presentation t ht i).permutation.images[a] =
      finFunctionFinEquiv (fun j =>
        H.constraints[finFunctionFinEquiv.symm i j].permutation.images[
          finFunctionFinEquiv.symm a j]) := by
  simp [outputRow, Embedded.row, graph, BipartiteGame.relabel, BipartiteGame.product,
    SimpleBipartite.toBipartiteGame, permutationEquiv, fullTable]

theorem output_gameWords (t : ℕ) (ht : 0 < t) :
    Complexity.gameWords (output H presentation t ht) =
      [H.vertices ^ t, q ^ t, H.constraints.length ^ t] ++
        (List.ofFn (outputRow H presentation t ht)).flatMap Complexity.constraintWords := by
  simp only [Complexity.gameWords, output_vertices, output_constraints, List.length_ofFn]

section

theorem output_value_eq_repetition [Nonempty (Fin q)] (t : ℕ) (ht : 0 < t) :
    Integration.InstanceValue.value (output H presentation t ht) =
      (presentation.toBipartiteGame.toGame.repetition t).value := by
  classical
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  let : Nonempty (Fin (q ^ t)) :=
    ⟨finFunctionFinEquiv (fun _ : Fin t => Classical.choice inferInstance)⟩
  rw [output, Embedded.value, ← BipartiteGame.toGame_value, graph,
    BipartiteGame.relabel_value, BipartiteGame.product_value_eq_repetition]

theorem output_completeness [Nonempty (Fin q)] (t : ℕ) (ht : 0 < t) {error : ℝ}
    (hcomplete : 1 - error ≤ Integration.InstanceValue.value H) :
    1 - (t : ℝ) * error ≤ Integration.InstanceValue.value (output H presentation t ht) := by
  classical
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition, ← BipartiteGame.product_value_eq_repetition]
  exact presentation.toBipartiteGame.product_completeness t
    (by simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hcomplete)

end

def finalCoordinates {ell : ℕ} (coordinates : Fin q ≃ (Fin ell → ZMod 2)) (t : ℕ) :
    Fin (q ^ t) ≃ (Fin (ell * t) → ZMod 2) :=
  finFunctionFinEquiv.symm.trans
    ((Equiv.piCongrRight (fun _ : Fin t => coordinates)).trans
      (BipartiteGame.binaryProductEquiv ell t).toEquiv)

theorem finalCoordinates_apply {ell : ℕ}
    (coordinates : Fin q ≃ (Fin ell → ZMod 2)) (t : ℕ) (a : Fin (q ^ t)) :
    finalCoordinates coordinates t a = BipartiteGame.binaryProductEquiv ell t
      (fun i => coordinates (finFunctionFinEquiv.symm a i)) := rfl

end UniqueGamesTheorem.Explicit.ProductPaddedOutput

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductFieldLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

/-! Actual power-header emission by fixed-width Horner evaluation of
`[1,0,...,0]`, followed by physical transfer to the reverse accumulator. -/

namespace UniqueGamesTheorem.Explicit.MachineProductPower

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {exponent : Nat}

/-- Header powers are computed from a unary input radix, not stored in an
unbounded register. Only the output accumulator changes at the boundary. -/
theorem powerTrace (slots : MachineHorner.Layout (exponent + 1) ↪ K) (output : K)
    (outside : ∀ i, output ≠ slots i) (labels : Label exponent → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots output labels exit l)
    (base : K → List Bool) (radix : Nat)
    (radixWord : base (slots (.inl 0)) = encodeWord radix)
    (digitWords : ∀ i : Fin (exponent + 1), base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : MachineHorner.Clean slots base) (fieldEmpty : base (slots (.inl 3)) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps radix exponent]
      (some ⟨some (labels (.inl .start)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update base output ((encodeWord (radix ^ exponent)).reverse ++ base output)⟩ := by
  have horner := MachineHorner.hornerTrace slots (fun x => labels (.inl x))
    (some (labels (.inr ()))) program (fun x => atLabels (.inl x)) base radix digits
    radixWord digitWords clean ambient register
  rw [value_eq] at horner
  let after := MachineHorner.resultTapes slots base (radix ^ exponent)
  have hout : after (slots (.inl 3)) = encodeWord (radix ^ exponent) := by
    dsimp only [after]
    rw [MachineHorner.resultTapes_output, fieldEmpty, List.append_nil]
  have hacc : after output = base output :=
    MachineHorner.resultTapes_other slots base (radix ^ exponent) output (outside _)
  have emit := transferAt_fromTapes (Γ := fun _ : K => Bool)
    (slots (.inl 3)) output (Ne.symm (outside _)) id false (labels (.inr ())) exit
    program (atLabels (.inr ())) after (ambient, ()) none
  rw [hout, hacc, List.map_id, encodeWord_length] at emit
  have tapes_eq : tapesAt (slots (.inl 3)) output after []
      ((encodeWord (radix ^ exponent)).reverse ++ base output) =
      Function.update base output ((encodeWord (radix ^ exponent)).reverse ++ base output) := by
    funext k
    by_cases h1 : k = output
    · subst k; simp [tapesAt]
    · by_cases h2 : k = slots (.inl 3)
      · subst k; simp [tapesAt, h1, fieldEmpty]
      · simp [tapesAt, after, MachineHorner.resultTapes, h1, h2]
  rw [tapes_eq] at emit
  rw [show steps radix exponent = (radix ^ exponent + 2) +
    MachineHorner.steps radix digits (exponent + 1) by unfold steps; omega,
    Function.iterate_add_apply, horner]
  exact emit

end UniqueGamesTheorem.Explicit.MachineProductPower

/-! A finite row-field schedule. Endpoint fields use the input vertex radix;
permutation fields use the fixed alphabet radix. The complete list of columns
is in finite control, while all row indices, table entries and radix magnitudes
remain data on tapes. -/

namespace UniqueGamesTheorem.Explicit.MachineProductRow

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

theorem resultOf_eq (slots : Layout width ↪ K) (values : Command width → Nat)
    (commands : List (Command width)) (base : K → List Bool) :
    MachineFiniteSequence.resultOf (result slots values) commands base =
      Function.update base (outputTape slots)
        ((rowBits values commands).reverse ++ base (outputTape slots)) := by
  induction commands generalizing base with
  | nil => simp [MachineFiniteSequence.resultOf, rowBits]
  | cons command commands ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    simp [result, appendField, rowBits, List.reverse_append, List.append_assoc]

/-- Complete row trace from the concrete field implementation. The only
premises concerning values are literal indexed-table identities and the
Horner interpretation of those values. -/
theorem rowTrace (slots : Layout width ↪ K) (table : List Nat) (coefficient : Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat) (commands : List (Command width))
    (fields : Command width → Fin width → Nat) (digits : Command width → Nat → Nat)
    (selected : ∀ command ∈ commands, ∀ i,
      table[coefficient * indices i + command.2 i]? = some (fields command i))
    (reversed : ∀ command ∈ commands, ∀ i : Fin width,
      digits command i.val = fields command i.rev)
    (labels : Label slots commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots coefficient commands labels exit l)
    (base : K → List Bool) (ready : Ready slots table indices radices base) (ambient : σ) :
    let values := fun c : Command width => MachineHorner.value (radices c.1) (digits c) width
    let cost := fun (c : Command width) (tapes : K → List Bool) =>
      MachineProductField.steps (fieldSlots slots c.1) table coefficient indices c.2 (fields c)
        tapes (radices c.1) (digits c)
    (advance (TM2.step program))^[MachineFiniteSequence.steps (result slots values) cost commands base]
      (some ⟨entry slots commands labels exit, ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update base (outputTape slots)
          ((rowBits values commands).reverse ++ base (outputTape slots))⟩ := by
  dsimp only
  let values := fun c : Command width => MachineHorner.value (radices c.1) (digits c) width
  let cost := fun (c : Command width) (tapes : K → List Bool) =>
    MachineProductField.steps (fieldSlots slots c.1) table coefficient indices c.2 (fields c)
      tapes (radices c.1) (digits c)
  have run := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction slots coefficient) (result slots values) cost program
    (Ready slots table indices radices) (fun _ => ((ambient, ()), none)) id commands
    (by intro c hc tapes ht; exact ht.appendField slots table indices radices tapes (values c))
    (by
      intro c hc fieldLabels fieldExit atField tapes ht
      have h := MachineProductField.fieldTrace (fieldSlots slots c.1) table coefficient
        indices c.2 (fields c) (selected c hc) fieldLabels fieldExit program atField tapes
        (fun _ => []) (ht.work c.1) ht.tableWord
        (fun i => by simpa [fieldSlots, fieldRole] using ht.sourceWords i) (radices c.1) (digits c)
        (ht.radixWords c.1) (reversed c hc) ambient none
      rw [MachineProductField.finalTapes_eq _ _ _ _ _ _ _ (ht.work c.1)] at h
      exact h)
    labels exit atLabels base ready
  rw [resultOf_eq] at run
  exact run

end UniqueGamesTheorem.Explicit.MachineProductRow

/-! Polynomial bounds for actual field and row traces. The output accumulator
is excluded from local cleanup and is never rescanned by row emission. -/

/-! Fixed natural polynomials are represented by literal Horner coefficients.
The coefficient representation is independent of the machine input. The actual
machine wrapper is built from the shared physical unary Horner subroutine. -/

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PolynomialMachine

noncomputable section

abbrev Layout (p : Polynomial Nat) := MachineHorner.Layout (width p)

def fieldWord (p : Polynomial Nat) : Layout p → List Bool
  | .inl _ => []
  | .inr i => encodeWord (digit p i.val)

def fieldIndices (p : Polynomial Nat) : List (Layout p) :=
  (List.finRange (width p)).map Sum.inr

theorem fieldIndices_nodup (p : Polynomial Nat) : (fieldIndices p).Nodup :=
  (List.nodup_finRange _).map Sum.inr_injective

@[simp] theorem inl_not_mem_fields (p : Polynomial Nat) (i : Fin 6) :
    Sum.inl i ∉ fieldIndices p := by simp [fieldIndices]

@[simp] theorem inr_mem_fields (p : Polynomial Nat) (i : Fin (width p)) :
    Sum.inr i ∈ fieldIndices p := by simp [fieldIndices]

def timePolynomial (p : Polynomial Nat) : Polynomial Nat :=
  prefixCostPolynomial (digit p) (width p) +
    Polynomial.C 2 * prefixValuePolynomial (digit p) (width p) + Polynomial.X + Polynomial.C 8

theorem timePolynomial_eval (p : Polynomial Nat) (n : Nat) :
    (timePolynomial p).eval n = MachineHorner.steps n (digit p) (width p) + n + 3 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval,
    prefixCostPolynomial_eval, MachineHorner.steps]
  omega

theorem hornerValue_eq_eval (p : Polynomial Nat) (n : Nat) :
    MachineHorner.value n (digit p) (width p) = p.eval n := by
  rw [MachineHorner.value_eq_foldl, range_map_digit]
  have hh := highCoefficients_foldl p n
  simpa only [Nat.mul_comm] using hh

end

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PolynomialMachine

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductMachineSemantics
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The exact table lookups and field schedule consumed by the product machine.
The table contains rows only: the three input header words have already been
consumed, so each affine lookup has coefficient `q+2` and no header offset.
-/

namespace UniqueGamesTheorem.Explicit.ProductMachineSemantics

open UniqueGamesTheorem.Foundations
open Target
open Complexity
open MachineOutputContract

variable {n q t : ℕ}

theorem inputTable_source (H : Instance q) (e : Fin H.constraints.length) :
    (inputTable H)[(q + 2) * e.val]? = some H.constraints[e].source.val := by
  have h := row_table_lookup H.constraints e (⟨0, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords] using h

theorem inputTable_target (H : Instance q) (e : Fin H.constraints.length) :
    (inputTable H)[(q + 2) * e.val + 1]? = some H.constraints[e].target.val := by
  have h := row_table_lookup H.constraints e (⟨1, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords] using h

theorem inputTable_image (H : Instance q) (e : Fin H.constraints.length) (a : Fin q) :
    (inputTable H)[(q + 2) * e.val + (2 + a.val)]? =
      some (H.constraints[e].permutation.images[a]).val := by
  have h := row_table_lookup H.constraints e (⟨2 + a.val, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords, tableWords, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

theorem source_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fields H edges (sourceCommand t) = fun j => H.constraints[edges j].source.val := by
  funext j
  simp [fields, sourceCommand, inputTable_source]

theorem target_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fields H edges (targetCommand t) = fun j => H.constraints[edges j].target.val := by
  funext j
  simp [fields, targetCommand, inputTable_target]

theorem image_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (a : Fin (q ^ t)) :
    fields H edges (imageCommand q t a) = fun j =>
      (H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j]).val := by
  funext j
  unfold fields imageCommand
  rw [inputTable_image H (edges j) (finFunctionFinEquiv.symm a j)]
  rfl

/-- Every scheduled lookup selects an actual word in the input table. -/
theorem selected (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (c : MachineProductRow.Command t) (hc : c ∈ commands q t) (i : Fin t) :
    (inputTable H)[(q + 2) * (edges i).val + c.2 i]? =
      some (fields H edges c i) := by
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [fields, sourceCommand, inputTable_source]
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [fields, targetCommand, inputTable_target]
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  rw [image_fields]
  exact inputTable_image H (edges i) (finFunctionFinEquiv.symm a i)

theorem fields_lt (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (c : MachineProductRow.Command t) (hc : c ∈ commands q t) (i : Fin t) :
    fields H edges c i < if c.1 then q else H.vertices := by
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [source_fields]
    exact H.constraints[edges i].source.isLt
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [target_fields]
    exact H.constraints[edges i].target.isLt
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  rw [image_fields]
  exact (H.constraints[edges i].permutation.images[finFunctionFinEquiv.symm a i]).isLt

theorem source_value (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fieldValue H edges (sourceCommand t) =
      (finFunctionFinEquiv (fun j => H.constraints[edges j].source) : ℕ) := by
  unfold fieldValue
  rw [source_fields]
  exact horner_ofFin (fun j => H.constraints[edges j].source)

theorem target_value (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fieldValue H edges (targetCommand t) =
      (finFunctionFinEquiv (fun j => H.constraints[edges j].target) : ℕ) := by
  unfold fieldValue
  rw [target_fields]
  exact horner_ofFin (fun j => H.constraints[edges j].target)

theorem image_value (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (a : Fin (q ^ t)) :
    fieldValue H edges (imageCommand q t a) =
      (finFunctionFinEquiv (fun j =>
        H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j]) : ℕ) := by
  unfold fieldValue
  rw [image_fields]
  exact horner_ofFin (fun j =>
    H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j])

theorem encodeWords_map {X : Type*} (xs : List X) (f : X → ℕ) :
    encodeWords (xs.map f) = xs.flatMap (fun x => encodeWord (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih]

/-- The controller's literal field-command output is the serialized semantic
row, including every forward permutation-table entry. -/
theorem rowBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) (i : Fin (H.constraints.length ^ t)) :
    MachineProductRow.rowBits (fieldValue H (finFunctionFinEquiv.symm i)) (commands q t) =
      encodeWords (constraintWords (ProductPaddedOutput.outputRow H presentation t ht i)) := by
  have hsource : fieldValue H (finFunctionFinEquiv.symm i) (sourceCommand t) =
      (ProductPaddedOutput.outputRow H presentation t ht i).source.val := source_value _ _
  have htarget : fieldValue H (finFunctionFinEquiv.symm i) (targetCommand t) =
      (ProductPaddedOutput.outputRow H presentation t ht i).target.val := target_value _ _
  have himage (a : Fin (q ^ t)) :
      fieldValue H (finFunctionFinEquiv.symm i) (imageCommand q t a) =
      ((ProductPaddedOutput.outputRow H presentation t ht i).permutation.images[a]).val := by
    rw [ProductPaddedOutput.outputRow_images]
    exact image_value _ _ _
  simp only [MachineProductRow.rowBits, commands, List.flatMap_cons, List.flatMap_map,
    hsource, htarget, himage, constraintWords, encodeWords_append, encodeWords,
    List.append_nil, List.append_assoc]
  congr 2
  have htable : tableWords (ProductPaddedOutput.outputRow H presentation t ht i).permutation =
      (List.finRange (q ^ t)).map
        (fun a => ((ProductPaddedOutput.outputRow H presentation t ht i).permutation.images[a]).val) := by
    apply List.ext_getElem
    · simp [tableWords]
    · intro j hj hk
      simp [tableWords, Fin.getElem_fin]
  rw [htable, encodeWords_map]

theorem allRowsBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    allRowsBits H t = encodeWords
      ((ProductPaddedOutput.output H presentation t ht).constraints.flatMap constraintWords) := by
  unfold allRowsBits
  simp_rw [rowBits_eq H presentation t ht]
  rw [ProductPaddedOutput.output_constraints]
  have hrows : List.ofFn (ProductPaddedOutput.outputRow H presentation t ht) =
      (List.finRange (H.constraints.length ^ t)).map
        (ProductPaddedOutput.outputRow H presentation t ht) := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  rw [hrows]
  erw [List.flatMap_map, encodeWords_flatMap]
  rfl

/-- Concatenating the three computed headers and all physical row fields yields
precisely the target serialization, including list order and full tables. -/
theorem gameBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    encodeWords [H.vertices ^ t, q ^ t, H.constraints.length ^ t] ++ allRowsBits H t =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  rw [gameBits, ProductPaddedOutput.output_gameWords, encodeWords_append,
    allRowsBits_eq H presentation t ht, ProductPaddedOutput.output_constraints]
  rfl

end UniqueGamesTheorem.Explicit.ProductMachineSemantics

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineFieldTemplate
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.MachineFieldTemplate

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q : Nat} {K Λ σ : Type}

/-- Local finite labels are placed in an arbitrary caller label space, with an
explicit continuation. Every instruction is determined by the fixed template. -/
def instruction (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (place : Label tokens.length → Λ) (exit : Option Λ) :
    Label tokens.length → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .entry i => match tokens.get i with
      | .literal bits => .load reset
          (pushWord output bits (.goto fun _ => place (startAt tokens.length (i.val + 1))))
      | .copy _ => .load reset (.goto fun _ => place (.scan i))
  | .scan i => match tokens.get i with
      | .literal _ => .halt
      | .copy j => MachineTransducerCopy.scanLoop (field j) scratch ()
          (fun _ b => place (.emit i b)) (place (.restore i))
  | .emit i b => MachineTransducerCopy.emitter output (fun _ _ => ()) identityEmit
      (place (.scan i)) () b
  | .restore i => match tokens.get i with
      | .literal _ => .halt
      | .copy j => MachineTransfer.loopAt scratch (field j) id false
          (place (.restore i)) (some (place (startAt tokens.length (i.val + 1))))
  | .done => .load reset (jump exit)

variable [DecidableEq K]

section Execution

variable (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
variable (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
variable (scratchOutput : scratch ≠ output)
variable (place : Label tokens.length → Λ) (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ label,
  P (place label) = instruction tokens field scratch output place exit label)

include atInstruction

theorem doneStep (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place .done), state, base⟩ =
      some ⟨exit, reset state, base⟩ := by
  change some (TM2.stepAux (P (place .done)) state base) = _
  rw [atInstruction .done]
  cases exit <;> rfl

theorem literalStep (i : Fin tokens.length) (bits : List Bool)
    (token : tokens.get i = .literal bits) (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (.entry i)), state, base⟩ =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output bits⟩ := by
  change some (TM2.stepAux (P (place (.entry i))) state base) = _
  rw [atInstruction (.entry i)]
  simp only [instruction, token, TM2.stepAux]
  rw [stepAux_pushWord]
  rfl

theorem copySetupStep (i : Fin tokens.length) (j : Fin q)
    (token : tokens.get i = .copy j) (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (.entry i)), state, base⟩ =
      some ⟨some (place (.scan i)), reset state, base⟩ := by
  change some (TM2.stepAux (P (place (.entry i))) state base) = _
  rw [atInstruction (.entry i)]
  simp only [instruction, token, TM2.stepAux]

include fieldScratch fieldOutput scratchOutput

theorem copyTrace (i : Fin tokens.length) (j : Fin q)
    (token : tokens.get i = .copy j) (base : K → List Bool)
    (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[3 * (base (field j)).length + 3]
      (some ⟨some (place (.entry i)), state, base⟩) =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output (base (field j))⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (field j) scratch output (fieldScratch j) (fieldOutput j) scratchOutput
    () (fun _ _ => ()) identityEmit (place (.scan i)) (place (.restore i))
    (fun _ b => place (.emit i b)) (some (place (startAt tokens.length (i.val + 1)))) P
    (by rw [atInstruction (.scan i)]; simp only [instruction, token])
    (by intro control b; cases control; exact atInstruction (.emit i b))
    (by rw [atInstruction (.restore i)]; simp only [instruction, token])
    base scratchEmpty state.1.1 () none
  rw [show 3 * (base (field j)).length + 3 =
      (3 * (base (field j)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[3 * (base (field j)).length + 2]
    (TM2.step P ⟨some (place (.entry i)), state, base⟩) = _
  rw [copySetupStep tokens field scratch output place exit P atInstruction i j token]
  simpa only [identity_output, reset, outputTapes] using copied

theorem tokenTrace (i : Fin tokens.length) (base : K → List Bool)
    (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[
      tokenSteps (fun j => base (field j)) (tokens.get i)]
      (some ⟨some (place (.entry i)), state, base⟩) =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output (tokenOutput (fun j => base (field j)) (tokens.get i))⟩ := by
  cases token : tokens.get i with
  | literal bits =>
      simpa only [token, tokenSteps, tokenOutput, Function.iterate_one,
        MachineComposition.advance_some] using
        literalStep tokens field scratch output place exit P atInstruction i bits token base state
  | copy j =>
      simpa only [token, tokenSteps, tokenOutput] using
        copyTrace tokens field scratch output fieldScratch fieldOutput scratchOutput place exit P
          atInstruction i j token base scratchEmpty state

theorem suffixTrace (remaining : Nat) :
    ∀ (i : Nat), i + remaining = tokens.length →
      ∀ (base : K → List Bool) (_scratchEmpty : base scratch = []) (state : State σ),
        (MachineComposition.advance (TM2.step P))^[
          workSteps (tokens.drop i) (fun j => base (field j)) + 1]
          (some ⟨some (place (startAt tokens.length i)), state, base⟩) =
          some ⟨exit, reset state, outputTapes base output
            (templateOutput (tokens.drop i) (fun j => base (field j)))⟩ := by
  induction remaining with
  | zero =>
      intro i hi base _scratchEmpty state
      have heq : i = tokens.length := by omega
      subst i
      simpa [startAt, workSteps, templateOutput, MachineComposition.advance_some] using
        doneStep tokens field scratch output place exit P atInstruction base state
  | succ remaining ih =>
      intro i hi base scratchEmpty state
      have hiLt : i < tokens.length := by omega
      let index : Fin tokens.length := ⟨i, hiLt⟩
      let bits := tokenOutput (fun j => base (field j)) (tokens.get index)
      let after := outputTapes base output bits
      have first := tokenTrace tokens field scratch output fieldScratch fieldOutput scratchOutput
        place exit P atInstruction index base scratchEmpty state
      have second := ih (i + 1) (by omega) after
        (by simpa [after, outputTapes, scratchOutput] using scratchEmpty) (reset state)
      have fieldsAfter : (fun j => after (field j)) = (fun j => base (field j)) :=
        fieldValues_outputTapes field output fieldOutput base bits
      rw [fieldsAfter] at second
      have combined := chain first second
      simp only [reset_reset, after, outputTapes_append] at combined
      have dropHead : tokens.drop i = tokens.get index :: tokens.drop (i + 1) :=
        List.drop_eq_getElem_cons hiLt
      have hstart : startAt tokens.length i = .entry index := by
        simp [startAt, hiLt, index]
      rw [hstart, dropHead]
      simp only [templateOutput, List.flatMap_cons]
      change _ = some (⟨exit, reset state, outputTapes base output
        (bits ++ templateOutput (tokens.drop (i + 1)) (fun j => base (field j)))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ))
      convert combined using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      simp only [workSteps, List.map_cons, List.sum_cons]
      omega

/-- The complete phase is derived from concrete instruction traces. The code
placement premise identifies instructions; it assumes no whole-phase run. -/
theorem phaseTrace (base : K → List Bool) (scratchEmpty : base scratch = [])
    (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[templateSteps tokens (fun j => base (field j))]
      (some ⟨some (place (startAt tokens.length 0)), state, base⟩) =
      some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩ := by
  simpa only [Nat.zero_add, List.drop_zero, templateSteps] using
    suffixTrace tokens field scratch output fieldScratch fieldOutput scratchOutput place exit P
      atInstruction tokens.length 0 (by omega) base scratchEmpty state

end Execution

def phaseInTime (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (place : Label tokens.length → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction tokens field scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (startAt tokens.length 0)), state, base⟩
      (some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩)
      (3 * copiedLength tokens (fun j => base (field j)) + 3 * tokens.length + 1) where
  steps := templateSteps tokens (fun j => base (field j))
  evals_in_steps := phaseTrace tokens field scratch output fieldScratch fieldOutput scratchOutput
    place exit P atInstruction base scratchEmpty state
  steps_le_m := templateSteps_le tokens _

end UniqueGamesTheorem.Reduction.MachineFieldTemplate

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SubdivisionTarget
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Concrete numbered, full-table output for the four-edge subdivision.
Original vertices keep their names. The new names are `n+e`, `n+Q+2e`,
and `n+Q+2e+1`, and each input occurrence emits four consecutive rows.
-/

namespace UniqueGamesTheorem.Explicit.SubdivisionTarget

open UniqueGamesTheorem.Foundations Target
open MachineOutputContract
open scoped BigOperators

/-- Retain every original list occurrence as its own edge identifier. -/
def ofInstance {q : Nat} (H : Instance q) :
    OccurrenceGame (Fin H.vertices) (Fin H.constraints.length) (Fin q) where
  source e := H.constraints[e].source
  target e := H.constraints[e].target
  permutation e := permutationEquiv H.constraints[e].permutation

def tables {q : Nat} (H : Instance q) (ei : Fin H.constraints.length × Fin 4) :
    PermutationTable q :=
  if ei.2 = 3 then MachineSubdivisionRows.inverseTable H.constraints[ei.1].permutation
  else MachineSubdivisionRows.identityTable q

/-- The five physical fields consumed by the checked row-emission phase. -/
def vertexFields {q : Nat} (H : Instance q) (e : Fin H.constraints.length) :
    Fin 5 → Fin (H.vertices + 3 * H.constraints.length) :=
  ![numericVertexEquiv _ _ (Sum.inl (Sum.inl H.constraints[e].source)),
    numericVertexEquiv _ _ (Sum.inr (e, false)),
    numericVertexEquiv _ _ (Sum.inl (Sum.inr e)),
    numericVertexEquiv _ _ (Sum.inr (e, true)),
    numericVertexEquiv _ _ (Sum.inl (Sum.inl H.constraints[e].target))]

theorem vertexFields_val {q : Nat} (H : Instance q) (e : Fin H.constraints.length)
    (j : Fin 5) :
    (vertexFields H e j).val = MachineSubdivisionRows.subdivisionVertexWords
      H.vertices H.constraints.length H.constraints[e].source.val
        H.constraints[e].target.val e.val j := by
  fin_cases j <;> simp [vertexFields, MachineSubdivisionRows.subdivisionVertexWords]

/-- Four consecutive semantic rows are exactly the four full-table rows emitted
by the machine phase, including the inverse table in the final row. -/
theorem rows_eq {q : Nat} (H : Instance q) (e : Fin H.constraints.length) :
    List.ofFn (fun i : Fin 4 => ProductTarget.row (Subdivision.game (ofInstance H))
      (numericVertexEquiv H.vertices H.constraints.length)
      (numericEdgeEquiv H.constraints.length) (tables H)
      ((numericEdgeEquiv H.constraints.length).symm (e, i))) =
    MachineSubdivisionRows.rows (vertexFields H e) H.constraints[e].permutation := by
  simp [List.ofFn_succ, ProductTarget.row, Subdivision.game, Subdivision.left,
    Subdivision.right, ofInstance, tables, vertexFields, MachineSubdivisionRows.rows]

/-- A deterministic full-table occurrence list with exactly four rows per input row. -/
def subdivide {q : Nat} (H : Instance q) : Instance q :=
  ProductTarget.render (Subdivision.game (ofInstance H))
    (numericVertexEquiv H.vertices H.constraints.length)
    (numericEdgeEquiv H.constraints.length) (tables H)
    (by have h := H.constraintCount_positive; omega)

@[simp] theorem subdivide_vertices {q : Nat} (H : Instance q) :
    (subdivide H).vertices = H.vertices + 3 * H.constraints.length := rfl

@[simp] theorem subdivide_length {q : Nat} (H : Instance q) :
    (subdivide H).constraints.length = 4 * H.constraints.length := by
  apply ProductTarget.render_length

end UniqueGamesTheorem.Explicit.SubdivisionTarget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SubdivisionEncoding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact whole-output serialization of four-edge subdivision. The input occurrence
at index `e` produces the four adjacent rows at `4e,4e+1,4e+2,4e+3`.
The bit formula uses the same complete row output as the checked machine phase.
-/

namespace UniqueGamesTheorem.Explicit.SubdivisionEncoding

open UniqueGamesTheorem.Foundations Target Complexity
open SubdivisionTarget

theorem subdivide_constraints {q : Nat} (H : Instance q) :
    (subdivide H).constraints =
      (List.ofFn (fun e : Fin H.constraints.length =>
        MachineSubdivisionRows.rows (vertexFields H e)
          H.constraints[e].permutation)).flatten := by
  change List.ofFn _ = _
  rw [List.ofFn_mul']
  congr 1
  apply congrArg List.ofFn
  funext e
  rw [← rows_eq H e]
  apply congrArg List.ofFn
  funext i
  congr 1
  apply Fin.ext
  simp only [numericEdgeEquiv_symm_val]

theorem subdivide_constraints_flatMap {q : Nat} (H : Instance q) :
    (subdivide H).constraints = (List.finRange H.constraints.length).flatMap
      (fun e => MachineSubdivisionRows.rows (vertexFields H e)
        H.constraints[e].permutation) := by
  rw [subdivide_constraints, List.ofFn_eq_map]
  rfl

/-- Header and complete row words, in the original input occurrence order. -/
theorem subdivide_gameWords {q : Nat} (H : Instance q) :
    gameWords (subdivide H) =
      [H.vertices + 3 * H.constraints.length, q, 4 * H.constraints.length] ++
      (List.finRange H.constraints.length).flatMap (fun e =>
        (MachineSubdivisionRows.rows (vertexFields H e)
          H.constraints[e].permutation).flatMap constraintWords) := by
  change [H.vertices + 3 * H.constraints.length, q, (subdivide H).constraints.length] ++
    (subdivide H).constraints.flatMap
      (@constraintWords (H.vertices + 3 * H.constraints.length) q) = _
  rw [subdivide_length, subdivide_constraints_flatMap, List.flatMap_assoc]

/-- Exact output bytes for the whole controller to emit: one header followed by
the verified four-row phase once per original occurrence. -/
theorem subdivide_gameBits {q : Nat} (H : Instance q) :
    gameBits (subdivide H) =
      encodeWords [H.vertices + 3 * H.constraints.length, q, 4 * H.constraints.length] ++
      (List.finRange H.constraints.length).flatMap (fun e =>
        MachineSubdivisionRows.rowBits (vertexFields H e) H.constraints[e].permutation) := by
  rw [gameBits, subdivide_gameWords, encodeWords_append, encodeWords_flatMap]
  rfl

end UniqueGamesTheorem.Explicit.SubdivisionEncoding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_UniformTarget
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Explicit.UniformTarget

open UniqueGamesTheorem.Foundations Target Complexity
open UniqueGamesTheorem.Integration
open MachineUniformCopyOrder

def construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) : Instance q where
  vertices := g.vertices
  constraints := copyMajor C g.constraints
  nonempty := by
    apply List.length_pos_iff.mp
    rw [copy_length]
    exact Nat.mul_pos hC g.constraintCount_positive

@[simp] theorem vertices {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    (construct C hC g).vertices = g.vertices := rfl

@[simp] theorem edge_count {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    (construct C hC g).constraints.length = C * g.constraints.length :=
  copy_length C g.constraints

theorem flatMap_copies {α β : Type*} (C : Nat) (xs : List α) (f : α → List β) :
    (copyMajor C xs).flatMap f = copyMajor C (xs.flatMap f) := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons,
      List.flatMap_append] using congrArg (fun ys => xs.flatMap f ++ ys) ih

/-- The complete output keeps the two first headers and scales the edge count. -/
theorem gameWords_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameWords (construct C hC g) =
      [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (g.constraints.flatMap constraintWords) := by
  simp only [gameWords, vertices]
  rw [show (construct C hC g).constraints = copyMajor C g.constraints from rfl,
    flatMap_copies, copy_length]

theorem gameBits_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameBits (construct C hC g) =
      encodeWords [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (encodeWords (g.constraints.flatMap constraintWords)) := by
  rw [gameBits, gameWords_construct, encodeWords_append, encode_copies]

end UniqueGamesTheorem.Explicit.UniformTarget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductSeed
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

namespace UniqueGamesTheorem.Explicit.MachineProductSeed

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open UniqueGamesTheorem.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

/-- Each literal has an actual one-transition trace in the ambient machine. -/
theorem seedTrace (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction commands labels exit l)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[commands.length]
      (some ⟨entry commands labels exit, (ambient, register), base⟩) =
      some ⟨exit, (ambient, register), finalTapes commands base⟩ := by
  have h := MachineFiniteSequence.trace LocalLabel (fun _ => ()) localInstruction
    result (fun _ _ => 1) program (fun _ => True) (fun _ => (ambient, register)) id commands
    (by intros; trivial)
    (by
      intro command hc localLabels localExit atLocal tapes ht
      have h := MachineInitialHeaders.literalTrace command.1 command.2.reverse
        (localLabels ()) localExit program (atLocal ()) tapes ambient register
      simpa only [List.reverse_reverse, id_eq, result] using h)
    labels exit atLabels base trivial
  simpa only [sequence_steps, entry, finalTapes, id_eq] using h

end UniqueGamesTheorem.Explicit.MachineProductSeed

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceFieldArrayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceFieldArray

open Turing
open UniqueGamesTheorem.Foundations.Complexity SourceMachine

variable {K Λ σ : Type} [DecidableEq K]

/-- Exact successive stack updates, in the original field order. -/
def sequenceTapes (source : K) (destination : Nat → K) (base : K → List Bool)
    (offset : Nat) (values : List Nat) (suffix : List Bool) : K → List Bool :=
  match values with
  | [] => base
  | n :: rest => sequenceTapes source destination
      (afterField source (destination offset) base n (encodeWords rest ++ suffix))
      (offset + 1) rest suffix

/-- The trace is built from the actual single-field transitions. The only
program premises identify the finitely many statements used by this record. -/
theorem sequenceTrace (source : K) (destination : Nat → K)
    (start loopLabel : Nat → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (atStart : ∀ r, r < values.length →
      program (start (offset + r)) = fieldStart (destination (offset + r)) (loopLabel (offset + r)))
    (atLoop : ∀ r, r < values.length → program (loopLabel (offset + r)) =
      fieldLoop source (destination (offset + r)) (loopLabel (offset + r))
        (some (start (offset + r + 1))))
    (atDone : program (start (offset + values.length)) = finish source exit)
    (hinput : base source = encodeWords values ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[values.sum + 2 * values.length + 1]
      (some ⟨some (start offset), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), sequenceTapes source destination base offset values suffix⟩ := by
  induction values generalizing offset base register with
  | nil =>
    simpa only [List.sum_nil, List.length_nil, Nat.mul_zero, Nat.zero_add,
      Nat.add_zero, Function.iterate_one, MachineComposition.advance_some, sequenceTapes]
      using finishStep source (start offset) exit program atDone base ambient register
  | cons n rest ih =>
    have hr0 : 0 < (n :: rest).length := by simp
    have hsep0 : source ≠ destination offset := by simpa using hsep 0 hr0
    have hs0 : program (start offset) = fieldStart (destination offset) (loopLabel offset) := by
      simpa using atStart 0 hr0
    have hl0 : program (loopLabel offset) = fieldLoop source (destination offset)
        (loopLabel offset) (some (start (offset + 1))) := by simpa using atLoop 0 hr0
    have hin : base source = encodeWord n ++ (encodeWords rest ++ suffix) := by
      simpa only [encodeWords, List.append_assoc] using hinput
    let nextBase := afterField source (destination offset) base n (encodeWords rest ++ suffix)
    have hfirst := (fieldInTime source (destination offset) hsep0 (start offset)
      (loopLabel offset) (some (start (offset + 1))) program hs0 hl0 base n
      (encodeWords rest ++ suffix) hin ambient register).evals_in_steps
    change (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some (start offset), (ambient, register), base⟩) =
      some ⟨some (start (offset + 1)), (ambient, none), nextBase⟩ at hfirst
    have hsep' : ∀ r, r < rest.length → source ≠ destination (offset + 1 + r) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsep (r + 1) (by simp; omega)
    have hs' : ∀ r, r < rest.length → program (start (offset + 1 + r)) =
        fieldStart (destination (offset + 1 + r)) (loopLabel (offset + 1 + r)) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atStart (r + 1) (by simp; omega)
    have hl' : ∀ r, r < rest.length → program (loopLabel (offset + 1 + r)) =
        fieldLoop source (destination (offset + 1 + r)) (loopLabel (offset + 1 + r))
          (some (start (offset + 1 + r + 1))) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atLoop (r + 1) (by simp; omega)
    have hd' : program (start (offset + 1 + rest.length)) = finish source exit := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atDone
    have hin' : nextBase source = encodeWords rest ++ suffix := by
      simp [nextBase, afterField, hsep0]
    rw [show (n :: rest).sum + 2 * (n :: rest).length + 1 =
      (rest.sum + 2 * rest.length + 1) + (n + 2) by simp; omega]
    rw [Function.iterate_add_apply, hfirst,
      ih nextBase (offset + 1) hsep' hs' hl' hd' hin' none]
    rfl

def sequenceInTime (source : K) (destination : Nat → K)
    (start loopLabel : Nat → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (atStart : ∀ r, r < values.length →
      program (start (offset + r)) = fieldStart (destination (offset + r)) (loopLabel (offset + r)))
    (atLoop : ∀ r, r < values.length → program (loopLabel (offset + r)) =
      fieldLoop source (destination (offset + r)) (loopLabel (offset + r))
        (some (start (offset + r + 1))))
    (atDone : program (start (offset + values.length)) = finish source exit)
    (hinput : base source = encodeWords values ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (start offset), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), sequenceTapes source destination base offset values suffix⟩)
      (values.sum + 2 * values.length + 1) where
  steps := values.sum + 2 * values.length + 1
  evals_in_steps := sequenceTrace source destination start loopLabel exit program base offset
    values suffix hsep atStart atLoop atDone hinput ambient register
  steps_le_m := Nat.le_refl _

theorem sequenceTapes_other (source : K) (destination : Nat → K)
    (p : K) (hpS : p ≠ source) (base : K → List Bool) (offset : Nat)
    (values : List Nat) (suffix : List Bool)
    (hpD : ∀ r, r < values.length → p ≠ destination (offset + r)) :
    sequenceTapes source destination base offset values suffix p = base p := by
  induction values generalizing base offset with
  | nil => rfl
  | cons n rest ih =>
    have hp0 : p ≠ destination offset := by simpa using hpD 0 (by simp)
    have htail : ∀ r, r < rest.length → p ≠ destination (offset + 1 + r) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpD (r + 1) (by simp; omega)
    rw [sequenceTapes, ih _ (offset + 1) htail]
    exact fieldTapes_other source (destination offset) p hpS hp0 _ _ _

theorem sequenceTapes_source (source : K) (destination : Nat → K)
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (hinput : base source = encodeWords values ++ suffix) :
    sequenceTapes source destination base offset values suffix source = suffix := by
  induction values generalizing base offset with
  | nil => simpa [sequenceTapes, encodeWords] using hinput
  | cons n rest ih =>
    have hsep0 : source ≠ destination offset := by simpa using hsep 0 (by simp)
    have htail : ∀ r, r < rest.length → source ≠ destination (offset + 1 + r) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsep (r + 1) (by simp; omega)
    apply ih _ (offset + 1) htail
    simp [afterField, hsep0]

/-- Distinct field destinations contain exactly their own encoded value. -/
theorem sequenceTapes_selected (source : K) (destination : Nat → K)
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (j : Nat) (hj : j < values.length)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (hdist : ∀ r s, r < values.length → s < values.length →
      destination (offset + r) = destination (offset + s) → r = s) :
    sequenceTapes source destination base offset values suffix (destination (offset + j)) =
      encodeWord (values[j]'hj) ++ base (destination (offset + j)) := by
  induction values generalizing base offset j with
  | nil => simp at hj
  | cons n rest ih =>
    have hsep0 : source ≠ destination offset := by simpa using hsep 0 (by simp)
    let nextBase := afterField source (destination offset) base n (encodeWords rest ++ suffix)
    cases j with
    | zero =>
      have hframe : ∀ r, r < rest.length → destination offset ≠ destination (offset + 1 + r) := by
        intro r hr heq
        have hh := hdist 0 (r + 1) (by simp) (by simp; omega)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)
        omega
      simp only [sequenceTapes, Nat.add_zero, List.getElem_cons_zero]
      rw [sequenceTapes_other source destination (destination offset) hsep0.symm _
        (offset + 1) rest suffix hframe]
      simp [afterField]
    | succ j =>
      have hj' : j < rest.length := by simpa using hj
      have hsep' : ∀ r, r < rest.length → source ≠ destination (offset + 1 + r) := by
        intro r hr
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsep (r + 1) (by simp; omega)
      have hdist' : ∀ r s, r < rest.length → s < rest.length →
          destination (offset + 1 + r) = destination (offset + 1 + s) → r = s := by
        intro r s hr hs heq
        have hh := hdist (r + 1) (s + 1) (by simp; omega) (by simp; omega)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)
        omega
      have hsrc : destination (offset + 1 + j) ≠ source := (hsep' j hj').symm
      have hdst : destination (offset + 1 + j) ≠ destination offset := by
        intro heq
        have hh := hdist (j + 1) 0 hj (by simp)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)
        omega
      have hkeep : nextBase (destination (offset + 1 + j)) = base (destination (offset + 1 + j)) :=
        fieldTapes_other source (destination offset) _ hsrc hdst _ _ _
      simp only [sequenceTapes, List.getElem_cons_succ]
      rw [show offset + (j + 1) = offset + 1 + j by omega]
      rw [ih _ (offset + 1) j hj' hsep' hdist']
      exact congrArg (encodeWord rest[j] ++ ·) hkeep

end UniqueGamesTheorem.Foundations.Hastad.SourceFieldArray

namespace UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition SourceMachine

section Discard

variable {K Λ σ : Type} [DecidableEq K]

/-- Compose the actual unary scanners for a fixed sequence of control labels.
The zero-field case is an identity, so the head register starts and ends clear. -/
theorem discardFieldsTrace (source : K) (label : Nat → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (atLoop : ∀ r, r < values.length → program (label (offset + r)) =
      MachineLookup.discard source (label (offset + r)) (label (offset + r + 1)))
    (hinput : base source = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (label offset), (ambient, none), base⟩) =
      some ⟨some (label (offset + values.length)), (ambient, none),
        Function.update base source suffix⟩ := by
  induction values generalizing base offset with
  | nil =>
    have hbase : Function.update base source suffix = base := by
      have hs : base source = suffix := by simpa only [encodeWords, List.nil_append] using hinput
      funext p
      by_cases hp : p = source
      · subst p; simp [hs]
      · simp [hp]
    simp only [encodeWords, List.length_nil, Nat.add_zero, Function.iterate_zero_apply, hbase]
  | cons n rest ih =>
    have hs : program (label offset) =
        MachineLookup.discard source (label offset) (label (offset + 1)) := by
      simpa only [Nat.add_zero] using atLoop 0 (by simp)
    have hin : base source = encodeWord n ++ (encodeWords rest ++ suffix) := by
      simpa only [encodeWords, List.append_assoc] using hinput
    have first := MachineLookup.discardTrace source (label offset) (label (offset + 1))
      program hs base n (encodeWords rest ++ suffix) hin ambient none
    have htail : ∀ r, r < rest.length → program (label (offset + 1 + r)) =
        MachineLookup.discard source (label (offset + 1 + r))
          (label (offset + 1 + r + 1)) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        atLoop (r + 1) (by simp; omega)
    have second := ih (Function.update base source (encodeWords rest ++ suffix))
      (offset + 1) htail (by simp)
    rw [show (encodeWords (n :: rest)).length = (encodeWords rest).length + (n + 1) by
      simp only [encodeWords, List.length_append, encodeWord_length]
      omega]
    rw [Function.iterate_add_apply, first]
    simpa [Function.update_idem, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

end Discard

end UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceLoopInitLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

/-- Exact execution, including the real drain loops, reversal, and reset. The
only program hypotheses identify the caller's actual placed statements. -/
def finishInTime (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (canonical : σ) (labels : Label clearKeys → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ label,
      program (labels label) = statement clearKeys accumulator output canonical labels exit label)
    (base : Tapes K) (outputEmpty : base output = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩)
      (finishCost clearKeys accumulator base) := by
  let cleared := MachineDrainMany.finalTapes clearKeys base
  let afterRegister := MachineDrainMany.finalRegister clearKeys register
  let drain : StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩)
      (MachineDrainMany.steps clearKeys base) := {
    steps := MachineDrainMany.steps clearKeys base
    evals_in_steps := MachineDrainMany.trace clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) program (fun l => atLabels (.inl l)) base ambient register
    steps_le_m := Nat.le_refl _ }
  have acc : cleared accumulator = base accumulator := cleared_frame _ _ _ keepAccumulator
  have out : cleared output = [] := (cleared_frame _ _ _ keepOutput).trans outputEmpty
  let reverse : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩
      (some ⟨some (labels (.inr true)), (ambient, none),
        canonicalTapes output (base accumulator).reverse⟩) ((base accumulator).length + 1) := {
    steps := (base accumulator).length + 1
    evals_in_steps := by
      change (Reduction.MachineTransfer.nextAt output program)^[(base accumulator).length + 1]
        (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩) = _
      have run := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
        accumulator output distinct id false (labels (.inr false))
        (some (labels (.inr true))) program
        (by simpa only [statement] using atLabels (.inr false)) cleared ambient afterRegister
      simpa only [acc, out, List.map_id, List.append_nil,
        cleared, reversed_tapes clearKeys accumulator output distinct covers base] using run
    steps_le_m := Nat.le_refl _ }
  let reset : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr true)), (ambient, none), canonicalTapes output (base accumulator).reverse⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (labels (.inr true))) _ _) = _
      rw [atLabels]
      cases exit <;> rfl
    steps_le_m := Nat.le_refl _ }
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ drain reverse
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first reset
  have hsteps : run.steps = finishCost clearKeys accumulator base := by
    change 1 + ((base accumulator).length + 1 + MachineDrainMany.steps clearKeys base) = _
    unfold finishCost
    omega
  exact {
    steps := finishCost clearKeys accumulator base
    evals_in_steps := by simpa only [hsteps] using run.evals_in_steps
    steps_le_m := Nat.le_refl _ }

open scoped BigOperators

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeFinish

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineTupleOdometer
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_increment_succ (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d r : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix) =
      ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord, List.replicate_succ, update_current, update_remaining]

theorem stepAux_increment_zero (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d 0 currentSuffix remainingSuffix) =
      ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord]

/-- A non-carrying digit increment is one actual ambient-program transition. -/
theorem incrementStep_succ (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix⟩ =
      some ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_succ current remaining distinct]

theorem incrementStep_zero (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ =
      some ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_zero current remaining distinct]

theorem resetTrace (current remaining : K) (distinct : current ≠ remaining)
    (resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 1]
      (some ⟨some resetLabel, (ambient, register),
        digitTapes current remaining base d r currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 (d + r) currentSuffix remainingSuffix⟩ :=
  MachineUnaryAddAt.addTrace current remaining distinct resetLabel (some carryLabel)
    program atReset base d r currentSuffix remainingSuffix ambient register

/-- Exhaustion costs one check plus the actual `d + 1`-transition reset. -/
theorem carryTrace (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 2]
      (some ⟨some checkLabel, (ambient, register),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 d currentSuffix remainingSuffix⟩ := by
  rw [show d + 2 = (d + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[d + 1]
    (TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) = _
  rw [incrementStep_zero current remaining distinct checkLabel doneLabel resetLabel
    program atCheck]
  simpa only [Nat.add_zero] using resetTrace current remaining distinct resetLabel carryLabel
    program atReset base d 0 currentSuffix remainingSuffix ambient none

section AscendingCycle

open scoped BigOperators

def bodyConfiguration (current remaining : K) (bodyLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (remainder + 1), none),
    digitTapes current remaining (base (remainder + 1)) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def checkConfiguration (current remaining : K) (checkLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some checkLabel, (ambient remainder, register remainder),
    digitTapes current remaining (base remainder) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def cycleExit (current remaining : K) (exitLabel : Λ)
    (maximum : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none),
    digitTapes current remaining (base 0) 0 maximum currentSuffix remainingSuffix⟩

def VisitTraces (current remaining : K) (bodyLabel checkLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (maximum count : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) : Prop :=
  ∀ r, r ≤ count → (MachineComposition.advance (TM2.step program))^[cost r]
    (some (bodyConfiguration current remaining bodyLabel maximum r
      currentSuffix remainingSuffix ambient base)) =
    some (checkConfiguration current remaining checkLabel maximum r
      currentSuffix remainingSuffix ambient register base)

theorem cycleTrace (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (maximum count : ℕ) (hcount : count ≤ maximum)
    (currentSuffix remainingSuffix : List Bool) (ambient : ℕ → σ)
    (register : ℕ → Option Bool) (base : ℕ → K → List Bool) (cost : ℕ → ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program maximum count
      currentSuffix remainingSuffix ambient register base cost) :
    (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (some (bodyConfiguration current remaining bodyLabel maximum count
        currentSuffix remainingSuffix ambient base)) =
      some (cycleExit current remaining exitLabel maximum
        currentSuffix remainingSuffix ambient base) := by
  induction count with
  | zero =>
    rw [cycleSteps_zero, Function.iterate_add_apply, visits 0 (Nat.le_refl 0)]
    simpa only [checkConfiguration, cycleExit, Nat.sub_zero] using
      carryTrace current remaining distinct checkLabel bodyLabel resetLabel exitLabel
        program atCheck atReset (base 0) maximum currentSuffix remainingSuffix
        (ambient 0) (register 0)
  | succ count ih =>
    rw [cycleSteps_succ, Function.iterate_add_apply, visits (count + 1) (Nat.le_refl _),
      Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (TM2.step program ⟨some checkLabel, (ambient (count + 1), register (count + 1)),
        digitTapes current remaining (base (count + 1)) (maximum - (count + 1))
          (count + 1) currentSuffix remainingSuffix⟩) = _
    rw [incrementStep_succ current remaining distinct checkLabel bodyLabel resetLabel
      program atCheck]
    have hnext : maximum - (count + 1) + 1 = maximum - count := by omega
    rw [hnext]
    exact ih (by omega) (fun r hr => visits r (by omega))

/-- A full positive-radix cycle performs `n` body visits and exactly `2*n`
counter transitions. This bound comes from the composed actual execution. -/
def ascendingCycleInTime (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (n : ℕ) (hn : 0 < n) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) (B : ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program (n - 1) (n - 1)
      currentSuffix remainingSuffix ambient register base cost)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    StateTransition.EvalsToInTime (TM2.step program)
      (bodyConfiguration current remaining bodyLabel (n - 1) (n - 1)
        currentSuffix remainingSuffix ambient base)
      (some (cycleExit current remaining exitLabel (n - 1)
        currentSuffix remainingSuffix ambient base)) (n * (B + 2)) where
  steps := cycleSteps cost (n - 1) (n - 1)
  evals_in_steps := cycleTrace current remaining distinct bodyLabel checkLabel resetLabel exitLabel
    program atCheck atReset (n - 1) (n - 1) (Nat.le_refl _) currentSuffix remainingSuffix
    ambient register base cost visits
  steps_le_m := by
    have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
      calc
        _ ≤ ∑ _r ∈ Finset.range n, B :=
          Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
        _ = _ := by simp
    have hn' : n - 1 + 1 = n := by omega
    simp only [cycleSteps, hn', Nat.mul_add] at *
    omega

end AscendingCycle

section Nested

open scoped BigOperators

/-- A finite nesting schedule. Only leaves supply actual emitter traces.
Internal nodes supply concrete instruction placements and compatible endpoint
schedules; their complete execution is derived below. Level `q` operates
coordinate `q`, so coordinate zero is always the innermost loop. -/
inductive NestedCycle (n : ℕ) (current remaining : ℕ → K) (bodyLabel : Λ)
    (checkLabel resetLabel : ℕ → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) :
    ℕ → Λ → Configuration K Λ σ → Configuration K Λ σ → Type where
  | leaf (exitLabel : Λ) (start finish : Configuration K Λ σ) (count : ℕ)
      (atBody : start.l = some bodyLabel) (atExit : finish.l = some exitLabel)
      (run : (MachineComposition.advance (TM2.step program))^[count] (some start) = some finish) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        0 exitLabel start finish
  | node (depth : ℕ) (exitLabel : Λ) (positive : 0 < n)
      (distinct : current depth ≠ remaining depth)
      (atCheck : program (checkLabel depth) =
        increment (current depth) (remaining depth) bodyLabel (resetLabel depth))
      (atReset : program (resetLabel depth) =
        reset (current depth) (remaining depth) (resetLabel depth) exitLabel)
      (s : CycleSchedule K σ)
      (children : ∀ r : Fin n,
        NestedCycle n current remaining bodyLabel checkLabel resetLabel program
          depth (checkLabel depth)
          (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.base)
          (checkConfiguration (current depth) (remaining depth) (checkLabel depth) (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.register s.base)) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        (depth + 1) exitLabel
        (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (current depth) (remaining depth) exitLabel (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

def steps {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : ℕ :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count
  | .node _ _ _ _ _ _ _ children =>
    cycleSteps (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) (n - 1) (n - 1)
termination_by depth

/-- Every supplied emitter leaf obeys its local time allowance. There is no
whole-loop runtime premise at any internal node. -/
def LeafBound (B : ℕ) {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : Prop :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count ≤ B
  | .node _ _ _ _ _ _ _ children => ∀ r, LeafBound B (children r)
termination_by depth

/-- The whole nested-loop trace is derived from its actual leaf traces and
the concrete increment/reset code. -/
theorem trace {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) :
    (MachineComposition.advance (TM2.step program))^[tree.steps] (some start) = some finish := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run => simpa only [steps] using run
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [steps]
    apply cycleTrace (current depth) (remaining depth) distinct bodyLabel (checkLabel depth)
      (resetLabel depth) exitLabel program atCheck atReset (n - 1) (n - 1)
      (Nat.le_refl _) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
    intro r hr
    have hlt : r < n := by omega
    simpa only [dite_eq_left hlt] using ih ⟨r, hlt⟩

theorem steps_le {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ n ^ depth * B + counterOverhead n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simpa only [steps, LeafBound, counterOverhead, pow_zero, Nat.one_mul, Nat.add_zero] using bounded
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [LeafBound] at bounded
    have visits : VisitTraces (current depth) (remaining depth) bodyLabel (checkLabel depth)
        program (n - 1) (n - 1) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
        (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) := by
      intro r hr
      have hlt : r < n := by omega
      simpa only [dite_eq_left hlt] using (children ⟨r, hlt⟩).trace
    have bodyBound : ∀ r, r < n →
        (if hr : r < n then steps (children ⟨r, hr⟩) else 0) ≤
          n ^ depth * B + counterOverhead n depth := by
      intro r hr
      simpa only [dite_eq_left hr] using ih ⟨r, hr⟩ (bounded ⟨r, hr⟩)
    have h := (ascendingCycleInTime (current depth) (remaining depth) distinct bodyLabel
      (checkLabel depth) (resetLabel depth) exitLabel program atCheck atReset n positive
      s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
      (n ^ depth * B + counterOverhead n depth) visits bodyBound).steps_le_m
    change cycleSteps _ (n - 1) (n - 1) ≤ _ at h
    simpa only [steps, counterOverhead, pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc] using h

end NestedCycle

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

theorem steps_le_power {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (hn : 0 < n) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ (B + 2 * depth) * n ^ depth := by
  have h := (tree.steps_le B bounded).trans
    (Nat.add_le_add_left (counterOverhead_le n depth hn) (n ^ depth * B))
  simpa only [Nat.add_mul, Nat.mul_add, Nat.mul_comm] using h

end NestedCycle

end Nested

end UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_EncodingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.CanonicalWordTemplate

open Foundations.Complexity CanonicalEncoding

def singleTemplate {s d : Nat} (index : Fin 3) (coefficient : Ambient s d) : List Token :=
  [.literal 1, .name index, .literal 0,
    .literal (vectorWord coefficient.1), .literal (vectorWord coefficient.2),
    .literal 0, .literal 0, .literal 0, .literal 0]

def fullTemplate {s d : Nat} (coefficients : Fin 3 → Ambient s d) : List Token :=
  [.literal 2, .literal 0, .occurrence,
    .literal (vectorWord (coefficients 0).1), .literal (vectorWord (coefficients 0).2),
    .literal (vectorWord (coefficients 1).1), .literal (vectorWord (coefficients 1).2),
    .literal (vectorWord (coefficients 2).1), .literal (vectorWord (coefficients 2).2)]

/-- Coefficient equality alone selects the record tag and the input field. -/
def template {s d : Nat} (a : Fin 3 → Ambient s d) : List Token :=
  if a 0 = a 1 then
    if a 0 = a 2 then blankTemplate else singleTemplate 2 (a 2 + a 0)
  else if a 0 = a 2 then singleTemplate 1 (a 1 + a 0)
  else if a 1 = a 2 then singleTemplate 0 (a 0 + a 2)
  else fullTemplate (ActualCanonical.normalize a)

@[simp] theorem blankTemplate_length : blankTemplate.length = 9 := rfl

@[simp] theorem singleTemplate_length {s d : Nat} (index : Fin 3)
    (coefficient : Ambient s d) : (singleTemplate index coefficient).length = 9 := rfl

@[simp] theorem fullTemplate_length {s d : Nat} (coefficients : Fin 3 → Ambient s d) :
    (fullTemplate coefficients).length = 9 := rfl

@[simp] theorem template_length {s d : Nat} (a : Fin 3 → Ambient s d) :
    (template a).length = 9 := by
  unfold template
  split_ifs <;> rfl

@[simp] theorem evalTemplate_length (names : Fin 3 → Nat) (occurrence : Nat)
    (tokens : List Token) : (evalTemplate names occurrence tokens).length = tokens.length :=
  List.length_map _

/-- The template evaluates to the exact existing canonical-record encoding. -/
theorem eval_template {n m s d : Nat} (names : Fin m → Fin 3 → Fin n)
    (occurrence : Fin m) (a : Fin 3 → Ambient s d) :
    evalTemplate (fun j => (names occurrence j).val) occurrence.val (template a) =
      recordWords (ActualCanonical.record names occurrence a) := by
  unfold template ActualCanonical.record
  split_ifs <;> rfl

end UniqueGamesTheorem.Reduction.CanonicalWordTemplate

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_CanonicalBodyTemplateLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.CanonicalBodyTemplate

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding
open scoped BigOperators

variable {k : Nat}

def liftToken (j : Fin k) : CanonicalWordTemplate.Token → Token k
  | .literal value => .literal value
  | .name index => .field j (nameField index)
  | .occurrence => .field j 3

def liftRecord (j : Fin k) (tokens : List CanonicalWordTemplate.Token) : List (Token k) :=
  tokens.map (liftToken j)

@[simp] theorem liftRecord_length (j : Fin k) (tokens : List CanonicalWordTemplate.Token) :
    (liftRecord j tokens).length = tokens.length := List.length_map _

theorem eval_liftToken {n m k : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (j : Fin k) (token : CanonicalWordTemplate.Token) :
    evalToken (sourceFields occ names) (liftToken j token) =
      CanonicalWordTemplate.evalToken (fun i => (names (occ j) i).val) (occ j).val token := by
  cases token <;> simp [evalToken, sourceFields, liftToken, CanonicalWordTemplate.evalToken]

theorem eval_liftRecord {n m k : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (j : Fin k)
    (tokens : List CanonicalWordTemplate.Token) :
    evalTemplate (sourceFields occ names) (liftRecord j tokens) =
      CanonicalWordTemplate.evalTemplate (fun i => (names (occ j) i).val) (occ j).val tokens := by
  simp only [evalTemplate, liftRecord, List.map_map, Function.comp_def, eval_liftToken,
    CanonicalWordTemplate.evalTemplate]

def recordsList {k s d : Nat} (a : Fin k → Fin 3 → Ambient s d)
    (positions : List (Fin k)) : List (Token k) :=
  positions.flatMap (fun j => liftRecord j (CanonicalWordTemplate.template (a j)))

theorem recordsList_length {k s d : Nat} (a : Fin k → Fin 3 → Ambient s d)
    (positions : List (Fin k)) : (recordsList a positions).length = 9 * positions.length := by
  induction positions with
  | nil => rfl
  | cons j positions ih =>
    change (liftRecord j (CanonicalWordTemplate.template (a j)) ++
      recordsList a positions).length = 9 * (positions.length + 1)
    rw [List.length_append, liftRecord_length, CanonicalWordTemplate.template_length, ih]
    omega

theorem eval_recordsList {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (a : Fin k → Fin 3 → Ambient s d)
    (positions : List (Fin k)) :
    evalTemplate (sourceFields occ names) (recordsList a positions) =
      (positions.map (fun j => ActualCanonical.record names (occ j) (a j))).flatMap recordWords := by
  induction positions with
  | nil => rfl
  | cons j positions ih =>
    change
      evalTemplate (sourceFields occ names)
          (liftRecord j (CanonicalWordTemplate.template (a j)) ++ recordsList a positions) =
        recordWords (ActualCanonical.record names (occ j) (a j)) ++
          (positions.map (fun i => ActualCanonical.record names (occ i) (a i))).flatMap recordWords
    rw [show ∀ xs ys, evalTemplate (sourceFields occ names) (xs ++ ys) =
      evalTemplate (sourceFields occ names) xs ++ evalTemplate (sourceFields occ names) ys by
      intro xs ys; exact List.map_append]
    rw [eval_liftRecord, CanonicalWordTemplate.eval_template, ih]

def ambientShift {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) : Ambient s d :=
  z + ∑ j, b j • ActualCanonical.pivot (a j)

def alphabetOffset {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) : Vector s :=
  (ambientShift z a b).1

def template {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) : List (Token k) :=
  .literal (vectorWord (ambientShift z a b).2) :: recordsList a (List.ofFn id)

@[simp] theorem template_length {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) :
    (template z a b).length = 1 + 9*k := by
  simp [template, recordsList_length, Nat.add_comm]

/-- Exact body serialization of general canonical data. -/
theorem eval_data {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (z : Ambient s d) (a : Fin k → Fin 3 → Ambient s d) :
    evalTemplate (sourceFields occ names) (template z a (fun j => rhs (occ j))) =
      bodyWords ((ActualCanonical.data occ names rhs z a).1.2,
        (ActualCanonical.data occ names rhs z a).2) := by
  change
    vectorWord (ambientShift z a (fun j => rhs (occ j))).2 ::
        evalTemplate (sourceFields occ names) (recordsList a (List.ofFn id)) =
      vectorWord (ambientShift z a (fun j => rhs (occ j))).2 ::
        (List.ofFn (fun j => ActualCanonical.record names (occ j) (a j))).flatMap recordWords
  rw [eval_recordsList, List.map_ofFn]
  rfl

theorem eval_canonical {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (X : ActualHomogeneous.E k →ₗ[F2] Ambient s d) :
    evalTemplate (sourceFields occ names)
        (template (X (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple X)
          (fun j => rhs (occ j))) =
      bodyWords ((ActualCanonical.canonical occ names rhs X).1.2,
        (ActualCanonical.canonical occ names rhs X).2) :=
  eval_data occ names rhs _ _

theorem eval_actualQuery (S : ActualSource.Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    evalTemplate (sourceFields q.1 (ActualGame.names S))
        (template (q.2 (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple q.2)
          (fun j => ActualGame.rhs S (q.1 j))) =
      bodyWords (ActualOrbit.body (ActualGame.canonical S k s d) q) :=
  eval_canonical q.1 (ActualGame.names S) (ActualGame.rhs S) q.2

theorem flatMap_encodeWord (fields : Fin k → Fin 4 → Nat) (tokens : List (Token k)) :
    tokens.flatMap (fun token => encodeWord (evalToken fields token)) =
      encodeWords (evalTemplate fields tokens) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.flatMap_cons, evalTemplate, List.map_cons, encodeWords]
    exact congrArg (List.append (encodeWord (evalToken fields token))) ih

end UniqueGamesTheorem.Reduction.CanonicalBodyTemplate

end

section

/-! Lower a complete canonical-body template to the actual field-template
machine. There are four saved fields per query position, numbered by
`field + 4 * position`. The template constants depend only on finite coefficient
and RHS data; names and occurrence identifiers remain saved tape contents. -/

namespace UniqueGamesTheorem.Reduction.CanonicalBodyMachine

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding

variable {k : Nat}

def lowerToken : CanonicalBodyTemplate.Token k → MachineFieldTemplate.Token (4*k)
  | .literal value => .literal (encodeWord value)
  | .field position field => .copy (fieldIndex position field)

def lowerTemplate (tokens : List (CanonicalBodyTemplate.Token k)) :
    List (MachineFieldTemplate.Token (4*k)) := tokens.map lowerToken

@[simp] theorem lowerTemplate_length (tokens : List (CanonicalBodyTemplate.Token k)) :
    (lowerTemplate tokens).length = tokens.length := List.length_map _

theorem tokenOutput_lowerToken (fields : Fin k → Fin 4 → Nat)
    (token : CanonicalBodyTemplate.Token k) :
    MachineFieldTemplate.tokenOutput (savedFields fields) (lowerToken token) =
      encodeWord (CanonicalBodyTemplate.evalToken fields token) := by
  cases token <;>
    simp [lowerToken, MachineFieldTemplate.tokenOutput, CanonicalBodyTemplate.evalToken]

theorem templateOutput_lowerTemplate (fields : Fin k → Fin 4 → Nat)
    (tokens : List (CanonicalBodyTemplate.Token k)) :
    MachineFieldTemplate.templateOutput (lowerTemplate tokens) (savedFields fields) =
      encodeWords (CanonicalBodyTemplate.evalTemplate fields tokens) := by
  simp only [MachineFieldTemplate.templateOutput, lowerTemplate, List.flatMap_map,
    tokenOutput_lowerToken]
  exact CanonicalBodyTemplate.flatMap_encodeWord fields tokens

/-- This fixed token list is directly accepted by the actual template machine. -/
def template {k s d : Nat} (z : Ambient s d) (a : Fin k → Fin 3 → Ambient s d)
    (b : Fin k → F2) : List (MachineFieldTemplate.Token (4*k)) :=
  lowerTemplate (CanonicalBodyTemplate.template z a b)

@[simp] theorem template_length {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) :
    (template z a b).length = 1 + 9*k := by
  simp [template]

end UniqueGamesTheorem.Reduction.CanonicalBodyMachine

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceOccurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Executable radix numbering of padded global long-code tables and an ordered
equation occurrence list. The code enumerates random tapes, not distinct
equations: coinciding equations and repeated variable occurrences are retained.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

theorem findValid_none_iff {J : Type} (valid : J → Bool) (xs : List J) :
    findValid valid xs = none ↔ ∀ j ∈ xs, valid j = false := by
  induction xs with
  | nil => simp [findValid]
  | cons j xs ih =>
    by_cases hj : valid j = true
    · simp [findValid, hj]
    · simp [findValid, hj, ih]

theorem firstValid_none_iff {J : Type} (e : Encoding J) (valid : J → Bool) :
    firstValid e valid = none ↔ ∀ j, valid j = false := by
  rw [firstValid, findValid_none_iff]
  exact ⟨fun h j => h j (e.mem_enumerate j), fun h j _ => h j⟩

section ConcreteSource

open SourceContexts
open UniqueGamesTheorem.Reduction.FiniteNoise

theorem rightAnchor_none_iff (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    rightAnchor F c = none ↔ ∀ j : J u, validJ F c j = false :=
  firstValid_none_iff _ _

def leftResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : Cube (I u) → Bool :=
  foldedAnswer (leftAnchor u) (fun h => bits ((proofEncoding F u).code (.inl (v, h.val))))

def rightResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (c : ClauseContext F u) : Cube (J u) → Bool :=
  match rightAnchor F c with
  | none => fun _ => false
  | some j₀ => conditionedFoldedAnswer (validJ F c) j₀
      (fun h => bits ((proofEncoding F u).code (.inr (.inl (c, extendRestricted (validJ F c) h.val)))))

end ConcreteSource

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHonestLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHonest

open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise
open scoped BigOperators

open SourceContexts
open SourceOccurrences

@[simp] theorem honestBits_dummy (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) :
    honestBits F u assignment (dummyIndex F u) = false := by
  rw [dummyIndex, honestBits_code]
  rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceHonest

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise

abbrev LocalKey (u : ℕ) := Cube (I u) ⊕ (Cube (J u) ⊕ Unit)
abbrev LocalInput (u D : ℕ) := Signature u × SourceTape.TestTape (I u) (J u) D

def emptyLocalAddress (u : ℕ) : EmptyContext.Address (leftAnchor u) → LocalKey u
  | .inl f => .inl f.val
  | .inr _ => .inr (.inr ())

def foldedLocalAddress (u : ℕ) (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    FoldedEquation.Address (leftAnchor u) j₀ → LocalKey u
  | .inl f => .inl f.val
  | .inr g => .inr (.inl (extendRestricted valid g.val))

/-- One local descriptor, reusing the existing folded and empty-context
equations. The first-valid search is over the fixed explicit answer encoding. -/
def equationFor (u D : ℕ) (valid : J u → Bool) (π : J u → I u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  match firstValid (jEncoding u) valid with
  | none => mapEquation (emptyLocalAddress u) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => mapEquation (foldedLocalAddress u valid j₀)
      (FoldedEquation.conditionedEquation valid π (leftAnchor u) j₀
        t.1 t.2.2 (realizedNoise t.2.1))

def equation (u D : ℕ) (σ : Signature u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  equationFor u D (signatureValid σ) (signatureProjection σ) t

def emit (u D : ℕ) (p : LocalInput u D) : Equation (LocalKey u) :=
  equation u D p.1 p.2

def addressMap (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) : LocalKey u → Fin (nBits F u)
  | .inl f => (proofEncoding F u).code (.inl (v, f))
  | .inr (.inl g) => (proofEncoding F u).code (.inr (.inl (c, g)))
  | .inr (.inr _) => dummyIndex F u

end UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences SourceLocalEquation SourceLocalSignature
open UniqueGamesTheorem.Reduction.CloneGap

def descriptor (u : ℕ) : LocalKey u → Descriptor
  | .inl f => (0, (((iEncoding u).function Encoding.bool).code f).val)
  | .inr (.inl g) => (1, (((jEncoding u).function Encoding.bool).code g).val)
  | .inr (.inr _) => (2, 0)

def words (base : Fin 3 → ℕ) (e : Equation Descriptor) : List ℕ :=
  [realize base e.first, realize base e.second, realize base e.third,
    if e.rhs then 1 else 0]

end UniqueGamesTheorem.Foundations.Hastad.SourceAddressDescriptors

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceSignaturePrepareLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/
noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

def leftTable (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : HalfCube (leftAnchor u) → Bool :=
  fun h => bits ((proofEncoding F u).code (.inl (v, h.val)))

def rightOracle (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (c : ClauseContext F u) : ConditionedOracle (validJ F c) :=
  match h : rightAnchor F c with
  | none => .empty ((rightAnchor_none_iff F c).mp h)
  | some j₀ => .stored j₀
      (fun h => bits ((proofEncoding F u).code
        (.inr (.inl (c, extendRestricted (validJ F c) h.val)))))

@[simp] theorem rightOracle_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (c : ClauseContext F u) :
    (rightOracle F u bits c).answer = rightResponse F u bits c := by
  unfold rightOracle
  split <;> simp_all [rightResponse, ConditionedOracle.answer]

@[simp] theorem leftTable_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (v : VariableContext F u) :
    foldedAnswer (leftAnchor u) (leftTable F u bits v) = leftResponse F u bits v := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceSoundness

end

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTestEmit

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit
open UniqueGamesTheorem.Reduction.CloneGap
open Complexity

abbrev State (u D : ℕ) := LocalInput u D × Option Bool

def localEquation (u D : ℕ) (state : LocalInput u D) : Equation Descriptor :=
  mapEquation (descriptor u) (SourceLocalEquation.emit u D state)

end UniqueGamesTheorem.Foundations.Hastad.SourceTestEmit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit SourceTestEmit

def equationBits (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : List Bool :=
  encodeWords (words values (localEquation u D state))

end UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryLoopLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual fixed finite traversal of all query/noise tapes. The finite
control contains one branch for each prescribed tape. The input-dependent
signature and the three address bases remain in registers throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

abbrev Query (u D : Nat) := SourceTape.TestTape (I u) (J u) D

variable {K Λ : Type} [DecidableEq K]

def prefixBits (u D : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u) : Nat → List Bool
  | 0 => []
  | n + 1 => prefixBits u D queries values signature n ++
      SourceTestAppend.equationBits u D values (signature, queries n)

end UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOdometerSchedule

open Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def currentAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .current ⟨i, h⟩ else .extra accumulator

def remainingAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .remaining ⟨i, h⟩ else .extra accumulator

theorem setDigits_setAcc (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc a base bits) = setAcc a (setDigits m digits base) bits := by
  funext k
  cases k <;> simp [setDigits, setAcc, Function.update_apply]

theorem putDigit_setAcc (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) (bits : List Bool) :
    putDigit i (setAcc a base bits) d r = setAcc a (putDigit i base d r) bits := by
  funext k
  cases k <;> simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
    setAcc, Function.update_apply]

/-- The low-coordinate assignment commutes with a separate higher digit. -/
theorem setDigits_putDigit (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (d r : ℕ) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d r := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | remaining i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

/-- The last coordinate is the outside loop coordinate. -/
theorem setDigits_snoc (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m (Fin.snoc digits d) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d (m - 1 - d) := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | remaining i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem setDigits_snoc_base (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d (m - 1 - d)) =
      setDigits m (Fin.snoc digits d) base := by
  rw [setDigits_putDigit, setDigits_snoc]

def blockPrefix (blocks : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => blockPrefix blocks n ++ blocks n

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

theorem blockPrefix_all {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) :
    blockPrefix (blocks bits) m = allBits bits := by
  rw [blockPrefix_eq_ofFn]
  simp only [blocks, Fin.isLt, ↓reduceDIte, allBits, tupleOrder_snoc]
  simp only [List.flatMap_assoc, List.flatMap_map]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ) (accumulator : Extra)
    {q : ℕ} (base : Tape u Extra → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc accumulator base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc accumulator base ((bits c).reverse ++ output))))

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (d : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c d i).val) =
      Fin.snoc (fun i => (c i).val) d.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ u)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical accumulator base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (.extra accumulator))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical accumulator base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt accumulator)
      (remaining := remainingAt accumulator) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical accumulator base bits) count rfl rfl hrun
    refine ⟨tree, ?_⟩
    dsimp only [tree]
    erw [NestedCycle.LeafBound]
    exact hcount
  | succ q ih =>
    have hqu : q < u := by omega
    let s : CycleSchedule (Tape u Extra) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (.extra accumulator))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base)
            (checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
              s.ambient s.register s.base), tree.LeafBound B := by
      let d : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c d)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (.extra accumulator)))
        d.val (m - 1 - d.val)
      have hrem : m - 1 - d.val = r.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = d.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = d.val + 1 := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, d.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical accumulator
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c d) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical accumulator childBase childBits =
          checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
            s.ambient s.register s.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_extra, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) s children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
        bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, s,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt accumulator q) (remainingAt accumulator q)
        (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        finalConfiguration (next (q + 1)) canonical accumulator base bits := by
      simp only [cycleExit, finalConfiguration, configuration, s, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt accumulator) (remainingAt accumulator)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
          bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (currentAt accumulator q) (remainingAt accumulator q)
          (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

/-- The time bound is derived from the concrete schedule, not from the number
of tuples alone. Dimension zero consists of its single actual body trace. -/
theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B : ℕ) (base : Tape u Extra → List Bool)
    (bits : (Fin u → Fin m) → List Bool)
    (atCheck : ∀ i, i < u → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < u → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) u bodyLabel canonical base)
      (some (finalConfiguration (next u) canonical accumulator base bits))
      ((B + 2 * u) * m ^ u)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical accumulator
    positive B u (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

end UniqueGamesTheorem.Foundations.Hastad.SourceOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Explicit.MachineProductProgram

open Turing
open UniqueGamesTheorem.Foundations
open Complexity Hastad
open UniqueGamesTheorem.Reduction.MachineTransfer


theorem initRole_injective (t : Nat) : Function.Injective (initRole t) := by
  intro a b h
  cases a <;> cases b <;> simp_all [initRole, auxiliary]

noncomputable section

def resetAt (q t i : Nat) : Label q t := if h : i < t then .reset ⟨i, h⟩ else .finishStart

end

end UniqueGamesTheorem.Explicit.MachineProductProgram

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductHeadersFrameLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Concrete header and initialized work-tape frames for the product machine. -/

namespace UniqueGamesTheorem.Explicit.MachineProductHeaders

open Turing
open UniqueGamesTheorem.Foundations Target Complexity Hastad
open MachineProductProgram


theorem power_outside (t : Nat) (edgeCount : Bool) (i : MachineHorner.Layout (t + 1)) :
    accumulator t ≠ powerSlots t edgeCount i := by
  cases i with
  | inl i => fin_cases i <;> cases edgeCount <;> simp [accumulator, powerSlots, powerRole, auxiliary]
  | inr i => simp [accumulator, powerSlots, powerRole, auxiliary, constantDigit]

theorem frame_power_clean {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) : MachineHorner.Clean (powerSlots t edgeCount) (frame H t emitted) := by
  constructor <;> simp [frame, powerSlots, powerRole, auxiliary]

theorem frame_append {q : Nat} (H : Instance q) (t : Nat) (emitted suffix : List Bool) :
    Function.update (frame H t emitted) (accumulator t)
      (suffix.reverse ++ frame H t emitted (accumulator t)) = frame H t (emitted ++ suffix) := by
  funext tape
  cases tape <;> simp [frame, accumulator, auxiliary, Function.update_apply]
  rename_i extra
  cases extra with
  | inl i =>
    fin_cases i <;> simp
  | inr i => simp

/-- The generic odometer initializer has exactly the scheduler's concrete digit
frame; all permanent headers and output-emitted bits retain their identity. -/
theorem initialized_eq {q : Nat} (H : Instance q) (t : Nat) :
    MachineOdometerInit.stageTapes (initRole t) H.constraints.length (baseTapes H t) t =
      SourceOdometerSchedule.setDigits H.constraints.length (fun _ : Fin t => 0) (baseTapes H t) := by
  funext tape
  cases tape with
  | current i =>
    have h := MachineOdometerInit.output_current (initRole t) (initRole_injective t)
      H.constraints.length (baseTapes H t) i
    simpa [initRole, SourceOdometerSchedule.setDigits, i.isLt] using h
  | remaining i =>
    have h := MachineOdometerInit.output_remaining (initRole t) (initRole_injective t)
      H.constraints.length (baseTapes H t) i
    simpa [initRole, SourceOdometerSchedule.setDigits, i.isLt] using h
  | _ =>
    rw [MachineOdometerInit.stageTapes_frame (initRole t) H.constraints.length
      (baseTapes H t) t _ (fun _ => by simp [initRole]) (fun _ => by simp [initRole])]
    rfl




/-! The three actual output-header emissions of the product controller. -/




noncomputable section

def powerExit (q t : Nat) (edgeCount : Bool) : Label q t :=
  if edgeCount then MachineOdometerInit.labelAt Label.initialize_ 0 else .alphabetHeader

def powerInTime {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) (edgeCount : Bool) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some (.power edgeCount (.inl .start)), (((), ()), none), frame H t emitted⟩
      (some ⟨some (powerExit q t edgeCount), (((), ()), none),
        frame H t (emitted ++ encodeWord
          ((if edgeCount then H.constraints.length else H.vertices) ^ t))⟩)
      (MachineProductPower.steps (if edgeCount then H.constraints.length else H.vertices) t) := by
  have trace := MachineProductPower.powerTrace (powerSlots t edgeCount) (accumulator t)
    (power_outside t edgeCount) (Label.power edgeCount) (some (powerExit q t edgeCount))
    (program q t) (by intro inner; cases edgeCount <;> rfl) (frame H t emitted)
    (if edgeCount then H.constraints.length else H.vertices)
    (frame_radix H t emitted edgeCount) (frame_digit H t emitted edgeCount)
    (frame_power_clean H t emitted edgeCount) (frame_power_output H t emitted edgeCount) () none
  rw [frame_append] at trace
  exact { steps := _, evals_in_steps := trace, steps_le_m := Nat.le_refl _ }

def alphabetInTime {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some .alphabetHeader, (((), ()), none), frame H t emitted⟩
      (some ⟨some (.power true (.inl .start)), (((), ()), none),
        frame H t (emitted ++ encodeWord (q ^ t))⟩) 1 := by
  have trace := MachineInitialHeaders.literalTrace (accumulator t) (encodeWord (q ^ t))
    (.alphabetHeader : Label q t) (some (.power true (.inl .start)))
    (program q t) rfl (frame H t emitted) ((), ()) none
  rw [frame_append] at trace
  exact { steps := 1, evals_in_steps := trace, steps_le_m := Nat.le_refl _ }

def powersInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some (.power false (.inl .start)), (((), ()), none), frame H t []⟩
      (some ⟨some (MachineOdometerInit.labelAt Label.initialize_ 0), (((), ()), none), baseTapes H t⟩)
      (MachineProductPower.steps H.vertices t + 1 + MachineProductPower.steps H.constraints.length t) := by
  have first := powerInTime H t [] false
  have second := alphabetInTime H t (encodeWord (H.vertices ^ t))
  have third := powerInTime H t (encodeWord (H.vertices ^ t) ++ encodeWord (q ^ t)) true
  simp only [Bool.false_eq_true, ↓reduceIte, powerExit, List.nil_append] at first
  simp only [↓reduceIte, powerExit] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  have finalFrame : frame H t
      ((encodeWord (H.vertices ^ t) ++ encodeWord (q ^ t)) ++
        encodeWord (H.constraints.length ^ t)) = baseTapes H t := by
    simp only [baseTapes, headerBits, encodeWords, List.append_nil, List.append_assoc]
  rw [finalFrame] at whole
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have h := whole.steps_le_m; omega }

end
end UniqueGamesTheorem.Explicit.MachineProductHeaders



/-! Three actual header reads for the fixed-alphabet, fixed-power product
machine. The constraint table stays in its original order on the formula tape. -/

namespace UniqueGamesTheorem.Explicit.MachineProductHeadersRead


open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineProductProgram

noncomputable section

def inputTapes (t : Nat) (bits : List Bool) : Tape t → List Bool
  | .formula => bits
  | _ => []

def afterVertices (t n : Nat) (rest : List Bool) : Tape t → List Bool
  | .formula => rest
  | .extra (.inl i) => if i = 0 then encodeWord n else []
  | _ => []

def afterAlphabet (t n q : Nat) (rest : List Bool) : Tape t → List Bool
  | .formula => rest
  | .extra (.inl i) => if i = 0 then encodeWord n else if i = 7 then encodeWord q else []
  | _ => []

def rawResultTapes (t n q m : Nat) (body : List Bool) : Tape t → List Bool
  | .formula => body
  | .extra (.inl i) => if i = 0 then encodeWord n else if i = 7 then encodeWord q
      else if i = 8 then encodeWord m else []
  | _ => []

def resultTapes {q : Nat} (H : Target.Instance q) (t : Nat) : Tape t → List Bool
  | .formula => encodeWords (ProductMachineSemantics.inputTable H)
  | .extra (.inl i) => if i = 0 then encodeWord H.vertices else if i = 7 then encodeWord q
      else if i = 8 then encodeWord H.constraints.length else []
  | _ => []

theorem initList_eq (q t : Nat) (bits : List Bool) :
    initList (machine q t) bits =
      ⟨some (.headerStart 0), (((), ()), none), inputTapes t bits⟩ := by
  unfold initList
  congr 1
  funext k
  (cases k <;> simp [inputTapes, machine]); rfl

theorem first_result (t n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 0)
      (inputTapes t (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes t (encodeWord n ++ rest) (auxiliary t 0)) =
      afterVertices t n rest := by
  funext k
  cases k with
  | extra x =>
    cases x with
    | inl i => fin_cases i <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices, auxiliary]
    | inr i => simp [SourceMachine.fieldTapes, inputTapes, afterVertices, auxiliary]
  | _ => simp [SourceMachine.fieldTapes, inputTapes, afterVertices, auxiliary]

theorem second_result (t n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 7)
      (afterVertices t n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices t n (encodeWord q ++ rest) (auxiliary t 7)) =
      afterAlphabet t n q rest := by
  funext k
  cases k with
  | extra x =>
    cases x with
    | inl i => fin_cases i <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet, auxiliary]
    | inr i => simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet, auxiliary]
  | _ => simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet, auxiliary]

theorem third_result (t n q m : Nat) (body : List Bool) :
    SourceMachine.fieldTapes (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 8)
      (afterAlphabet t n q (encodeWord m ++ body)) body
      (encodeWord m ++ afterAlphabet t n q (encodeWord m ++ body) (auxiliary t 8)) =
      rawResultTapes t n q m body := by
  funext k
  cases k with
  | extra x =>
    cases x with
    | inl i => fin_cases i <;> simp [SourceMachine.fieldTapes, afterAlphabet, rawResultTapes, auxiliary]
    | inr i => simp [SourceMachine.fieldTapes, afterAlphabet, rawResultTapes, auxiliary]
  | _ => simp [SourceMachine.fieldTapes, afterAlphabet, rawResultTapes, auxiliary]

def rawHeadersInTime (q t n m : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (encodeWords [n, q, m] ++ body))
      (some ⟨some .seedStart, (((), ()), none), rawResultTapes t n q m body⟩)
      (n + q + m + 6) := by
  have first := SourceMachine.fieldInTime
    (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 0) (by simp [auxiliary])
    (.headerStart 0 : Label q t) (.headerRead 0) (some (.headerStart 1))
    (program q t) rfl rfl
    (inputTapes t (encodeWord n ++ (encodeWord q ++ (encodeWord m ++ body)))) n
    (encodeWord q ++ (encodeWord m ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime
    (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 7) (by simp [auxiliary])
    (.headerStart 1 : Label q t) (.headerRead 1) (some (.headerStart 2))
    (program q t) rfl rfl (afterVertices t n (encodeWord q ++ (encodeWord m ++ body))) q
    (encodeWord m ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime
    (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 8) (by simp [auxiliary])
    (.headerStart 2 : Label q t) (.headerRead 2) (some .seedStart)
    (program q t) rfl rfl (afterAlphabet t n q (encodeWord m ++ body)) m body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  have timed : StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some (.headerStart 0), (((), ()), none),
        inputTapes t (encodeWord n ++ (encodeWord q ++ (encodeWord m ++ body)))⟩
      (some ⟨some .seedStart, (((), ()), none), rawResultTapes t n q m body⟩)
      (n + q + m + 6) := {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have bound := whole.steps_le_m; omega
  }
  simpa only [FinTM2.step, FinTM2.Cfg, machine, encodeWords,
    List.nil_append, List.append_assoc] using! timed

/-- The exact runtime machine starts on the complete ordinary target game codec
and reaches the seed phase with its untouched row table and three unary headers. -/
def headersInTime {q : Nat} (H : Target.Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some ⟨some .seedStart, (((), ()), none), resultTapes H t⟩)
      (H.vertices + q + H.constraints.length + 6) := by
  have input : gameBits H = encodeWords [H.vertices, q, H.constraints.length] ++
      encodeWords (ProductMachineSemantics.inputTable H) := by
    simp only [gameBits, gameWords, ProductMachineSemantics.inputTable, encodeWords_append]
  have result : rawResultTapes t H.vertices q H.constraints.length
      (encodeWords (ProductMachineSemantics.inputTable H)) = resultTapes H t := rfl
  rw [input]
  simpa only [result] using rawHeadersInTime q t H.vertices H.constraints.length
    (encodeWords (ProductMachineSemantics.inputTable H))

theorem headers_budget {q : Nat} (H : Target.Instance q) (_power : Nat) :
    H.vertices + q + H.constraints.length + 6 ≤ (gameBits H).length + 3 := by
  simp [gameBits, gameWords, List.length_append, encodeWords]
  omega

end
end UniqueGamesTheorem.Explicit.MachineProductHeadersRead



/-! Actual literal initialization of the finitely many product power digits. -/

namespace UniqueGamesTheorem.Explicit.MachineProductHeaders

open Turing
open UniqueGamesTheorem.Foundations Target Complexity Hastad
open MachineProductProgram


noncomputable section

theorem seedCommands_nodup (t : Nat) : ((seedCommands t).map Prod.fst).Nodup := by
  simp only [seedCommands, List.map_ofFn, Function.comp_def]
  apply List.nodup_ofFn.mpr
  intro i j same
  simpa [constantDigit] using same

theorem seed_result {q : Nat} (H : Instance q) (t : Nat) :
    MachineProductSeed.finalTapes (seedCommands t)
      (MachineProductHeadersRead.resultTapes H t) = frame H t [] := by
  have unchanged (tape : Tape t) (outside : ∀ i, tape ≠ constantDigit t i) :
      MachineProductSeed.finalTapes (seedCommands t)
        (MachineProductHeadersRead.resultTapes H t) tape =
        MachineProductHeadersRead.resultTapes H t tape := by
    apply MachineProductSeed.finalTapes_frame
    intro command member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact outside i
  funext tape
  cases tape with
  | extra extra =>
    cases extra with
    | inl i =>
      rw [unchanged _ (by intro j; simp [constantDigit])]
      fin_cases i <;> simp [MachineProductHeadersRead.resultTapes, frame]
    | inr i =>
      have run := MachineProductSeed.finalTapes_field (seedCommands t) (seedCommands_nodup t)
        (MachineProductHeadersRead.resultTapes H t)
        (constantDigit t i, encodeWord (MachineProductPower.digits i.val))
        (by apply List.mem_ofFn.mpr; exact ⟨i, rfl⟩)
      simpa [constantDigit, MachineProductHeadersRead.resultTapes, frame] using run
  | _ =>
    rw [unchanged _ (by intro j; simp [constantDigit])]
    rfl

def seedBridge {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some .seedStart, (((), ()), none), MachineProductHeadersRead.resultTapes H t⟩
      (some ⟨MachineProductSeed.entry (seedCommands t) Label.seed
        (some (.power false (.inl .start))), (((), ()), none),
        MachineProductHeadersRead.resultTapes H t⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q t .seedStart) _ _) = _
    simp only [program]
    cases h : MachineProductSeed.entry (seedCommands t) (Label.seed (q := q))
      (some (.power false (.inl .start))) <;>
      simp only [Reduction.MachineTransfer.exitAt, TM2.stepAux] <;> erw [h] <;> rfl
  steps_le_m := Nat.le_refl _

def seedInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some .seedStart, (((), ()), none), MachineProductHeadersRead.resultTapes H t⟩
      (some ⟨some (.power false (.inl .start)), (((), ()), none), frame H t []⟩)
      (t + 2) := by
  have trace := MachineProductSeed.seedTrace (seedCommands t) (Label.seed (q := q))
    (some (.power false (.inl .start))) (program q t) (fun _ => rfl)
    (MachineProductHeadersRead.resultTapes H t) ((), ()) none
  rw [seed_result] at trace
  have seed : StateTransition.EvalsToInTime (machine q t).step
      ⟨MachineProductSeed.entry (seedCommands t) Label.seed
        (some (.power false (.inl .start))), (((), ()), none),
        MachineProductHeadersRead.resultTapes H t⟩
      (some ⟨some (.power false (.inl .start)), (((), ()), none), frame H t []⟩)
      (t + 1) := {
    steps := (seedCommands t).length
    evals_in_steps := trace
    steps_le_m := by simp [seedCommands] }
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ (seedBridge H t) seed
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have h := whole.steps_le_m; omega }




/-! Complete actual initialization of the independent-product machine. -/





def initializeInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some (MachineOdometerInit.labelAt Label.initialize_ 0), (((), ()), none), baseTapes H t⟩
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t)))
      (t * (2 * H.constraints.length + 6) + 1) := by
  have run := MachineOdometerInit.initializeInTime (initRole t) (initRole_injective t)
    Label.initialize_ (some (rowMain q t)) (program q t) (fun _ => rfl)
    H.constraints.length H.constraintCount_positive (baseTapes H t)
    (by simp [baseTapes, frame, initRole, auxiliary])
    (by intro j; rfl) (by intro j; rfl) rfl ((), ())
  rw [initialized_eq] at run
  exact run

def steps {q : Nat} (H : Instance q) (t : Nat) : Nat :=
  H.vertices + q + H.constraints.length + 6 + (t + 2) +
    (MachineProductPower.steps H.vertices t + 1 + MachineProductPower.steps H.constraints.length t) +
    (t * (2 * H.constraints.length + 6) + 1)

/-- Header reading, literal seed setup, actual Horner power computation, and
all odometer digits are supplied by real execution traces of the same program. -/
def prepareInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t))) (steps H t) := by
  have headers := MachineProductHeadersRead.headersInTime H t
  have seeds := seedInTime H t
  have powers := powersInTime H t
  have initialized := initializeInTime H t
  have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ headers seeds
  have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first powers
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second initialized
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have h := whole.steps_le_m; unfold steps; omega }

theorem steps_le {q : Nat} (H : Instance q) (t : Nat) :
    steps H t ≤ (timePolynomial t).eval (gameBits H).length := by
  have headerBound := MachineProductHeadersRead.headers_budget H t
  have hn : H.vertices ≤ (gameBits H).length + 1 := by omega
  have hm : H.constraints.length ≤ (gameBits H).length + 1 := by omega
  have hm' : H.constraints.length ≤ (gameBits H).length := by omega
  have first := MachineProductPower.steps_le H.vertices t ((gameBits H).length + 1) hn (by omega)
  have second := MachineProductPower.steps_le H.constraints.length t ((gameBits H).length + 1) hm (by omega)
  have initialization := Nat.mul_le_mul_left t (show 2 * H.constraints.length + 6 ≤
      2 * (gameBits H).length + 6 by omega)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold steps
  omega

/-- Polynomial initialization in the literal incoming instance-code length. -/
def inPolynomialTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t)))
      ((timePolynomial t).eval (gameBits H).length) :=
  { toEvalsTo := (prepareInTime H t).toEvalsTo
    steps_le_m := (prepareInTime H t).steps_le_m.trans (steps_le H t) }

end
end UniqueGamesTheorem.Explicit.MachineProductHeaders



/-! Whole tuple traversal of the concrete product program. The odometer theorem
is instantiated by the proved actual row trace, not by an assumed row machine. -/

namespace UniqueGamesTheorem.Explicit.MachineProductLoop

open Turing
open UniqueGamesTheorem.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram


variable {q t : Nat}

noncomputable section

structure BaseReady (H : Target.Instance q) (base : Tape t → List Bool) : Prop where
  work : ∀ b, MachineProductField.Ready (MachineProductRow.fieldSlots (rowSlots t) b) base
  table : base .formula = encodeWords (ProductMachineSemantics.inputTable H)
  vertices : base (auxiliary t 0) = encodeWord H.vertices
  alphabet : base (auxiliary t 7) = encodeWord q

theorem tupleTapes_frame (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) (k : Tape t)
    (hc : ∀ i, k ≠ .current i) (hr : ∀ i, k ≠ .remaining i)
    (ha : k ≠ accumulator t) : tupleTapes H base edges out k = base k := by
  cases k with
  | current i => exact (hc i rfl).elim
  | remaining i => exact (hr i rfl).elim
  | extra x =>
    simp only [tupleTapes, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]
    exact Function.update_of_ne ha _ _
  | _ => simp [tupleTapes, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]

theorem tupleTapes_ready (H : Target.Instance q) (base : Tape t → List Bool)
    (ready : BaseReady H base) (edges : Fin t → Fin H.constraints.length) (out : List Bool) :
    MachineProductRow.Ready (rowSlots t) (ProductMachineSemantics.inputTable H)
      (fun i => (edges i).val) (fun b => if b then q else H.vertices) (tupleTapes H base edges out) := by
  have other (k : Tape t) (hc : ∀ i, k ≠ .current i) (hr : ∀ i, k ≠ .remaining i)
      (ha : k ≠ accumulator t) := tupleTapes_frame H base edges out k hc hr ha
  constructor
  · intro b
    have work := ready.work b
    constructor
    · change tupleTapes H base edges out .index = []
      rw [other .index (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.query
    · change tupleTapes H base edges out .work = []
      rw [other .work (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.scan
    · change tupleTapes H base edges out .scratch = []
      rw [other .scratch (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.gatherScratch
    · intro i
      change tupleTapes H base edges out (.field i 0) = []
      rw [other (.field i 0) (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.fields i
    · change tupleTapes H base edges out (auxiliary t 1) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.accA
    · change tupleTapes H base edges out (auxiliary t 2) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.accB
    · change tupleTapes H base edges out (auxiliary t 3) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.counter
    · change tupleTapes H base edges out (auxiliary t 4) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.hornerScratch
    · change tupleTapes H base edges out (auxiliary t 5) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.output
  · change tupleTapes H base edges out .formula = _
    rw [other .formula (by simp) (by simp) (by simp [accumulator, auxiliary])]
    exact ready.table
  · intro i; exact tupleTapes_current H base edges out i
  · intro b
    cases b
    · change tupleTapes H base edges out (auxiliary t 0) = _
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact ready.vertices
    · change tupleTapes H base edges out (auxiliary t 7) = _
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact ready.alphabet

theorem input_length (H : Target.Instance q) :
    (gameBits H).length = H.vertices + q + H.constraints.length + 3 +
      (encodeWords (ProductMachineSemantics.inputTable H)).length := by
  simp [gameBits, gameWords, ProductMachineSemantics.inputTable,
    encodeWords, encodeWord_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

def bodyBound (H : Target.Instance q) (t : Nat) : Nat :=
  (q ^ t + 2) * (MachineProductBounds.fieldPolynomial t).eval (gameBits H).length

/-- The actual row execution supplies the local obligation of the generic
odometer schedule. Its cost is uniformly polynomial in the original bits. -/
theorem bodyTrace (H : Target.Instance q) (base : Tape t → List Bool) (ready : BaseReady H base) :
    SourceOdometerSchedule.BodyTrace (program q t) (rowMain q t) (nextCheck q t 0)
      ((), ()) (Sum.inl (6 : Fin 10)) base (rowBits (t := t) H) (bodyBound H t) := by
  intro edges out
  let indices := fun i => (edges i).val
  let radices := fun b : Bool => if b then q else H.vertices
  let fields := ProductMachineSemantics.fields H edges
  let digits := fun c => ProductMachineSemantics.reverseDigits (fields c)
  let frame := tupleTapes H base edges out
  have hready := tupleTapes_ready H base ready edges out
  have selected := ProductMachineSemantics.selected H edges
  have reversed : ∀ c ∈ ProductMachineSemantics.commands q t, ∀ i : Fin t,
      digits c i.val = fields c i.rev := by
    intro c hc i
    exact ProductMachineSemantics.reverseDigits_at _ _
  have run := MachineProductRow.rowTrace (rowSlots t) (ProductMachineSemantics.inputTable H)
    (q + 2) indices radices (ProductMachineSemantics.commands q t) fields digits selected reversed
    Label.row (some (nextCheck q t 0)) (program q t) (fun _ => rfl) frame hready ()
  have len := input_length H
  have tableBound : (encodeWords (ProductMachineSemantics.inputTable H)).length ≤ (gameBits H).length := by omega
  have indexBound (i : Fin t) : indices i ≤ (gameBits H).length := by
    have h := (edges i).isLt; dsimp [indices]; omega
  have radixBound (b : Bool) : radices b ≤ (gameBits H).length := by
    cases b <;> dsimp [radices] <;> omega
  have digitBound (c : MachineProductRow.Command t) (hc : c ∈ ProductMachineSemantics.commands q t)
      (i : Nat) (hi : i < t) : digits c i ≤ (gameBits H).length := by
    rw [show digits c i = fields c (Fin.rev ⟨i, hi⟩) from
      ProductMachineSemantics.reverseDigits_at _ ⟨i, hi⟩]
    have h := ProductMachineSemantics.fields_lt H edges c hc (Fin.rev ⟨i, hi⟩)
    have hr := radixBound c.1
    dsimp [radices, fields] at hr ⊢
    omega
  have bound := MachineProductBounds.row_steps_le (rowSlots t) (ProductMachineSemantics.inputTable H)
    (q + 2) indices radices (ProductMachineSemantics.commands q t) fields digits selected
    frame hready (gameBits H).length tableBound indexBound radixBound digitBound
  rw [ProductMachineSemantics.commands_length] at bound
  refine ⟨_, bound, ?_⟩
  have hframe : Function.update frame (MachineProductRow.outputTape (rowSlots t))
      ((rowBits H edges).reverse ++ frame (MachineProductRow.outputTape (rowSlots t))) =
      tupleTapes H base edges ((rowBits H edges).reverse ++ out) := by
    change Function.update frame (accumulator t)
      ((rowBits H edges).reverse ++ frame (accumulator t)) = _
    rw [show frame (accumulator t) = out from tupleTapes_accumulator H base edges out]
    simp only [frame, tupleTapes, SourceOdometerSchedule.setDigits_setAcc]
    simp [SourceOdometerSchedule.setAcc, accumulator, auxiliary]
  dsimp only at run
  change _ = some (⟨some (nextCheck q t 0), (((), ()), none),
    Function.update frame (MachineProductRow.outputTape (rowSlots t))
      ((rowBits H edges).reverse ++ frame (MachineProductRow.outputTape (rowSlots t)))⟩ : (machine q t).Cfg) at run
  erw [hframe] at run
  exact run

/-- Complete positive-radix tuple traversal with actual row bodies discharged. -/
theorem traversalInTime (H : Target.Instance q) (base : Tape t → List Bool) (ready : BaseReady H base) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (program q t))
      (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length) t (rowMain q t) ((), ()) base)
      (some (SourceOdometerSchedule.finalConfiguration (nextCheck q t t) ((), ())
        (Sum.inl (6 : Fin 10)) base (rowBits (t := t) H)))
      ((bodyBound H t + 2 * t) * H.constraints.length ^ t)) := by
  apply SourceOdometerSchedule.traversalInTime (program q t) (rowMain q t)
    (nextCheck q t) (resetAt q t) ((), ()) (Sum.inl (6 : Fin 10))
    (List.length_pos_iff.mpr H.nonempty) (bodyBound H t) base (rowBits (t := t) H)
  · intro i hi
    simp [nextCheck, resetAt, hi, program, SourceOdometerSchedule.currentAt,
      SourceOdometerSchedule.remainingAt]
  · intro i hi
    simp [nextCheck, resetAt, hi, program, SourceOdometerSchedule.currentAt,
      SourceOdometerSchedule.remainingAt]
  · exact bodyTrace H base ready

end

end UniqueGamesTheorem.Explicit.MachineProductLoop



/-! Exact final cleanup and binary-output identification for the product
controller. The final runtime bound is derived from actual stack lengths. -/

namespace UniqueGamesTheorem.Explicit.MachineProductFinish

open Turing
open UniqueGamesTheorem.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram


variable {q t : Nat}

noncomputable section

theorem base_ready (H : Target.Instance q) (t : Nat) :
    MachineProductLoop.BaseReady H (MachineProductHeaders.baseTapes H t) := by
  constructor
  · intro b
    constructor <;> simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame,
      MachineProductRow.fieldSlots, MachineProductRow.fieldRole, rowSlots] <;> (intros; rfl)
  · rfl
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]

theorem afterRows_output (H : Target.Instance q) (t : Nat) :
    (afterRows H t).stk (output t) = [] := by
  simp [afterRows, SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration,
    SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc, output, auxiliary,
    MachineProductHeaders.baseTapes, MachineProductHeaders.frame]
  rfl

theorem afterRows_accumulator (H : Target.Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    ((afterRows H t).stk (accumulator t)).reverse =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  change ((SourceOdometerSchedule.allBits (MachineProductLoop.rowBits (t := t) H)).reverse ++
    MachineProductHeaders.baseTapes H t (accumulator t)).reverse = _
  rw [MachineProductHeaders.baseTapes, MachineProductHeaders.frame_accumulator,
    List.reverse_append, List.reverse_reverse, List.reverse_reverse]
  rw [SourceOdometerSchedule.allBits, allRows_eq]
  exact ProductMachineSemantics.gameBits_eq H presentation t ht

/-- The entry hop reaches the actual cleanup list, then all work is drained,
the accumulator is reversed, and the final finite register is reset. -/
def finishInTime (base : Tape t → List Bool) (emptyOutput : base (output t) = []) :
    StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some .finishStart, (((), ()), none), base⟩
      (some ⟨none, (((), ()), none),
        SourceRuntimeFinish.canonicalTapes (output t) (base (accumulator t)).reverse⟩)
      (1 + SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) base) := by
  have enter : StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some .finishStart, (((), ()), none), base⟩
      (some ⟨SourceRuntimeFinish.entry (clearKeys t) Label.finish, (((), ()), none), base⟩) 1 := by
    refine ⟨⟨1, ?_⟩, Nat.le_refl _⟩
    change some (TM2.stepAux (program q t .finishStart) _ _) = _
    simp only [program, UniqueGamesTheorem.Reduction.MachineTransfer.exitAt]
    split <;> simp_all [TM2.stepAux]
  have finish := SourceRuntimeFinish.finishInTime (clearKeys t) (accumulator t) (output t)
    (by simp [accumulator, output, auxiliary])
    (by simp) (by simp) (by intro k h1 h2; simp [h1, h2])
    ((), ()) Label.finish none (program q t) (fun _ => rfl) base emptyOutput ((), ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ enter finish
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := by simpa only [Nat.add_comm] using joined.steps_le_m }

theorem finish_afterRows (H : Target.Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    Nonempty (StateTransition.EvalsToInTime (machine q t).step (afterRows H t)
      (some (haltList (machine q t) (gameBits (ProductPaddedOutput.output H presentation t ht))))
      (1 + SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) (afterRows H t).stk)) := by
  have run := finishInTime (q := q) (afterRows H t).stk (afterRows_output H t)
  erw [afterRows_accumulator H presentation t ht] at run
  have hstart : (afterRows H t).l = some .finishStart := by simp [afterRows,
    SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration, nextCheck]
  have hstate : (afterRows H t).var = (((), ()), none) := rfl
  have halt : (⟨none, (((), ()), none), SourceRuntimeFinish.canonicalTapes (output t)
      (gameBits (ProductPaddedOutput.output H presentation t ht))⟩ : (machine q t).Cfg) =
      haltList (machine q t) (gameBits (ProductPaddedOutput.output H presentation t ht)) := by
    unfold haltList SourceRuntimeFinish.canonicalTapes
    congr 1
    funext k
    by_cases hk : k = output t
    · subst k
      simp only [machine]
      erw [Function.update_self]
      rfl
    · simp only [machine]
      erw [Function.update_of_ne hk, dite_eq_right hk]
  erw [halt] at run
  have hcfg : (⟨some .finishStart, (((), ()), none), (afterRows H t).stk⟩ : (machine q t).Cfg) =
      afterRows H t := by cases h : afterRows H t; simp_all
  erw [hcfg] at run
  exact ⟨run⟩

end

end UniqueGamesTheorem.Explicit.MachineProductFinish

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! The complete explicit product computation. Every execution phase is supplied
by the actual controller; the cleanup bound follows from the space reached by
its actual prefix. The exponent and alphabet enter only the fixed program. -/

namespace UniqueGamesTheorem.Explicit.MachineProductRuntime

open Turing
open UniqueGamesTheorem.Foundations Target Complexity Hastad
open MachineProductProgram


noncomputable section

theorem loop_budget {q : Nat} (H : Instance q) (t : Nat) :
    (MachineProductLoop.bodyBound H t + 2 * t) * H.constraints.length ^ t ≤
      (loopPolynomial q t).eval (gameBits H).length := by
  have hlen := MachineProductLoop.input_length H
  have hm : H.constraints.length ≤ (gameBits H).length := by omega
  simp only [loopPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm t)

/-- Actual header initialization followed by every product row and odometer step. -/
def prefixInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (MachineProductFinish.afterRows H t))
      ((prefixPolynomial q t).eval (gameBits H).length) := by
  let first := MachineProductHeaders.inPolynomialTime H t
  let loop := Classical.choice (MachineProductLoop.traversalInTime H
    (MachineProductHeaders.baseTapes H t) (MachineProductFinish.base_ready H t))
  let second : StateTransition.EvalsToInTime (machine q t).step
      (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (MachineProductHeaders.baseTapes H t))
      (some (MachineProductFinish.afterRows H t))
      ((loopPolynomial q t).eval (gameBits H).length) := {
    toEvalsTo := loop.toEvalsTo
    steps_le_m := loop.steps_le_m.trans (loop_budget H t) }
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  exact {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm]
        using joined.steps_le_m }

def timePolynomial (q t : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q t) (clearKeys t).length
    (prefixPolynomial q t) + 1

/-- The complete run produces the literal full-table target code, clears all
private stacks, resets its finite state, and halts. -/
def outputInTime {q : Nat} (H : Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    TM2OutputsInTime (machine q t) (gameBits H)
      (some (gameBits (ProductPaddedOutput.output H presentation t ht)))
      ((timePolynomial q t).eval (gameBits H).length) := by
  let initialRun := prefixInTime H t
  let finish := Classical.choice (MachineProductFinish.finish_afterRows H presentation t ht)
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initialRun finish
  have keepAccumulator : accumulator t ∉ clearKeys t := by simp
  have keepOutput : output t ∉ clearKeys t := by simp
  have covers (k : Tape t) (ha : k ≠ accumulator t) (ho : k ≠ output t) :
      k ∈ clearKeys t := (mem_clearKeys t k).mpr ⟨ha, ho⟩
  have bound : SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t)
      (MachineProductFinish.afterRows H t).stk ≤ (gameBits H).length +
        (prefixPolynomial q t).eval (gameBits H).length *
          (@Fintype.card (machine q t).K (machine q t).kFin * Runtime.programPushBound (machine q t)) +
        (clearKeys t).length + 2 :=
    SourceRuntimeSpace.finishCost_le_of_prefix (machine q t) (gameBits H)
    initialRun (clearKeys t) (accumulator t) (output t)
    keepAccumulator keepOutput covers
    (MachineProductFinish.afterRows H t).stk (MachineProductFinish.afterRows_output H t)
    (fun _ => rfl)
  change StateTransition.EvalsToInTime (machine q t).step _
    (some (haltList (machine q t) _)) _
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one,
    SourceRuntimeSpace.completedTime_eval]
  omega

/-- The bipartition is proof-side data. Its codec is exactly the underlying
instance code and the fixed program does not inspect it. -/
abbrev Input (q : Nat) := Σ H : Instance q, MachineOutputContract.SimpleBipartite H

def construct {q : Nat} (t : Nat) (ht : 0 < t) (H : Input q) : Instance (q ^ t) :=
  ProductPaddedOutput.output H.1 H.2 t ht

def computation (q t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime (fun H : Input q => gameBits H.1) gameBits
      (construct t ht) where
  tm := machine q t
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q t
  outputsFun H := by
    change TM2OutputsInTime (machine q t) ((gameBits H.1).map id)
      (some ((gameBits (construct t ht H)).map id)) _
    have input_eq :
        @List.map ((machine q t).Γ (machine q t).k₀)
          ((machine q t).Γ (machine q t).k₀) id (gameBits H.1) = gameBits H.1 := List.map_id _
    have output_eq :
        @List.map ((machine q t).Γ (machine q t).k₁)
          ((machine q t).Γ (machine q t).k₁) id (gameBits (construct t ht H)) =
          gameBits (construct t ht H) := List.map_id _
    simpa only [input_eq, output_eq] using! outputInTime H.1 H.2 t ht

theorem finiteAlphabet (q t : Nat) (ht : 0 < t) :
    MachineFiniteAlphabet.FiniteAlphabet (computation q t ht).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

variable {A : Type} {q : Nat} {encode : A → List Bool} {f : A → Instance q}

def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a)) :
    TM2ComputableInPolyTime encode (fun H : Input q => gameBits H.1)
      (fun a => ⟨f a, presentation a⟩) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

/-- Direct composition with an actual preceding simple-bipartite producer. -/
def compose (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime encode gameBits
      (fun a => ProductPaddedOutput.output (f a) (presentation a) t ht) :=
  MachineSequential.composeBits (certify upstream presentation) (computation q t ht)

theorem compose_finiteAlphabet (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) (finite : MachineFiniteAlphabet.FiniteAlphabet upstream.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (compose upstream presentation t ht).tm :=
  MachineFiniteAlphabet.composeBits (certify upstream presentation) (computation q t ht)
    finite (finiteAlphabet q t ht)

end

end UniqueGamesTheorem.Explicit.MachineProductRuntime

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

namespace Header

def tableTape : Tape := .inl (.inner .table)

end Header

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSingleOrbitProgramLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Physical postprocessing of the two-side address codec. The program reads
`2*C,q,m`, writes `C,q,m`, and replaces each row `u,C+v,table` by `u,v,table`.
Only the fixed alphabet size `q` occurs in finite control. All input-dependent
integers reside on unary tapes. Six Bool tapes suffice.
-/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitProgram

open Turing
open UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction

def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .start => .push .capacity (fun _ => false)
      (.push .remaining (fun _ => false) (.goto fun _ => .halfFirst))
  | .halfFirst => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.goto fun _ => .halfSecond)
        (.push .accumulator (fun _ => false)
          (.load (fun _ => initialState) (.goto fun _ => .alphabet))))
  | .halfSecond => .pop .input (fun state _ => state)
      (.push .capacity (fun _ => true)
        (.push .accumulator (fun _ => true) (.goto fun _ => .halfFirst)))
  | .alphabet => copyField .alphabet .count
  | .count => .pop .input (fun state head => (state.1, head))
      (.push .accumulator (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (.push .remaining (fun _ => true) (.goto fun _ => .count))
          (.load (fun _ => initialState) (.goto fun _ => .guard))))
  | .guard => MachineUnaryCounter.guard .remaining .source .finishStart
  | .source => copyField .source .subtract
  | .subtract => .peek .capacity (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.pop .capacity (fun state _ => state)
          (.pop .input (fun state _ => state)
            (.push .saved (fun _ => true) (.goto fun _ => .subtract))))
        (.load (fun _ => initialState) (.goto fun _ => .restore)))
  | .restore => MachineTransfer.loopAt .saved .capacity id false .restore (some .target)
  | .target => copyField .target (.table 0)
  | .table completed =>
      if h : completed.val < q then
        copyField (.table completed) (.table ⟨completed.val + 1, by omega⟩)
      else .load (fun _ => initialState) (.goto fun _ => .guard)
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      () Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .start
  σ := State
  initialState := initialState
  m := program q

end UniqueGamesTheorem.Explicit.MachineSingleOrbitProgram

/-! Exact streaming traces in the single-orbit postprocessor. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitStreams

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram

theorem copyStep_true {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (true :: i) c s r a o) =
      some (cfg loopLabel (some true) i c s r (true :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg]

theorem copyStep_false {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (false :: i) c s r a o) =
      some (cfg exitLabel none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg, initialState]

/-- The physical field copy takes one transition for each input bit. -/
theorem copyFieldTrace {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (n : Nat) (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg loopLabel register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg exitLabel none suffix c s r ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing a register with
  | zero =>
    simpa [encodeWord] using copyStep_false loopLabel exitLabel atLoop suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some,
      copyStep_true loopLabel exitLabel atLoop, ih]
    congr 2
    simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

/-- All permutation fields are copied with a finite delimiter counter. -/
theorem tableTrace {q : Nat} (completed : Fin (q + 1)) (words : List Nat)
    (hcount : completed.val + words.length = q)
    (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some (cfg (.table completed) register (encodeWords words ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s r ((encodeWords words).reverse ++ a) o) := by
  induction words generalizing completed a register with
  | nil =>
    have hc : ¬ completed.val < q := by simp only [List.length_nil] at hcount; omega
    change some (TM2.stepAux (program q (.table completed)) _ _) = _
    simp [program, hc, TM2.stepAux, cfg, initialState, encodeWords]
  | cons n words ih =>
    have hc : completed.val < q := by simp only [List.length_cons] at hcount; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at hcount
      dsimp [next]
      omega
    have hp : program q (.table completed) = copyField (.table completed) (.table next) := by
      simp [program, hc, next]
    have first := copyFieldTrace (.table completed) (.table next) hp n
      (encodeWords words ++ suffix) c s r a o register
    have rest := ih next hn ((encodeWord n).reverse ++ a) none
    have ht : (encodeWords (n :: words)).length + 1 =
        ((encodeWords words).length + 1) + (n + 1) := by
      simp only [encodeWords, List.length_append, encodeWord_length]
      omega
    rw [ht, Function.iterate_add_apply]
    simp only [encodeWords, List.append_assoc]
    rw [first, rest]
    simp only [List.reverse_append, List.append_assoc]

end UniqueGamesTheorem.Explicit.MachineSingleOrbitStreams

/-! Physical unary header conversion, with an exact TM2 transition count. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitHeader

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem halfStep_first {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (true :: i) c s r a o) =
      some (cfg .halfSecond (some true) i c s r a o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_second {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfSecond register (true :: i) c s r a o) =
      some (cfg .halfFirst register i (true :: c) s r (true :: a) o) := by
  change some (TM2.stepAux (program q .halfSecond) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (false :: i) c s r a o) =
      some (cfg .alphabet none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

/-- Consume two unary input marks per output mark, storing the new capacity. -/
theorem halfTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * n + 1]
      (some (cfg .halfFirst register (encodeWord (2 * n) ++ suffix) c s r a o)) =
      some (cfg .alphabet none suffix (List.replicate n true ++ c) s r
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing c a register with
  | zero =>
    simpa [encodeWord] using halfStep_false suffix c s r a o register
  | succ n ih =>
    have ht : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by omega
    have hw : encodeWord (2 * (n + 1)) ++ suffix =
        true :: true :: (encodeWord (2 * n) ++ suffix) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, ht, Function.iterate_succ_apply, advance_some, halfStep_first,
      Function.iterate_succ_apply, advance_some, halfStep_second, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem countStep_true {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (true :: i) c s r a o) =
      some (cfg .count (some true) i c s (true :: r) (true :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem countStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (false :: i) c s r a o) =
      some (cfg .guard none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

/-- Copy the occurrence count while also storing its physical unary counter. -/
theorem countTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .count register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s (List.replicate n true ++ r)
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing r a register with
  | zero =>
    simpa [encodeWord] using countStep_false suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some, countStep_true, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem initial_configuration (q : Nat) (input : List Bool) :
    initList (machine q) input = cfg .start none input [] [] [] [] [] := by
  have ht : (initList (machine q) input).stk = tapes input [] [] [] [] [] := by
    funext t
    (cases t <;> simp [initList, machine, tapes]); rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem initialStep (q : Nat) (input : List Bool) :
    TM2.step (program q) (initList (machine q) input) =
      some (cfg .halfFirst none input [false] [] [false] [] []) := by
  rw [initial_configuration]
  change some (TM2.stepAux (program q .start) _ _) = _
  simp [program, TM2.stepAux, cfg]

/-- Read `2*C,q,m`, write `C,q,m`, and leave the physical unary capacity and
occurrence counters ready for the row loop.  The bound counts real transitions. -/
theorem headerTrace (q C m : Nat) (suffix : List Bool) :
    (advance (TM2.step (program q)))^[2 * C + q + m + 4]
      (some (initList (machine q)
        (encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix))) =
      some (cfg .guard none suffix (encodeWord C) [] (encodeWord m)
        (encodeWords [C, q, m]).reverse []) := by
  let input := encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix
  have hfirst :
      (advance (TM2.step (program q)))^[(2 * C + 1) + 1]
        (some (initList (machine q) input)) =
        some (cfg .alphabet none (encodeWord q ++ encodeWord m ++ suffix)
          (encodeWord C) [] [false] (encodeWord C).reverse []) := by
    rw [Function.iterate_add_apply _ (2 * C + 1) 1, Function.iterate_one]
    erw [advance_some, initialStep]
    simpa only [input, encodeWord, List.append_nil, List.append_assoc] using
      halfTrace (q := q) C (encodeWord q ++ encodeWord m ++ suffix)
        [false] [] [false] [] [] none
  have hsecond :
      (advance (TM2.step (program q)))^[(q + 1) + ((2 * C + 1) + 1)]
        (some (initList (machine q) input)) =
        some (cfg .count none (encodeWord m ++ suffix) (encodeWord C) [] [false]
          ((encodeWord q).reverse ++ (encodeWord C).reverse) []) := by
    rw [Function.iterate_add_apply _ (q + 1) ((2 * C + 1) + 1), hfirst]
    simpa only [List.append_assoc] using
      copyFieldTrace (q := q) .alphabet .count rfl q (encodeWord m ++ suffix)
        (encodeWord C) [] [false] (encodeWord C).reverse [] none
  have ht : 2 * C + q + m + 4 = (m + 1) + ((q + 1) + ((2 * C + 1) + 1)) := by omega
  change (advance (TM2.step (program q)))^[2 * C + q + m + 4]
    (some (initList (machine q) input)) = _
  rw [ht, Function.iterate_add_apply _ (m + 1) ((q + 1) + ((2 * C + 1) + 1)), hsecond]
  have hlast := countTrace (q := q) m suffix (encodeWord C) [] [false]
    ((encodeWord q).reverse ++ (encodeWord C).reverse) [] none
  simpa [encodeWord, encodeWords, List.reverse_append, List.append_assoc] using hlast

end UniqueGamesTheorem.Explicit.MachineSingleOrbitHeader

/-! Actual subtraction of the right-side address offset, preserving the unary
capacity tape for every later edge. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitSubtract

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Reduction
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem subtractStep_zero (q : Nat) (suffix saved remaining accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register suffix (encodeWord 0) saved remaining accumulator output) =
      some (cfg .restore none suffix (encodeWord 0) saved remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, initialState]

theorem subtractStep_succ (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register (List.replicate (n + 1) true ++ suffix)
        (encodeWord (n + 1)) saved remaining accumulator output) =
      some (cfg .subtract (some true) (List.replicate n true ++ suffix)
        (encodeWord n) (true :: saved) remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

/-- The scan consumes precisely the capacity prefix of the target field. -/
theorem subtractTrace (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .subtract register (List.replicate n true ++ suffix)
        (encodeWord n) saved remaining accumulator output)) =
      some (cfg .restore none suffix (encodeWord 0)
        (List.replicate n true ++ saved) remaining accumulator output) := by
  induction n generalizing saved register with
  | zero =>
    simpa using subtractStep_zero q suffix saved remaining accumulator output register
  | succ n ih =>
    rw [Function.iterate_succ_apply, advance_some, subtractStep_succ, ih]
    congr 2
    simp [List.replicate_add, List.append_assoc]

/-- The real saved-prefix transfer restores `C`, empties scratch, and takes
`C + 1` transitions. -/
theorem restoreTrace (q n : Nat) (suffix remaining accumulator output : List Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .restore none suffix (encodeWord 0) (List.replicate n true)
        remaining accumulator output)) =
      some (cfg .target none suffix (encodeWord n) [] remaining accumulator output) := by
  have h := MachineTransfer.transferAt_fromTapes (Γ := fun _ : Tape => Bool) (σ := Unit)
    Tape.saved Tape.capacity (by decide) id false (Label.restore : Label q) (some .target)
    (program q) rfl (tapes suffix (encodeWord 0) (List.replicate n true)
      remaining accumulator output) () none
  have next_eq : MachineTransfer.nextAt Tape.capacity (program q) =
      advance (TM2.step (program q)) := rfl
  rw [next_eq] at h
  simpa only [cfg, restore_tapes,
    tapes_saved, tapes_capacity, List.length_replicate,
    List.reverse_replicate, List.map_id, encodeWord, List.replicate_zero,
    List.nil_append] using h

/-- The complete target-offset removal preserves every other tape. In
particular the capacity is reusable and the `v` field delimiter is untouched. -/
theorem removeOffsetTrace (q C v : Nat) (suffix remaining accumulator output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * (C + 1)]
      (some (cfg .subtract register (encodeWord (C + v) ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .target none (encodeWord v ++ suffix) (encodeWord C)
        [] remaining accumulator output) := by
  have hw : encodeWord (C + v) ++ suffix =
      List.replicate C true ++ (encodeWord v ++ suffix) := by
    simp only [encodeWord, List.replicate_add, List.append_assoc]
  rw [hw, show 2 * (C + 1) = (C + 1) + (C + 1) by omega,
    Function.iterate_add_apply, subtractTrace]
  simp only [List.append_nil]
  exact restoreTrace q C (encodeWord v ++ suffix) remaining accumulator output

end UniqueGamesTheorem.Explicit.MachineSingleOrbitSubtract

/-! Complete ordered row traversal of the physical one-orbit postprocessor. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitRows

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitSubtract MachineSingleOrbitCodec

theorem rowTrace {C q : Nat} (c : Constraint C q)
    (suffix remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowCost c]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .guard none suffix (encodeWord C) [] remaining
        ((rowBits c).reverse ++ accumulator) output) := by
  let table := encodeWords (tableWords c.permutation)
  let afterSource := (encodeWord c.source.val).reverse ++ accumulator
  let afterTarget := (encodeWord c.target.val).reverse ++ afterSource
  have hs := copyFieldTrace (q := q) .source .subtract rfl c.source.val
    (encodeWord (C + c.target.val) ++ table ++ suffix)
    (encodeWord C) [] remaining accumulator output register
  have hd := removeOffsetTrace q C c.target.val (table ++ suffix)
    remaining afterSource output none
  have ht := copyFieldTrace (q := q) .target (.table 0) rfl c.target.val
    (table ++ suffix) (encodeWord C) [] remaining afterSource output none
  have hp := tableTrace (q := q) 0 (tableWords c.permutation)
    (by simp) suffix (encodeWord C) [] remaining afterTarget output none
  have hs' : (advance (TM2.step (program q)))^[c.source.val + 1]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .subtract none (encodeWord (C + c.target.val) ++ (table ++ suffix))
        (encodeWord C) [] remaining afterSource output) := by
    simpa only [doubledRowBits_eq, List.append_assoc, afterSource, table] using hs
  have hsd := joinTrace hs' hd
  have hsdt := joinTrace hsd ht
  have hall := joinTrace hsdt hp
  have hcost : (encodeWords (tableWords c.permutation)).length + 1 +
        (c.target.val + 1 + (2 * (C + 1) + (c.source.val + 1))) = rowCost c := by
    simp only [rowCost, doubledRowBits_eq, List.length_append, encodeWord_length]
    omega
  rw [hcost] at hall
  simpa only [rowBits_eq, List.reverse_append, List.append_assoc,
    afterTarget, afterSource, table] using hall

theorem guardStep_succ (q n : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord (n + 1)) accumulator output) =
      some (cfg .source none input capacity saved (encodeWord n) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

theorem guardStep_zero (q : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord 0) accumulator output) =
      some (cfg .finishStart none input capacity saved (encodeWord 0) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord]

/-- The actual counted loop visits every row once and preserves its order.
No complete-loop execution is supplied as an input hypothesis. -/
theorem rowsTrace {C q : Nat} (cs : List (Constraint C q))
    (suffix accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowsCost cs]
      (some (cfg .guard register (doubledRowsBits cs ++ suffix)
        (encodeWord C) [] (encodeWord cs.length) accumulator output)) =
      some (cfg .finishStart none suffix (encodeWord C) [] (encodeWord 0)
        ((rowsBits cs).reverse ++ accumulator) output) := by
  induction cs generalizing accumulator register with
  | nil =>
    simpa [rowsCost] using guardStep_zero q suffix (encodeWord C) [] accumulator output register
  | cons c cs ih =>
    have hg : (advance (TM2.step (program q)))^[1]
        (some (cfg .guard register (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] (encodeWord (c :: cs).length) accumulator output)) =
        some (cfg .source none (doubledRowBits c ++ (doubledRowsBits cs ++ suffix))
          (encodeWord C) [] (encodeWord cs.length) accumulator output) := by
      simpa only [Function.iterate_one, advance_some, List.length_cons,
        doubledRowsBits_cons, List.append_assoc] using
        guardStep_succ q cs.length (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] accumulator output register
    have hr := rowTrace c (doubledRowsBits cs ++ suffix) (encodeWord cs.length)
      accumulator output none
    have ht := ih ((rowBits c).reverse ++ accumulator) none
    have hall := joinTrace (joinTrace hg hr) ht
    have hcost : rowsCost cs + (rowCost c + 1) = rowsCost (c :: cs) := by
      rw [rowsCost_cons]
      omega
    rw [hcost] at hall
    simpa only [rowsBits_cons, List.reverse_append, List.append_assoc] using hall

end UniqueGamesTheorem.Explicit.MachineSingleOrbitRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSingleOrbitFinishLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual tape cleanup, accumulator reversal, and halt for the one-orbit
postprocessor. The time bound is derived from an actual executed prefix. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitFinish

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem haltList_eq (q : Nat) (bits : List Bool) : haltList (machine q) bits =
    ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  change (⟨none, initialState, (haltList (machine q) bits).stk⟩ : (machine q).Cfg) = _
  apply congrArg (fun base => (⟨none, initialState, base⟩ : (machine q).Cfg))
  funext tape
  cases tape <;> simp [haltList, machine, SourceRuntimeFinish.canonicalTapes] <;> rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩) 1 where
  steps := 1
  evals_in_steps := by rfl
  steps_le_m := Nat.le_refl _

def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

/-- This helper consumes a proved prefix trace. The final runtime theorem
supplies that trace from the concrete header and complete row traversal. -/
def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using
        joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys clearKeys_covers
    () Label.finish none (program q) (fun _ => rfl) base outputEmpty () none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q) input (prefixTime + 1)
    prefixRun clearKeys Tape.accumulator Tape.output accumulator_not_mem_clearKeys
    output_not_mem_clearKeys clearKeys_covers base outputEmpty (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end UniqueGamesTheorem.Explicit.MachineSingleOrbitFinish

/-!
Complete finite-machine postprocessing of the doubled address representation.
Every input field and row is physically processed. The time polynomial is in
the literal input bit length, including the final reversal and all tape cleanup.
-/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitRuntime

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitCodec MachineSingleOrbitRows

def finalTapes {q : Nat} (I : Instance q) : Tape → List Bool :=
  tapes [] (encodeWord I.vertices) [] (encodeWord 0) (gameBits I).reverse []

/-- The complete prefix is obtained from the actual header and row traces. -/
theorem prefixTrace {q : Nat} (I : Instance q) :
    (advance (TM2.step (program q)))^[prefixCost I]
      (some (initList (machine q) (gameBits (doubleInstance I)))) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
  have hh := MachineSingleOrbitHeader.headerTrace q I.vertices I.constraints.length
    (doubledRowsBits I.constraints)
  have hr := rowsTrace I.constraints []
    (encodeWords [I.vertices, q, I.constraints.length]).reverse [] none
  have hbits : gameBits I =
      encodeWords [I.vertices, q, I.constraints.length] ++ rowsBits I.constraints := by
    simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc] using gameBits_eq I
  have hr' : (advance (TM2.step (program q)))^[rowsCost I.constraints]
      (some (cfg .guard none (doubledRowsBits I.constraints) (encodeWord I.vertices) []
        (encodeWord I.constraints.length)
        (encodeWords [I.vertices, q, I.constraints.length]).reverse [])) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
    simpa only [List.append_nil, cfg, finalTapes, hbits, List.reverse_append, initialState]
      using hr
  have run := joinTrace hh hr'
  have hcost : rowsCost I.constraints +
      (2 * I.vertices + q + I.constraints.length + 4) = prefixCost I := by
    rw [prefixCost, input_length_eq]
    unfold rowsCost
    omega
  rw [hcost] at run
  simpa only [doubled_gameBits_eq] using run

def prefixInTime {q : Nat} (I : Instance q) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (gameBits (doubleInstance I)))
      (some ⟨some .finishStart, initialState, finalTapes I⟩)
      (prefixPolynomial.eval (gameBits (doubleInstance I)).length) where
  steps := prefixCost I
  evals_in_steps := prefixTrace I
  steps_le_m := prefixCost_le I

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSingleOrbitFinish.timePolynomial q prefixPolynomial

/-- Literal init-to-halt execution, with every non-output tape empty at halt. -/
def fullRunInTime {q : Nat} (I : Instance q) :
    TM2OutputsInTime (machine q) (gameBits (doubleInstance I))
      (some (gameBits I)) ((timePolynomial q).eval (gameBits (doubleInstance I)).length) := by
  let run := MachineSingleOrbitFinish.completePrefix q (gameBits (doubleInstance I))
    prefixPolynomial (finalTapes I) (prefixInTime I) rfl
  simpa only [finalTapes, tapes_accumulator, List.reverse_reverse, timePolynomial] using run

/-- A proved polynomial-time codec conversion, without an assumed time bound,
an output-size certificate, or an unbounded integer in finite machine state. -/
def computableInPolyTime (q : Nat) :
    TM2ComputableInPolyTime (fun I : Instance q => gameBits (doubleInstance I)) gameBits id where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun I := by
    change TM2OutputsInTime (machine q) ((gameBits (doubleInstance I)).map id)
      (some ((gameBits I).map id))
      ((timePolynomial q).eval (gameBits (doubleInstance I)).length)
    erw [List.map_id, List.map_id]
    exact fullRunInTime I

end UniqueGamesTheorem.Explicit.MachineSingleOrbitRuntime

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineTemplateAddress
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A fixed canonical-word template followed by actual radix-address execution.
The program is determined by the fixed tokens and tape layout. Numeric field
values enter only the tape invariants and execution theorem, never the labels. -/

namespace UniqueGamesTheorem.Reduction.MachineTemplateAddress

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def hornerLayout : MachineHorner.Layout width ↪ Tape q width where
  toFun
    | .inl 0 => .radix
    | .inl 1 => .accA
    | .inl 2 => .accB
    | .inl 3 => .output
    | .inl 4 => .counter
    | .inl 5 => .hornerScratch
    | .inr i => .digit i
  inj' := by
    rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> simp_all
    · fin_cases a <;> simp_all
    · fin_cases b <;> simp_all
    · exact congrArg Sum.inr (Tape.digit.inj h)

def hornerSlots (slots : Tape q width ↪ K) : MachineHorner.Layout width ↪ K :=
  hornerLayout.trans slots

/-- Fixed finite instruction assembly, with arbitrary placement and continuation. -/
def instruction (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
    (place : Label tokens.length width (chosen slots) → Λ) (exit : Option Λ) :
    Label tokens.length width (chosen slots) → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .inl l => MachineFieldTemplate.instruction tokens (fun j => slots (.field j))
      (slots .copyScratch) (slots .reversed) (fun l => place (emitLabel l))
      (some (place reverseLabel)) l
  | .inr (.inl _) => MachineTransfer.loopAt (slots .reversed) (slots .forward) id false
      (place reverseLabel) (some (place (parseLabel (SourceFieldArray.startLabel width 0))))
  | .inr (.inr (.inl l)) =>
      if h : l.1.val < width then
        if l.2 then
          SourceMachine.fieldLoop (slots .forward) (slots (.digit ⟨l.1.val, h⟩))
            (place (parseLabel (l.1, true)))
            (some (place (parseLabel (SourceFieldArray.startLabel width (l.1.val + 1)))))
        else SourceMachine.fieldStart (slots (.digit ⟨l.1.val, h⟩))
          (place (parseLabel (l.1, true)))
      else SourceFieldArray.finish (slots .forward) (some (place (hornerLabel .start)))
  | .inr (.inr (.inr (.inl l))) => MachineHorner.statement (hornerSlots slots)
      (fun l => place (hornerLabel l))
      (MachineDrainMany.entry (chosen slots) (fun l => place (cleanupLabel l)) exit) l
  | .inr (.inr (.inr (.inr l))) => MachineDrainMany.instruction (chosen slots)
      (fun l => place (cleanupLabel l)) exit l

def parsedTapes (slots : Tape q width ↪ K) (base : K → List Bool) (values : List Nat) :
    K → List Bool :=
  SourceFieldArray.sequenceTapes (slots .forward) (parseDestination slots)
    (forwardTapes slots base values) 0 values []

def resultTapes (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    K → List Bool := Function.update base (slots .output) (encodeWord value ++ base (slots .output))

def afterHorner (slots : Tape q width ↪ K) (base : K → List Bool) (B : Nat) (values : List Nat) :
    K → List Bool :=
  MachineHorner.resultTapes (hornerSlots slots) (parsedTapes slots base values)
    (MachineHorner.value B (digits values) width)

def phaseSteps (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
    (base : K → List Bool) (B : Nat) (values : List Nat) : Nat :=
  MachineFieldTemplate.templateSteps tokens (fun j => base (slots (.field j))) +
    ((encodeWords values).length + 1) + (values.sum + 2 * values.length + 1) +
    MachineHorner.steps B (digits values) width +
    MachineDrainMany.steps (chosen slots) (afterHorner slots base B values)

@[simp] theorem resultTapes_output (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    resultTapes slots base value (slots .output) = encodeWord value ++ base (slots .output) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat)
    (tape : K) (hne : tape ≠ slots .output) : resultTapes slots base value tape = base tape := by
  simp [resultTapes, hne]

/-- The numeric recurrence used by the checked Horner machine is the direct
canonical-address radix, in the original template-word order. -/
theorem hornerValue_eq_radix (B : Nat) (values : List Nat) :
    MachineHorner.value B (digits values) values.length = CanonicalAddress.radix B values := by
  rw [MachineHorner.value_eq_foldl, CanonicalAddress.radix_eq_foldl]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, digits,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem parsedTapes_other (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) (tape : K)
    (notForward : tape ≠ slots .forward) (notDigit : ∀ i, tape ≠ slots (.digit i)) :
    parsedTapes slots base values tape = base tape := by
  rw [parsedTapes, SourceFieldArray.sequenceTapes_other]
  · exact Function.update_of_ne notForward _ _
  · exact notForward
  · intro r hr
    simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
    exact notDigit _

theorem parsedTapes_source (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) :
    parsedTapes slots base values (slots .forward) = [] := by
  apply SourceFieldArray.sequenceTapes_source
  · intro r hr
    simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
    exact slots.injective.ne (by simp)
  · simp [forwardTapes]

theorem parsedTapes_digit (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) (clean : Clean slots base) (i : Fin width) :
    parsedTapes slots base values (slots (.digit i)) = encodeWord (digits values i.val) := by
  have hi : i.val < values.length := by omega
  have h := SourceFieldArray.sequenceTapes_selected (slots .forward) (parseDestination slots)
    (forwardTapes slots base values) 0 values [] i.val hi
    (by
      intro r hr
      simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
      exact slots.injective.ne (by simp))
    (by
      intro r s hr hs h
      simp only [Nat.zero_add, parseDestination_below slots r (by omega),
        parseDestination_below slots s (by omega)] at h
      exact congrArg Fin.val (Tape.digit.inj (slots.injective h)))
  simpa [parsedTapes, parseDestination, i.isLt, forwardTapes, clean.digit,
    slots.injective.ne (show Tape.digit i ≠ Tape.forward by simp), digits,
    List.getElem?_eq_getElem hi] using h

theorem parsedTapes_clean (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) (clean : Clean slots base) :
    MachineHorner.Clean (hornerSlots slots) (parsedTapes slots base values) := by
  constructor
  · rw [show hornerSlots slots (.inl 1) = slots .accA from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.accA
  · rw [show hornerSlots slots (.inl 2) = slots .accB from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.accB
  · rw [show hornerSlots slots (.inl 4) = slots .counter from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.counter
  · rw [show hornerSlots slots (.inl 5) = slots .hornerScratch from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.hornerScratch

theorem cleanup_result (slots : Tape q width ↪ K) (base : K → List Bool)
    (B : Nat) (values : List Nat) (hlen : values.length = width) (clean : Clean slots base) :
    MachineDrainMany.finalTapes (chosen slots) (afterHorner slots base B values) =
      resultTapes slots base (CanonicalAddress.radix B values) := by
  have hv : MachineHorner.value B (digits values) width = CanonicalAddress.radix B values := by
    rw [← hlen, hornerValue_eq_radix]
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  by_cases hd : tape ∈ chosen slots
  · rw [ite_eq_left hd]
    obtain ⟨i, rfl⟩ := (mem_chosen slots tape).mp hd
    simp [resultTapes, slots.injective.ne (show Tape.digit i ≠ Tape.output by simp), clean.digit]
  · rw [ite_eq_right hd]
    have notDigit : ∀ i, tape ≠ slots (.digit i) := by
      intro i hi
      exact hd ((mem_chosen slots tape).mpr ⟨i, hi.symm⟩)
    by_cases ho : tape = slots .output
    · subst tape
      simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        Function.update_self, resultTapes_output, hv]
      rw [parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp)) notDigit]
    · simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        resultTapes, Function.update_of_ne ho]
      by_cases hf : tape = slots .forward
      · subst tape
        rw [parsedTapes_source slots base values hlen, clean.forward]
      · exact parsedTapes_other slots base values hlen tape hf notDigit

section Execution

variable (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
variable (place : Label tokens.length width (chosen slots) → Λ) (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ l, P (place l) = instruction tokens slots place exit l)

include atInstruction

omit [DecidableEq K] in
theorem parse_atStart (r : Nat) (hr : r < width) :
    P (place (parseLabel (SourceFieldArray.startLabel width r))) =
      SourceMachine.fieldStart (parseDestination slots r)
        (place (parseLabel (SourceFieldArray.loopLabel width r))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel, SourceFieldArray.loopLabel,
    SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem parse_atLoop (r : Nat) (hr : r < width) :
    P (place (parseLabel (SourceFieldArray.loopLabel width r))) =
      SourceMachine.fieldLoop (slots .forward) (parseDestination slots r)
        (place (parseLabel (SourceFieldArray.loopLabel width r)))
        (some (place (parseLabel (SourceFieldArray.startLabel width (r + 1))))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel, SourceFieldArray.loopLabel,
    SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem parse_atDone :
    P (place (parseLabel (SourceFieldArray.startLabel width width))) =
      SourceFieldArray.finish (slots .forward) (some (place (hornerLabel .start))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel]

theorem phaseTrace (base : K → List Bool) (B : Nat) (values : List Nat)
    (hlen : values.length = width) (clean : Clean slots base)
    (baseField : base (slots .radix) = encodeWord B)
    (wordCorrect : MachineFieldTemplate.templateOutput tokens (fun j => base (slots (.field j))) =
      encodeWords values) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step P))^[phaseSteps tokens slots base B values]
      (some ⟨some (place (emitLabel (MachineFieldTemplate.startAt tokens.length 0))),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (CanonicalAddress.radix B values)⟩ := by
  let emitted := MachineFieldTemplate.outputTapes base (slots .reversed) (encodeWords values)
  have emitRun := MachineFieldTemplate.phaseTrace tokens (fun j => slots (.field j))
    (slots .copyScratch) (slots .reversed)
    (fun _ => slots.injective.ne (by simp)) (fun _ => slots.injective.ne (by simp))
    (slots.injective.ne (by simp)) (fun l => place (emitLabel l))
    (some (place reverseLabel)) P (fun l => atInstruction (emitLabel l))
    base clean.copyScratch ((ambient, ()), register)
  rw [wordCorrect] at emitRun
  change (MachineComposition.advance (TM2.step P))^[_] _ =
    some ⟨some (place reverseLabel), ((ambient, ()), none), emitted⟩ at emitRun
  have reverseRun := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (slots .reversed) (slots .forward) (slots.injective.ne (by simp)) id false
    (place reverseLabel) (some (place (parseLabel (SourceFieldArray.startLabel width 0))))
    P (atInstruction reverseLabel) emitted (ambient, ()) none
  have reverseResult : MachineTransfer.tapesAt (slots .reversed) (slots .forward) emitted []
      ((emitted (slots .reversed)).reverse.map id ++ emitted (slots .forward)) =
      forwardTapes slots base values := by
    funext tape
    by_cases hr : tape = slots .reversed
    · subst tape
      simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt, forwardTapes,
        slots.injective.ne (show Tape.reversed ≠ Tape.forward by simp), clean.reversed]
    · by_cases hf : tape = slots .forward
      · subst tape
        simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt, forwardTapes,
          slots.injective.ne (show Tape.forward ≠ Tape.reversed by simp),
          clean.reversed, clean.forward]
      · simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt,
          forwardTapes, hr, hf]
  rw [reverseResult] at reverseRun
  have reverseLength : (emitted (slots .reversed)).length + 1 = (encodeWords values).length + 1 := by
    simp [emitted, MachineFieldTemplate.outputTapes, clean.reversed]
  rw [reverseLength] at reverseRun
  change (MachineComposition.advance (TM2.step P))^[(encodeWords values).length + 1]
    (some ⟨some (place reverseLabel), ((ambient, ()), none), emitted⟩) =
    some ⟨some (place (parseLabel (SourceFieldArray.startLabel width 0))),
      ((ambient, ()), none), forwardTapes slots base values⟩ at reverseRun
  have parseRun := SourceFieldArray.sequenceTrace (slots .forward) (parseDestination slots)
    (fun r => place (parseLabel (SourceFieldArray.startLabel width r)))
    (fun r => place (parseLabel (SourceFieldArray.loopLabel width r)))
    (some (place (hornerLabel .start))) P (forwardTapes slots base values) 0 values []
    (by
      intro r hr
      simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
      exact slots.injective.ne (by simp))
    (by intro r hr; simpa using parse_atStart tokens slots place exit P atInstruction r (by omega))
    (by intro r hr; simpa using parse_atLoop tokens slots place exit P atInstruction r (by omega))
    (by simpa only [Nat.zero_add, hlen] using parse_atDone tokens slots place exit P atInstruction)
    (by simp [forwardTapes]) (ambient, ()) none
  change (MachineComposition.advance (TM2.step P))^[values.sum + 2 * values.length + 1]
    (some ⟨some (place (parseLabel (SourceFieldArray.startLabel width 0))),
      ((ambient, ()), none), forwardTapes slots base values⟩) =
    some ⟨some (place (hornerLabel .start)), ((ambient, ()), none),
      parsedTapes slots base values⟩ at parseRun
  have hbase : parsedTapes slots base values (hornerSlots slots (.inl 0)) = encodeWord B := by
    change parsedTapes slots base values (slots .radix) = _
    rw [parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
      (fun _ => slots.injective.ne (by simp))]
    exact baseField
  have hornerRun := MachineHorner.hornerTrace (hornerSlots slots) (fun l => place (hornerLabel l))
    (MachineDrainMany.entry (chosen slots) (fun l => place (cleanupLabel l)) exit)
    P (fun l => atInstruction (hornerLabel l)) (parsedTapes slots base values) B (digits values)
    hbase (parsedTapes_digit slots base values hlen clean)
    (parsedTapes_clean slots base values hlen clean) ambient none
  have cleanupRun := MachineDrainMany.trace (chosen slots) (fun l => place (cleanupLabel l)) exit
    P (fun l => atInstruction (cleanupLabel l)) (afterHorner slots base B values) (ambient, ()) none
  rw [MachineDrainMany.finalRegister_none, cleanup_result slots base B values hlen clean] at cleanupRun
  rw [show phaseSteps tokens slots base B values =
    MachineDrainMany.steps (chosen slots) (afterHorner slots base B values) +
      (MachineHorner.steps B (digits values) width +
      ((values.sum + 2 * values.length + 1) +
      (((encodeWords values).length + 1) +
      MachineFieldTemplate.templateSteps tokens (fun j => base (slots (.field j)))))) by
        unfold phaseSteps; omega]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := MachineHorner.steps B (digits values) width)]
  rw [Function.iterate_add_apply (m := values.sum + 2 * values.length + 1)]
  rw [Function.iterate_add_apply (m := (encodeWords values).length + 1)]
  rw [emitRun, reverseRun, parseRun, hornerRun]
  exact cleanupRun

end Execution

theorem phaseSteps_le_timePolynomial (tokens : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool) (B : Nat) (values : List Nat)
    (hlen : values.length = width) (clean : Clean slots base) (M : Nat)
    (fieldsBound : ∀ j, (base (slots (.field j))).length ≤ M)
    (wordsBound : (encodeWords values).length ≤ M) (radixBound : B ≤ M)
    (digitBound : ∀ i, i < width → digits values i ≤ M) :
    phaseSteps tokens slots base B values ≤ (timePolynomial tokens.length width).eval M := by
  have hcopied := copiedLength_le tokens (fun j => base (slots (.field j))) M fieldsBound
  have htemplate := MachineFieldTemplate.templateSteps_le tokens (fun j => base (slots (.field j)))
  have hhorner := MachineHorner.steps_le_timePolynomial B (digits values) width M radixBound digitBound
  have hselected : ∀ tape ∈ chosen slots, (afterHorner slots base B values tape).length ≤ M + 1 := by
    intro tape ht
    obtain ⟨i, rfl⟩ := (mem_chosen slots tape).mp ht
    have heq : afterHorner slots base B values (slots (.digit i)) =
        encodeWord (digits values i.val) := by
      simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        Function.update_of_ne (slots.injective.ne (show Tape.digit i ≠ Tape.output by simp))]
      exact parsedTapes_digit slots base values hlen clean i
    rw [heq]
    simpa only [encodeWord, List.length_append, List.length_replicate, List.length_singleton] using
      Nat.add_le_add_right (digitBound i.val i.isLt) 1
  have hsum := lengthSum_le (chosen slots) (afterHorner slots base B values) (M + 1) hselected
  have hcleanup := MachineDrainMany.steps_le (chosen slots) (afterHorner slots base B values)
  have hchosen : (chosen slots).length = width := by simp [chosen]
  rw [hchosen] at hsum hcleanup
  have hparse := SourceFieldArray.sequence_time_eq_length values
  rw [hlen] at hparse
  rw [timePolynomial_eval]
  unfold phaseSteps
  rw [hlen]
  nlinarith

end UniqueGamesTheorem.Reduction.MachineTemplateAddress

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineAddressEdgeLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual edge emission from two fixed address templates. Capacity is copied
before unary addition, so the original capacity tape is preserved. All local
labels and literal instructions depend only on fixed templates and layout. -/

namespace UniqueGamesTheorem.Reduction.MachineAddressEdge

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

abbrev Tape (q width : Nat) := MachineTemplateAddress.Tape q width ⊕ Fin 2

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def addressSlots (slots : Tape q width ↪ K) : MachineTemplateAddress.Tape q width ↪ K where
  toFun tape := slots (.inl tape)
  inj' := by intro a b h; exact Sum.inl.inj (slots.injective h)

def capacityTape (slots : Tape q width ↪ K) : K := slots (.inr 0)
def outputTape (slots : Tape q width ↪ K) : K := slots (.inr 1)
def workTape (slots : Tape q width ↪ K) : K := addressSlots slots .output
def tempTape (slots : Tape q width ↪ K) : K := addressSlots slots .forward
def scratchTape (slots : Tape q width ↪ K) : K := addressSlots slots .copyScratch

omit [DecidableEq K] in
theorem address_ne_output (slots : Tape q width ↪ K) (tape : MachineTemplateAddress.Tape q width) :
    addressSlots slots tape ≠ outputTape slots := slots.injective.ne (by simp)

omit [DecidableEq K] in
theorem capacity_ne_output (slots : Tape q width ↪ K) :
    capacityTape slots ≠ outputTape slots := slots.injective.ne (by simp)

omit [DecidableEq K] in
theorem work_ne_output (slots : Tape q width ↪ K) :
    workTape slots ≠ outputTape slots := address_ne_output slots _

omit [DecidableEq K] in
theorem temp_ne_work (slots : Tape q width ↪ K) :
    tempTape slots ≠ workTape slots := slots.injective.ne (by simp)

def instruction (left right : List (MachineFieldTemplate.Token q))
    (permutation : List Bool) (slots : Tape q width ↪ K)
    (place : Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) → Λ)
    (exit : Option Λ) :
    Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) →
      TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .inl label => MachineTemplateAddress.instruction left (addressSlots slots) (fun l => place (leftLabel l))
      (some (place (plumbing 0))) label
  | .inr (.inl label) => MachineTemplateAddress.instruction right (addressSlots slots)
      (fun l => place (rightLabel l)) (some (place (plumbing 1))) label
  | .inr (.inr 0) => MachineTransfer.loopAt (workTape slots) (outputTape slots) id false
      (place (plumbing 0))
      (some (place (rightLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt right.length 0)))))
  | .inr (.inr 1) => MachineTransfer.loopAt (capacityTape slots) (scratchTape slots) id false
      (place (plumbing 1)) (some (place (plumbing 2)))
  | .inr (.inr 2) => MachineCopy.forkLoop (scratchTape slots) (capacityTape slots)
      (tempTape slots) false (place (plumbing 2)) (some (place (plumbing 3)))
  | .inr (.inr 3) => MachineUnaryAddAt.loop (tempTape slots) (workTape slots)
      (place (plumbing 3)) (some (place (plumbing 4)))
  | .inr (.inr 4) => MachineDrain.drain (tempTape slots)
      (place (plumbing 4)) (some (place (plumbing 5)))
  | .inr (.inr 5) => MachineTransfer.loopAt (workTape slots) (outputTape slots) id false
      (place (plumbing 5)) (some (place (plumbing 6)))
  | .inr (.inr 6) => .load MachineFieldTemplate.reset
      (pushWord (outputTape slots) permutation (MachineFieldTemplate.jump exit))

structure Clean (slots : Tape q width ↪ K) (base : K → List Bool) : Prop where
  address : MachineTemplateAddress.Clean (addressSlots slots) base
  work : base (workTape slots) = []

def appended (slots : Tape q width ↪ K) (base : K → List Bool) (bits : List Bool) :
    K → List Bool := MachineFieldTemplate.outputTapes base (outputTape slots) bits

@[simp] theorem appended_address (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) (tape : MachineTemplateAddress.Tape q width) :
    appended slots base bits (addressSlots slots tape) = base (addressSlots slots tape) :=
  MachineFieldTemplate.outputTapes_other base (outputTape slots) bits _
    (address_ne_output slots tape)

@[simp] theorem appended_capacity (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) : appended slots base bits (capacityTape slots) = base (capacityTape slots) :=
  MachineFieldTemplate.outputTapes_other base (outputTape slots) bits _ (capacity_ne_output slots)

@[simp] theorem appended_output (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) :
    appended slots base bits (outputTape slots) = bits.reverse ++ base (outputTape slots) := by
  exact MachineFieldTemplate.outputTapes_output _ _ _

theorem appended_other (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) (tape : K) (hne : tape ≠ outputTape slots) :
    appended slots base bits tape = base tape :=
  MachineFieldTemplate.outputTapes_other _ _ _ _ hne

theorem appended_append (slots : Tape q width ↪ K) (base : K → List Bool)
    (first second : List Bool) :
    appended slots (appended slots base first) second = appended slots base (first ++ second) :=
  MachineFieldTemplate.outputTapes_append _ _ _ _

theorem Clean.appended (slots : Tape q width ↪ K) (base : K → List Bool)
    (clean : Clean slots base) (bits : List Bool) : Clean slots (appended slots base bits) := by
  constructor
  · constructor
    · simpa only [appended_address] using clean.address.reversed
    · simpa only [appended_address] using clean.address.forward
    · simpa only [appended_address] using clean.address.copyScratch
    · simpa only [appended_address] using clean.address.accA
    · simpa only [appended_address] using clean.address.accB
    · simpa only [appended_address] using clean.address.counter
    · simpa only [appended_address] using clean.address.hornerScratch
    · intro j; simpa only [appended_address] using clean.address.digit j
  · simpa only [workTape, appended_address] using clean.work

def edgeBits (B C : Nat) (leftValues rightValues : List Nat) (permutation : List Bool) :
    List Bool :=
  encodeWords [CanonicalAddress.radix B leftValues, C + CanonicalAddress.radix B rightValues] ++
    permutation

def phaseSteps (left right : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool)
    (B C : Nat) (leftValues rightValues : List Nat) : Nat :=
  MachineTemplateAddress.phaseSteps left (addressSlots slots) base B leftValues +
    MachineTemplateAddress.phaseSteps right (addressSlots slots)
      (appended slots base (encodeWord (CanonicalAddress.radix B leftValues))) B rightValues +
    CanonicalAddress.radix B leftValues + CanonicalAddress.radix B rightValues + 4 * C + 12

theorem addressResult_eq (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    MachineTemplateAddress.resultTapes (addressSlots slots) base value =
      Function.update base (workTape slots) (encodeWord value ++ base (workTape slots)) := rfl

theorem transfer_result (slots : Tape q width ↪ K) (base : K → List Bool)
    (value : Nat) (empty : base (workTape slots) = []) :
    MachineTransfer.tapesAt (workTape slots) (outputTape slots)
      (MachineTemplateAddress.resultTapes (addressSlots slots) base value) []
      (((MachineTemplateAddress.resultTapes (addressSlots slots) base value) (workTape slots)).reverse.map id ++
        (MachineTemplateAddress.resultTapes (addressSlots slots) base value) (outputTape slots)) =
      appended slots base (encodeWord value) := by
  funext tape
  by_cases hw : tape = workTape slots
  · subst tape
    simp [MachineTransfer.tapesAt, addressResult_eq, appended,
      MachineFieldTemplate.outputTapes, work_ne_output, empty]
  · by_cases ho : tape = outputTape slots
    · subst tape
      simp [MachineTransfer.tapesAt, addressResult_eq, appended,
        MachineFieldTemplate.outputTapes, Ne.symm (work_ne_output slots), empty]
    · simp [MachineTransfer.tapesAt, addressResult_eq, appended,
        MachineFieldTemplate.outputTapes, hw, ho]

section Execution

variable (left right : List (MachineFieldTemplate.Token q)) (permutation : List Bool)
variable (slots : Tape q width ↪ K)
variable (place : Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) → Λ)
variable (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ label,
  P (place label) = instruction left right permutation slots place exit label)

include atInstruction

theorem literalStep (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (plumbing 6)), state, base⟩ =
      some ⟨exit, MachineFieldTemplate.reset state, appended slots base permutation⟩ := by
  change some (TM2.stepAux (P (place (plumbing 6))) state base) = _
  rw [atInstruction (plumbing 6)]
  simp only [instruction, plumbing, TM2.stepAux]
  rw [stepAux_pushWord]
  cases exit <;> rfl

/-- Both actual address computations, a preserved-capacity copy, unary addition,
cleanup, two reverse transfers, and the fixed permutation instruction. -/
theorem phaseTrace (base : K → List Bool) (B C : Nat)
    (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base)
    (baseField : base (addressSlots slots .radix) = encodeWord B)
    (capacityField : base (capacityTape slots) = encodeWord C)
    (leftCorrect : MachineFieldTemplate.templateOutput left
      (fun j => base (addressSlots slots (.field j))) = encodeWords leftValues)
    (rightCorrect : MachineFieldTemplate.templateOutput right
      (fun j => base (addressSlots slots (.field j))) = encodeWords rightValues)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step P))^[phaseSteps left right slots base B C leftValues rightValues]
      (some ⟨some (place (leftLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt left.length 0)))),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        appended slots base (edgeBits B C leftValues rightValues permutation)⟩ := by
  let L := CanonicalAddress.radix B leftValues
  let R := CanonicalAddress.radix B rightValues
  let afterLeft := appended slots base (encodeWord L)
  have cleanLeft : Clean slots afterLeft := Clean.appended slots base clean (encodeWord L)
  let rightResult := MachineTemplateAddress.resultTapes (addressSlots slots) afterLeft R
  let copied := Function.update rightResult (tempTape slots) (encodeWord C)
  let added := MachineUnaryAddAt.unaryTapes (tempTape slots) (workTape slots) copied 0 (C + R) [] []
  let shifted := MachineTemplateAddress.resultTapes (addressSlots slots) afterLeft (C + R)
  have leftRun := MachineTemplateAddress.phaseTrace left (addressSlots slots) (fun l => place (leftLabel l))
    (some (place (plumbing 0))) P (fun l => atInstruction (leftLabel l))
    base B leftValues leftLength clean.address baseField leftCorrect ambient register
  have transferLeft := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (workTape slots) (outputTape slots) (work_ne_output slots) id false
    (place (plumbing 0))
    (some (place (rightLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt right.length 0)))))
    P (atInstruction (plumbing 0)) (MachineTemplateAddress.resultTapes (addressSlots slots) base L) (ambient, ()) none
  rw [transfer_result slots base L clean.work] at transferLeft
  have leftWork : MachineTemplateAddress.resultTapes (addressSlots slots) base L (workTape slots) = encodeWord L := by
    simp only [addressResult_eq, Function.update_self, clean.work, List.append_nil]
  rw [leftWork] at transferLeft
  change (MachineComposition.advance (TM2.step P))^[(encodeWord L).length + 1]
    (some ⟨some (place (plumbing 0)), ((ambient, ()), none),
      MachineTemplateAddress.resultTapes (addressSlots slots) base L⟩) =
    some ⟨some (place (rightLabel (MachineTemplateAddress.emitLabel
      (MachineFieldTemplate.startAt right.length 0)))), ((ambient, ()), none), afterLeft⟩ at transferLeft
  have rightRun := MachineTemplateAddress.phaseTrace right (addressSlots slots) (fun l => place (rightLabel l))
    (some (place (plumbing 1))) P (fun l => atInstruction (rightLabel l))
    afterLeft B rightValues rightLength cleanLeft.address
    (by simpa [afterLeft] using baseField)
    (by simpa [afterLeft] using rightCorrect) ambient none
  have rightWork : rightResult (workTape slots) = encodeWord R := by
    simp only [rightResult, addressResult_eq, Function.update_self, cleanLeft.work, List.append_nil]
  have rightTemp : rightResult (tempTape slots) = [] := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · exact cleanLeft.address.forward
    · exact temp_ne_work slots
  have rightScratch : rightResult (scratchTape slots) = [] := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · exact cleanLeft.address.copyScratch
    · exact slots.injective.ne (by simp)
  have rightCapacity : rightResult (capacityTape slots) = encodeWord C := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · simpa [afterLeft] using capacityField
    · exact slots.injective.ne (by simp)
  have copyRun := MachineCopy.copyTrace (capacityTape slots) (tempTape slots) (scratchTape slots)
    (slots.injective.ne (by simp)) (slots.injective.ne (by simp))
    (slots.injective.ne (by simp)) false (place (plumbing 1)) (place (plumbing 2))
    (some (place (plumbing 3))) P (atInstruction (plumbing 1)) (atInstruction (plumbing 2))
    rightResult rightScratch (ambient, ()) none
  rw [rightCapacity, rightTemp, List.append_nil] at copyRun
  have addRun := MachineUnaryAddAt.addFromTapes (tempTape slots) (workTape slots)
    (temp_ne_work slots) (place (plumbing 3)) (some (place (plumbing 4)))
    P (atInstruction (plumbing 3)) copied C R [] []
    (by simp [copied])
    (by simp [copied, Ne.symm (temp_ne_work slots), rightWork]) (ambient, ()) none
  have addedTemp : added (tempTape slots) = encodeWord 0 := by
    simp [added, temp_ne_work]
  have drainResult : Function.update added (tempTape slots) [] = shifted := by
    funext tape
    by_cases ht : tape = tempTape slots
    · subst tape
      simp [shifted, addressResult_eq, temp_ne_work, show afterLeft (tempTape slots) = [] from cleanLeft.address.forward]
    · by_cases hw : tape = workTape slots
      · subst tape
        simp [added, MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, shifted,
          addressResult_eq, Ne.symm (temp_ne_work slots), cleanLeft.work]
      · simp [added, MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, copied,
          rightResult, shifted, addressResult_eq, ht, hw]
  have drainRun := (MachineDrain.drainInTime (tempTape slots) (place (plumbing 4))
    (some (place (plumbing 5))) P (atInstruction (plumbing 4)) added (ambient, ()) none).evals_in_steps
  change (MachineComposition.advance (TM2.step P))^[(added (tempTape slots)).length + 1]
    (some ⟨some (place (plumbing 4)), ((ambient, ()), none), added⟩) = _ at drainRun
  rw [addedTemp, drainResult] at drainRun
  have transferRight := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (workTape slots) (outputTape slots) (work_ne_output slots) id false
    (place (plumbing 5)) (some (place (plumbing 6))) P (atInstruction (plumbing 5))
    shifted (ambient, ()) none
  rw [transfer_result slots afterLeft (C + R) cleanLeft.work] at transferRight
  have shiftedWork : shifted (workTape slots) = encodeWord (C + R) := by
    simp only [shifted, addressResult_eq, Function.update_self, cleanLeft.work, List.append_nil]
  rw [shiftedWork] at transferRight
  change (MachineComposition.advance (TM2.step P))^[(encodeWord (C + R)).length + 1]
    (some ⟨some (place (plumbing 5)), ((ambient, ()), none), shifted⟩) =
    some ⟨some (place (plumbing 6)), ((ambient, ()), none),
      appended slots afterLeft (encodeWord (C + R))⟩ at transferRight
  have finishRun := literalStep left right permutation slots place exit P atInstruction
    (appended slots afterLeft (encodeWord (C + R))) ((ambient, ()), none)
  have fullSteps : phaseSteps left right slots base B C leftValues rightValues =
      1 + (((encodeWord (C + R)).length + 1) + ((encodeWord 0).length + 1 +
      ((C + 1) + (2 * ((encodeWord C).length + 1) +
      (MachineTemplateAddress.phaseSteps right (addressSlots slots) afterLeft B rightValues +
      (((encodeWord L).length + 1) + MachineTemplateAddress.phaseSteps left (addressSlots slots) base B leftValues)))))) := by
    simp only [encodeWord_length]
    dsimp only [phaseSteps, L, R, afterLeft]
    omega
  rw [fullSteps]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (encodeWord (C + R)).length + 1)]
  rw [Function.iterate_add_apply (m := (encodeWord 0).length + 1)]
  rw [Function.iterate_add_apply (m := C + 1)]
  rw [Function.iterate_add_apply (m := 2 * ((encodeWord C).length + 1))]
  rw [Function.iterate_add_apply (m := MachineTemplateAddress.phaseSteps right (addressSlots slots)
    afterLeft B rightValues)]
  rw [Function.iterate_add_apply (m := (encodeWord L).length + 1)]
  rw [leftRun, transferLeft, rightRun, copyRun, addRun, drainRun, transferRight]
  simp only [Function.iterate_one, MachineComposition.advance_some]
  rw [finishRun]
  simp only [MachineFieldTemplate.reset, afterLeft, appended_append]
  simp [edgeBits, encodeWords, L, R, List.append_assoc]

end Execution

omit [DecidableEq K] in
theorem radix_le_magnitude (B : Nat) (values : List Nat) (width M : Nat)
    (hlen : values.length = width) (radixBound : B ≤ M)
    (digitBound : ∀ i, i < width → MachineTemplateAddress.digits values i ≤ M) :
    CanonicalAddress.radix B values ≤ (M + 1) ^ width := by
  have h := MachineHorner.value_le B (MachineTemplateAddress.digits values) values.length M
    radixBound (by simpa only [hlen] using digitBound) values.length (Nat.le_refl _)
  rw [MachineTemplateAddress.hornerValue_eq_radix, hlen] at h
  exact h

theorem phaseSteps_le_timePolynomial (left right : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool) (B C : Nat)
    (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base) (M : Nat)
    (fieldsBound : ∀ j, (base (addressSlots slots (.field j))).length ≤ M)
    (leftWordsBound : (encodeWords leftValues).length ≤ M)
    (rightWordsBound : (encodeWords rightValues).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (leftDigitBound : ∀ i, i < width → MachineTemplateAddress.digits leftValues i ≤ M)
    (rightDigitBound : ∀ i, i < width → MachineTemplateAddress.digits rightValues i ≤ M) :
    phaseSteps left right slots base B C leftValues rightValues ≤
      (timePolynomial left.length right.length width).eval M := by
  have hleft := MachineTemplateAddress.phaseSteps_le_timePolynomial left (addressSlots slots)
    base B leftValues leftLength clean.address M fieldsBound leftWordsBound radixBound leftDigitBound
  have hright := MachineTemplateAddress.phaseSteps_le_timePolynomial right (addressSlots slots)
    (appended slots base (encodeWord (CanonicalAddress.radix B leftValues))) B rightValues
    rightLength (Clean.appended slots base clean _).address M
    (by simpa only [appended_address] using fieldsBound) rightWordsBound radixBound rightDigitBound
  have hlrank := radix_le_magnitude B leftValues width M leftLength radixBound leftDigitBound
  have hrrank := radix_le_magnitude B rightValues width M rightLength radixBound rightDigitBound
  rw [timePolynomial_eval]
  unfold phaseSteps
  omega

end UniqueGamesTheorem.Reduction.MachineAddressEdge

/-! Execute all fixed outcome rows after the existing RHS loader. A single
dispatcher freezes the loaded finite RHS vector into labels. Every row is an
actual address-edge phase; no row-run or whole-loop execution is assumed.
Program definitions contain only fixed templates, literal permutations, and
tape/label placement. Numeric names, radix, and capacity occur only in tapes
and the semantic correctness hypotheses. -/

namespace UniqueGamesTheorem.Reduction.MachineOutcomeRows

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

abbrev LocalLabel (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :=
  MachineAddressEdge.Label row.left.length row.right.length width
    (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))

def localMain (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    LocalLabel slots row :=
  MachineAddressEdge.leftLabel (MachineTemplateAddress.emitLabel
    (MachineFieldTemplate.startAt row.left.length 0))

def localInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (row : Spec q width) (place : LocalLabel slots row → Λ) (exit : Option Λ) :
    LocalLabel slots row → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ) :=
  MachineAddressEdge.instruction row.left row.right row.permutation slots place exit

def payload (B C : Nat) (values : Spec q width → Values width) (row : Spec q width) :
    List Bool :=
  MachineAddressEdge.edgeBits B C (values row).left (values row).right row.permutation

def rowResult (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : K → List Bool :=
  MachineAddressEdge.appended slots base (payload B C values row)

def rowCost (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : Nat :=
  MachineAddressEdge.phaseSteps row.left row.right slots base B C
    (values row).left (values row).right

/-- Exact per-row costs at their actual accumulated output frames. -/
def rowCosts (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) :
    List (Spec q width) → (K → List Bool) → List Nat
  | [], _ => []
  | row :: rows, base => rowCost slots B C values row base ::
      rowCosts slots B C values rows (rowResult slots B C values row base)

structure Invariant (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) : Prop where
  clean : MachineAddressEdge.Clean slots base
  radix : base (MachineAddressEdge.addressSlots slots .radix) = encodeWord B
  capacity : base (MachineAddressEdge.capacityTape slots) = encodeWord C
  correct : ∀ row ∈ rows,
    MachineFieldTemplate.templateOutput row.left
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).left ∧
    MachineFieldTemplate.templateOutput row.right
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).right

theorem Invariant.appended (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) (valid : Invariant slots B C values rows base) (bits : List Bool) :
    Invariant slots B C values rows (MachineAddressEdge.appended slots base bits) := by
  constructor
  · exact MachineAddressEdge.Clean.appended slots base valid.clean bits
  · simpa only [MachineAddressEdge.appended_address] using valid.radix
  · simpa only [MachineAddressEdge.appended_capacity] using valid.capacity
  · intro row hrow
    simpa only [MachineAddressEdge.appended_address] using valid.correct row hrow

theorem appended_nil (slots : MachineAddressEdge.Tape q width ↪ K) (base : K → List Bool) :
    MachineAddressEdge.appended slots base [] = base := by
  simp [MachineAddressEdge.appended, MachineFieldTemplate.outputTapes]

theorem sequence_result (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.resultOf (rowResult slots B C values) rows base =
      MachineAddressEdge.appended slots base (rows.flatMap (payload B C values)) := by
  induction rows generalizing base with
  | nil => simpa only [MachineFiniteSequence.resultOf, List.flatMap_nil] using
      (appended_nil slots base).symm
  | cons row rows ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    exact MachineAddressEdge.appended_append slots base _ _

theorem sequence_steps (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.steps (rowResult slots B C values) (rowCost slots B C values)
      rows base = (rowCosts slots B C values rows base).sum := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih => simp only [MachineFiniteSequence.steps, rowCosts, List.sum_cons, ih]

def sequenceInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) rows place exit

/-- The generic finite-sequence local obligation is discharged by the concrete
edge program, including its address arithmetic and capacity restoration. -/
theorem sequenceTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ))
    (atInstruction : ∀ label, P (place label) = sequenceInstruction slots rows place exit label)
    (base : K → List Bool) (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values rows base) (ambient : σ) :
    (MachineComposition.advance (TM2.step P))^[(rowCosts slots B C values rows base).sum]
      (some ⟨MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) rows place exit,
        ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineAddressEdge.appended slots base (rows.flatMap (payload B C values))⟩ := by
  have h := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) (rowResult slots B C values) (rowCost slots B C values)
    P (Invariant slots B C values rows) (fun _ => ((ambient, ()), none)) id rows
    (by
      intro row _ frame hframe
      exact Invariant.appended slots B C values rows frame hframe (payload B C values row))
    (by
      intro row hrow labels next placement frame hframe
      exact MachineAddressEdge.phaseTrace row.left row.right row.permutation slots
        labels next P placement frame B C (values row).left (values row).right
        (values row).left_length (values row).right_length hframe.clean hframe.radix
        hframe.capacity (hframe.correct row hrow).1 (hframe.correct row hrow).2 ambient none)
    place exit atInstruction base valid
  simpa only [sequence_steps, sequence_result, id_eq] using h

abbrev Label (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :=
  Unit ⊕ (Σ rhs : Rhs k, MachineFiniteSequence.Label (LocalLabel slots) (selected rows rhs))

instance localLabelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    Fintype (LocalLabel slots row) := by unfold LocalLabel; infer_instance

instance localLabelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    DecidableEq (LocalLabel slots row) := by
  letI : DecidableEq (MachineTemplateAddress.Label row.left.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  letI : DecidableEq (MachineTemplateAddress.Label row.right.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  dsimp only [LocalLabel, MachineAddressEdge.Label]
  infer_instance

instance labelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    Fintype (Label slots rows) := by unfold Label; infer_instance

instance labelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    DecidableEq (Label slots rows) := by unfold Label; infer_instance

def sequenceEntry (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k)
    (place : Label slots rows → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) (selected rows rhs)
    (fun label => place (.inr ⟨rhs, label⟩)) exit

/-- Reuse the RHS vector already loaded by `MachineRhsLoad`; dispatch takes
one real transition, and resets only the optional temporary bit. -/
def dispatcher (slots : MachineAddressEdge.Tape q width ↪ K) :
    (rows : List (Row k q width)) → (Label slots rows → Λ) → Option Λ →
      TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | [], _, exit => .load MachineFieldTemplate.reset (MachineFieldTemplate.jump exit)
  | row :: _rows, place, _ => .load MachineFieldTemplate.reset
      (.goto fun state => place (.inr ⟨MachineRhsLoad.rhs state,
        .inl (localMain slots (row (MachineRhsLoad.rhs state)))⟩))

def instruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ) :
    Label slots rows → TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | .inl _ => dispatcher slots rows place exit
  | .inr ⟨rhs, label⟩ => sequenceInstruction slots (selected rows rhs)
      (fun l => place (.inr ⟨rhs, l⟩)) exit label

theorem dispatcherStep (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atDispatcher : P (place (.inl ())) = dispatcher slots rows place exit)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool) :
    TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩ =
      some ⟨sequenceEntry slots rows rhs place exit, (((rhs, ambient), ()), none), base⟩ := by
  change some (TM2.stepAux (P (place (.inl ()))) (((rhs, ambient), ()), register) base) = _
  rw [atDispatcher]
  cases rows with
  | nil => cases exit <;> rfl
  | cons row rows => rfl

theorem phaseTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    (MachineComposition.advance (TM2.step P))^[
      (rowCosts slots B C values (selected rows rhs) base).sum + 1]
      (some ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) =
      some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩ := by
  have first := dispatcherStep slots rows place exit P (atInstruction (.inl ()))
    base rhs ambient register
  have rest := sequenceTrace slots (selected rows rhs) (fun l => place (.inr ⟨rhs, l⟩))
    exit P (fun l => atInstruction (.inr ⟨rhs, l⟩)) base B C values valid (rhs, ambient)
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[_]
    (TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) = _
  rw [first]
  exact rest

def phaseInTime (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩
      (some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩)
      ((rowCosts slots B C values (selected rows rhs) base).sum + 1) where
  steps := (rowCosts slots B C values (selected rows rhs) base).sum + 1
  evals_in_steps := phaseTrace slots rows place exit P atInstruction base rhs ambient register
    B C values valid
  steps_le_m := Nat.le_refl _

theorem rowCosts_sum_le (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum ≤
      ((rows.map (fun row => MachineAddressEdge.timePolynomial
        row.left.length row.right.length width)).sum).eval M := by
  induction rows generalizing base with
  | nil => simp [rowCosts]
  | cons row rows ih =>
    have bounds := valuesBound row (by simp)
    have first := MachineAddressEdge.phaseSteps_le_timePolynomial row.left row.right
      slots base B C (values row).left (values row).right
      (values row).left_length (values row).right_length clean M fieldsBound
      bounds.1 bounds.2.1 radixBound capacityBound bounds.2.2.1 bounds.2.2.2
    have rest := ih (rowResult slots B C values row base)
      (MachineAddressEdge.Clean.appended slots base clean (payload B C values row))
      (by simpa only [rowResult, MachineAddressEdge.appended_address] using fieldsBound)
      (fun r hr => valuesBound r (List.mem_cons_of_mem row hr))
    simpa only [rowCosts, List.sum_cons, List.map_cons, Polynomial.eval_add, rowCost] using
      Nat.add_le_add first rest

/-- The actual dispatcher-and-rows count is bounded by a fixed polynomial in
explicit tape and digit magnitudes, using the checked edge arithmetic bound. -/
theorem phaseCost_le_timePolynomial (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum + 1 ≤ (timePolynomial rows).eval M := by
  have h := rowCosts_sum_le slots rows base B C values M clean fieldsBound
    radixBound capacityBound valuesBound
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one] using
    Nat.add_le_add_right h 1

end UniqueGamesTheorem.Reduction.MachineOutcomeRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHeaderCounts
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

noncomputable section

namespace Eval

open CookLevin.PolynomialMachine

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (p : Polynomial Nat) := Unit ⊕ (MachineHorner.Label (width p) ⊕ Unit)

def start (p : Polynomial Nat) : Label p := .inl ()
def inner (p : Polynomial Nat) (l : MachineHorner.Label (width p)) : Label p := .inr (.inl l)
def finish (p : Polynomial Nat) : Label p := .inr (.inr ())

def word (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K) : K → List Bool :=
  Function.extend slots (fieldWord p) (fun _ => [])

def indices (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K) : List K :=
  (fieldIndices p).map slots

omit [DecidableEq K] in
theorem indices_nodup (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K) :
    (indices p slots).Nodup := (fieldIndices_nodup p).map slots.injective

omit [DecidableEq K] in
@[simp] theorem word_slot (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (i : MachineHorner.Layout (width p)) : word p slots (slots i) = fieldWord p i :=
  slots.injective.extend_apply _ _ i

omit [DecidableEq K] in
@[simp] theorem control_not_mem (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (i : Fin 6) :
    slots (.inl i) ∉ indices p slots := by
  simp [indices, slots.injective.eq_iff]

omit [DecidableEq K] in
@[simp] theorem digit_mem (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (i : Fin (width p)) :
    slots (.inr i) ∈ indices p slots := by
  simp [indices, slots.injective.eq_iff]

def prepared (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (base : K → List Bool) : K → List Bool :=
  prependFieldsTapes (word p slots) (indices p slots) base

@[simp] theorem prepared_control (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (base : K → List Bool) (i : Fin 6) :
    prepared p slots base (slots (.inl i)) = base (slots (.inl i)) := by
  rw [prepared, prependFieldsTapes_apply _ _ (indices_nodup p slots)]
  simp

@[simp] theorem prepared_digit (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (base : K → List Bool)
    (i : Fin (width p)) (hi : base (slots (.inr i)) = []) :
    prepared p slots base (slots (.inr i)) = encodeWord (digit p i.val) := by
  rw [prepared, prependFieldsTapes_apply _ _ (indices_nodup p slots)]
  simp [fieldWord, hi]

theorem clear_result (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (base : K → List Bool) (result : Nat)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = []) :
    clearFieldsTapes (fun k => (word p slots k).length) (indices p slots)
      (MachineHorner.resultTapes slots (prepared p slots base) result) =
      MachineHorner.resultTapes slots base result := by
  funext k
  rw [clearFieldsTapes_apply _ _ (indices_nodup p slots)]
  by_cases h : k ∈ indices p slots
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp [MachineHorner.resultTapes, slots.injective.eq_iff, prepared_digit,
      fieldWord, hcoeff]
  · by_cases hd : k = slots (.inl 3)
    · subst k
      simp [MachineHorner.resultTapes]
    · simp [h, MachineHorner.resultTapes, hd, prepared,
        prependFieldsTapes_apply _ _ (indices_nodup p slots)]

def statement (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ) :
    Label p → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl _ => prependFields (word p slots) (indices p slots)
      (.goto fun _ => labels (inner p .start))
  | .inr (.inl l) => MachineHorner.statement slots (fun l => labels (inner p l))
      (some (labels (finish p))) l
  | .inr (.inr _) => clearFields (fun k => (word p slots k).length) (indices p slots)
      (Reduction.MachineTransfer.exitAt (slots (.inl 3)) exit)

def steps (p : Polynomial Nat) (n : Nat) : Nat :=
  MachineHorner.steps n (digit p) (width p) + 2

theorem trace (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement p slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl 0)) = encodeWord n)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps p n]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
  have hp : (advance (TM2.step program))^[1]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (inner p .start)), ((ambient, ()), register), prepared p slots base⟩ := by
    change some (TM2.stepAux (program (labels (start p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (prependFields _ _ _) _ _) = _
    rw [stepAux_prependFields]
    rfl
  have hh := MachineHorner.hornerTrace slots (fun l => labels (inner p l))
    (some (labels (finish p))) program (fun l => atLabels (inner p l))
    (prepared p slots base) n (digit p) (by simpa using hinput)
    (fun i => prepared_digit p slots base i (hcoeff i))
    (by
      constructor
      · simpa using clean.accA
      · simpa using clean.accB
      · simpa using clean.counter
      · simpa using clean.scratch) ambient register
  rw [hornerValue_eq_eval] at hh
  have hc : (advance (TM2.step program))^[1]
      (some ⟨some (labels (finish p)), ((ambient, ()), none),
        MachineHorner.resultTapes slots (prepared p slots base) (p.eval n)⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
    change some (TM2.stepAux (program (labels (finish p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (clearFields _ _ _) _ _) = _
    rw [stepAux_clearFields, clear_result p slots base _ hcoeff]
    cases exit <;> rfl
  rw [show steps p n = 1 + (MachineHorner.steps n (digit p) (width p) + 1) by
    unfold steps; omega, Function.iterate_add_apply, Function.iterate_add_apply, hp, hh, hc]

end Eval

def occurrenceValue (u D m : Nat) : Nat :=
  3 ^ u * (SourceOccurrences.testTapeEncoding u D).size * m ^ u

def polynomial (u D : Nat) : Kind → Polynomial Nat
  | .left => Polynomial.C (2 ^ (2 ^ u)) * Polynomial.X ^ u
  | .right => Polynomial.C (2 ^ (8 ^ u)) * Polynomial.X ^ u
  | .occurrences => Polynomial.C (3 ^ u * (SourceOccurrences.testTapeEncoding u D).size) *
      Polynomial.X ^ u

@[simp] theorem polynomial_left_eval (u D n : Nat) :
    (polynomial u D .left).eval n = leftValue u n := by simp [polynomial, leftValue]
@[simp] theorem polynomial_right_eval (u D m : Nat) :
    (polynomial u D .right).eval m = rightValue u m := by simp [polynomial, rightValue]
@[simp] theorem polynomial_occurrences_eval (u D m : Nat) :
    (polynomial u D .occurrences).eval m = occurrenceValue u D m := by
  simp [polynomial, occurrenceValue]

abbrev Coefficients (u D : Nat) :=
  Fin (CookLevin.PolynomialMachine.width (polynomial u D .left)) ⊕
    (Fin (CookLevin.PolynomialMachine.width (polynomial u D .right)) ⊕
      Fin (CookLevin.PolynomialMachine.width (polynomial u D .occurrences)))

abbrev Layout (u D : Nat) := Control ⊕ Coefficients u D

def coefficientBlock (u D : Nat) (kind : Kind) :
    Fin (CookLevin.PolynomialMachine.width (polynomial u D kind)) ↪ Coefficients u D :=
  match kind with
  | .left => ⟨Sum.inl, Sum.inl_injective⟩
  | .right => ⟨fun i => .inr (.inl i), Sum.inr_injective.comp Sum.inl_injective⟩
  | .occurrences => ⟨fun i => .inr (.inr i), Sum.inr_injective.comp Sum.inr_injective⟩

def inputControl : Kind → Control
  | .left => .variableCount | _ => .clauseCount

def outputControl : Kind → Control
  | .left => .leftBlockSize | .right => .rightTemporary | .occurrences => .occurrenceCount

def controlSlots (kind : Kind) : Fin 6 ↪ Control where
  toFun i := match i.val with
    | 0 => inputControl kind | 1 => .accA | 2 => .accB
    | 3 => outputControl kind | 4 => .counter | _ => .scratch
  inj' := by
    intro i j h
    cases kind <;> fin_cases i <;> fin_cases j <;> cases h <;> rfl

def localSlots (u D : Nat) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial u D kind)) ↪ Layout u D where
  toFun
    | .inl i => .inl (controlSlots kind i)
    | .inr i => .inr (coefficientBlock u D kind i)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((controlSlots kind).injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr ((coefficientBlock u D kind).injective (Sum.inr.inj h))

variable {u D : Nat} {K Λ σ : Type}

def control (slots : Layout u D ↪ K) (c : Control) : K := slots (.inl c)

def evalSlots (slots : Layout u D ↪ K) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial u D kind)) ↪ K :=
  (localSlots u D kind).trans slots

@[simp] theorem evalSlots_radix (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 0) = control slots (inputControl kind) := rfl
@[simp] theorem evalSlots_accA (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 1) = control slots .accA := rfl
@[simp] theorem evalSlots_accB (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 2) = control slots .accB := rfl
@[simp] theorem evalSlots_destination (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 3) = control slots (outputControl kind) := rfl
@[simp] theorem evalSlots_counter (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 4) = control slots .counter := rfl
@[simp] theorem evalSlots_scratch (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 5) = control slots .scratch := rfl
@[simp] theorem evalSlots_digit (slots : Layout u D ↪ K) (kind : Kind)
    (i : Fin (CookLevin.PolynomialMachine.width (polynomial u D kind))) :
    evalSlots slots kind (.inr i) = slots (.inr (coefficientBlock u D kind i)) := rfl

@[simp] theorem control_eq_iff (slots : Layout u D ↪ K) (a b : Control) :
    control slots a = control slots b ↔ a = b := by
  simp [control, slots.injective.eq_iff]

variable [DecidableEq K]

def resultTapes (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (control slots .leftBlockSize) (encodeWord (leftValue u n)))
    (control slots .occurrenceCount) (encodeWord (occurrenceValue u D m)))
    (control slots .dummyIndex) (encodeWord (dummyValue u n m)))
    (control slots .bitCount) (encodeWord (bitValue u n m))

@[simp] theorem result_left (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .leftBlockSize) = encodeWord (leftValue u n) := by
  simp [resultTapes]
@[simp] theorem result_occurrences (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .occurrenceCount) = encodeWord (occurrenceValue u D m) := by
  simp [resultTapes]
@[simp] theorem result_dummy (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .dummyIndex) = encodeWord (dummyValue u n m) := by
  simp [resultTapes]
@[simp] theorem result_bits (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .bitCount) = encodeWord (bitValue u n m) := by
  simp [resultTapes]

end

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_CloneMachineModelLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.CloneMachineModel

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

end UniqueGamesTheorem.Reduction.CloneMachineModel

end

section

/-!
# Affine word emission in the actual clone-table machine

The shared machine keeps its context fixed while copying one saved word. Its
finite transducer therefore acts by a fixed symbol substitution. The lemmas
below identify that substitution with the established unary encoding of
`offset + scale * value`, including all header and equation-field contexts.
Scale, offset, and the triple-table length remain symbolic.
-/

namespace UniqueGamesTheorem.Reduction.CloneMachineAffine

open UniqueGamesTheorem.Foundations.Complexity
open CloneMachineModel

theorem affineEmit_replicate_true (scale offset v : Nat) :
    (List.replicate v true).flatMap (affineEmit scale offset) =
      List.replicate (scale * v) true := by
  rw [List.flatMap_replicate]
  change (List.replicate v (List.replicate scale true)).flatten = _
  rw [List.flatten_replicate_replicate, Nat.mul_comm v scale]

/-- This includes zero scale and zero offset, with no positivity assumptions. -/
theorem affineEmit_word (scale offset v : Nat) :
    (encodeWord v).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) := by
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, affineEmit_replicate_true, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * v) offset]

end UniqueGamesTheorem.Reduction.CloneMachineAffine

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineAddressHeaders
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Reduction.MachineAddressHeaders

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineComposition

namespace Prefix

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .copyOut => MachineTransfer.loopAt (slots 0) (slots 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (slots 4) (slots 0) (slots 1) false
      (labels .copyBack) (some (labels (readStart 0)))
  | .read slot => if slot.1.val < 2 then
      if slot.2 then SourceMachine.fieldLoop (slots 1) (destination slots slot.1.val)
        (labels (.read (slot.1, true))) (some (labels (readStart (slot.1.val + 1))))
      else SourceMachine.fieldStart (destination slots slot.1.val) (labels (.read (slot.1, true)))
    else SourceFieldArray.finish (slots 1) (some (labels .clear))
  | .clear => MachineDrain.drain (slots 1) (labels .clear) exit

omit [DecidableEq K] in
theorem atReadStart (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (r : Nat) (hr : r < 2) :
    statement (σ := σ) slots labels exit (readStart r) =
      SourceMachine.fieldStart (destination slots r) (labels (readLoop r)) := by
  simp [statement, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem atReadLoop (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (r : Nat) (hr : r < 2) :
    statement (σ := σ) slots labels exit (readLoop r) =
      SourceMachine.fieldLoop (slots 1) (destination slots r) (labels (readLoop r))
        (some (labels (readStart (r + 1)))) := by
  simp [statement, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem atReadDone (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    statement (σ := σ) slots labels exit (readStart 2) =
      SourceFieldArray.finish (slots 1) (some (labels .clear)) := by
  simp [statement, readStart]

def readTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat)
    (suffix : List Bool) : K → List Bool :=
  SourceFieldArray.sequenceTapes (slots 1) (destination slots) (copied slots base)
    0 [n, m] suffix

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base (slots 1) [])
    (slots 2) (encodeWord n ++ base (slots 2))) (slots 3) (encodeWord m ++ base (slots 3))

theorem clear_readTapes (slots : Fin 5 ↪ K) (base : K → List Bool)
    (n m : Nat) (suffix : List Bool) :
    Function.update (readTapes slots base n m suffix) (slots 1) [] =
      resultTapes slots base n m := by
  funext tape
  by_cases hw : tape = slots 1
  · subst tape
    simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
      SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
  · by_cases hn : tape = slots 2
    · subst tape
      simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
        SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
    · by_cases hm : tape = slots 3
      · subst tape
        simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
          SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
      · simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
          SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff, hw, hn, hm]

theorem readTapes_work (slots : Fin 5 ↪ K) (base : K → List Bool)
    (n m : Nat) (suffix : List Bool) : readTapes slots base n m suffix (slots 1) = suffix := by
  simp [readTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
    SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff, encodeWords]

theorem resultTapes_other (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat)
    (tape : K) (hw : tape ≠ slots 1) (hn : tape ≠ slots 2) (hm : tape ≠ slots 3) :
    resultTapes slots base n m tape = base tape := by simp [resultTapes, hw, hn, hm]

@[simp] theorem resultTapes_source (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 0) = base (slots 0) := by
  simp [resultTapes, slots.injective.eq_iff]

@[simp] theorem resultTapes_work (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 1) = [] := by simp [resultTapes]

@[simp] theorem resultTapes_n (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 2) = encodeWord n ++ base (slots 2) := by
  simp [resultTapes, slots.injective.eq_iff]

@[simp] theorem resultTapes_m (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 3) = encodeWord m ++ base (slots 3) := by
  simp [resultTapes]

/-- Actual copying, two-field extraction, and complete disposal of the work copy. -/
def inTime (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base (slots 0) = encodeWords [n, m] ++ suffix)
    (hwork : base (slots 1) = []) (hscratch : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyOut), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (3 * (base (slots 0)).length + 6) := by
  have copying := MachineCopy.copyInTime (slots 0) (slots 1) (slots 4)
    (by simp [slots.injective.eq_iff]) (by simp [slots.injective.eq_iff])
    (by simp [slots.injective.eq_iff]) false (labels .copyOut) (labels .copyBack)
    (some (labels (readStart 0))) program (atLabels .copyOut) (atLabels .copyBack)
    base hscratch (ambient, ()) register
  have hc : Function.update base (slots 1) (base (slots 0) ++ base (slots 1)) =
      copied slots base := by simp [copied, hwork]
  rw [hc] at copying
  have reading := SourceFieldArray.sequenceInTime (slots 1) (destination slots)
    (fun r => labels (readStart r)) (fun r => labels (readLoop r)) (some (labels .clear))
    program (copied slots base) 0 [n, m] suffix
    (by
      intro r hr
      simp only [destination]
      split <;> simp [slots.injective.eq_iff])
    (by
      intro r hr
      simpa only [Nat.zero_add] using
        (atLabels (readStart r)).trans (atReadStart slots labels exit r (by simpa using hr)))
    (by
      intro r hr
      simpa only [Nat.zero_add] using
        (atLabels (readLoop r)).trans (atReadLoop slots labels exit r (by simpa using hr)))
    (by simpa using (atLabels (readStart 2)).trans (atReadDone slots labels exit))
    (by simp [copied, hinput]) (ambient, ()) none
  have draining := MachineDrain.drainInTime (slots 1) (labels .clear) exit program
    (atLabels .clear) (readTapes slots base n m suffix) (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copying reading) draining
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [clear_readTapes] using joined.evals_in_steps
  · apply Nat.le_trans joined.steps_le_m
    rw [readTapes_work, hinput]
    simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    omega

end Prefix

noncomputable section

namespace Arithmetic

abbrev Coefficients (k s d noiseCount : Nat) :=
  Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount .capacity)) ⊕
    Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount .edges))

abbrev Layout (k s d noiseCount : Nat) := Control ⊕ Coefficients k s d noiseCount

def coefficientBlock (k s d noiseCount : Nat) (kind : Kind) :
    Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind)) ↪
      Coefficients k s d noiseCount :=
  match kind with
  | .capacity => ⟨Sum.inl, Sum.inl_injective⟩
  | .edges => ⟨Sum.inr, Sum.inr_injective⟩

def localSlots (k s d noiseCount : Nat) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind)) ↪
      Layout k s d noiseCount where
  toFun
    | .inl i => .inl (controlSlots kind i)
    | .inr i => .inr (coefficientBlock k s d noiseCount kind i)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((controlSlots kind).injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b =>
        exact congrArg Sum.inr ((coefficientBlock k s d noiseCount kind).injective (Sum.inr.inj h))

variable {k s d noiseCount : Nat} {K Λ σ : Type}

def control (slots : Layout k s d noiseCount ↪ K) (c : Control) : K := slots (.inl c)

def evalSlots (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind)) ↪ K :=
  (localSlots k s d noiseCount kind).trans slots

@[simp] theorem control_eq_iff (slots : Layout k s d noiseCount ↪ K) (a b : Control) :
    control slots a = control slots b ↔ a = b := by simp [control, slots.injective.eq_iff]

@[simp] theorem evalSlots_radix (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 0) = control slots (inputControl kind) := rfl
@[simp] theorem evalSlots_accA (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 1) = control slots .accA := rfl
@[simp] theorem evalSlots_accB (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 2) = control slots .accB := rfl
@[simp] theorem evalSlots_destination (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 3) = control slots (outputControl kind) := rfl
@[simp] theorem evalSlots_counter (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 4) = control slots .counter := rfl
@[simp] theorem evalSlots_scratch (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 5) = control slots .scratch := rfl
@[simp] theorem evalSlots_digit (slots : Layout k s d noiseCount ↪ K) (kind : Kind)
    (i : Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind))) :
    evalSlots slots kind (.inr i) = slots (.inr (coefficientBlock k s d noiseCount kind i)) := rfl

inductive Label (k s d noiseCount : Nat)
  | copyNOut | copyNBack | copyMOut | copyMBack | addM | seedBase
  | evaluate (kind : Kind) (localLabel : SourceHeaderCounts.Eval.Label (polynomial k s d noiseCount kind))
  | doubleScan | doubleEmit (symbol : Bool) | doubleRestore | alphabet | edgeTransfer
  deriving DecidableEq, Fintype

def evalStart (kind : Kind) : Label k s d noiseCount :=
  .evaluate kind (SourceHeaderCounts.Eval.start (polynomial k s d noiseCount kind))

def afterEval : Kind → Label k s d noiseCount
  | .capacity => .doubleScan | .edges => .edgeTransfer

variable [DecidableEq K]

/-- The fixed arithmetic program never captures input counts in its code. -/
def statement (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ) :
    Label k s d noiseCount → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .copyNOut => MachineTransfer.loopAt (control slots .variableCount) (control slots .scratch)
      id false (labels .copyNOut) (some (labels .copyNBack))
  | .copyNBack => MachineCopy.forkLoop (control slots .scratch) (control slots .variableCount)
      (control slots .baseValue) false (labels .copyNBack) (some (labels .copyMOut))
  | .copyMOut => MachineTransfer.loopAt (control slots .occurrenceCount) (control slots .scratch)
      id false (labels .copyMOut) (some (labels .copyMBack))
  | .copyMBack => MachineCopy.forkLoop (control slots .scratch) (control slots .occurrenceCount)
      (control slots .temporary) false (labels .copyMBack) (some (labels .addM))
  | .addM => MachineUnaryAddAt.loop (control slots .temporary) (control slots .baseValue)
      (labels .addM) (some (labels .seedBase))
  | .seedBase => .pop (control slots .temporary) (fun state _ => state)
      (MachineSubstitution.pushWord (control slots .baseValue) (List.replicate (baseConstant s d) true)
        (.goto fun _ => labels (evalStart .capacity)))
  | .evaluate kind localLabel => SourceHeaderCounts.Eval.statement
      (polynomial k s d noiseCount kind) (evalSlots slots kind)
      (fun label => labels (.evaluate kind label)) (some (labels (afterEval kind))) localLabel
  | .doubleScan => MachineTransducerCopy.scanLoop (control slots .capacity) (control slots .scratch)
      () (fun _ symbol => labels (.doubleEmit symbol)) (labels .doubleRestore)
  | .doubleEmit symbol => MachineTransducerCopy.emitter (control slots .reversed)
      (fun q _ => q) (fun _ : Unit => CloneMachineModel.affineEmit 2 0)
      (labels .doubleScan) () symbol
  | .doubleRestore => MachineTransfer.loopAt (control slots .scratch) (control slots .capacity)
      id false (labels .doubleRestore) (some (labels .alphabet))
  | .alphabet => MachineSubstitution.pushWord (control slots .reversed) (encodeWord (2 ^ s))
      (.goto fun _ => labels (evalStart .edges))
  | .edgeTransfer => MachineTransfer.loopAt (control slots .temporary) (control slots .reversed)
      id false (labels .edgeTransfer) exit

structure WorkClean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop where
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients k s d noiseCount, base (slots (.inr i)) = []

structure Clean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop
    extends WorkClean slots base where
  baseValue : base (control slots .baseValue) = []
  capacity : base (control slots .capacity) = []
  temporary : base (control slots .temporary) = []

theorem WorkClean.update_control {slots : Layout k s d noiseCount ↪ K} {base : K → List Bool}
    (clean : WorkClean slots base) (c : Control)
    (other : c ≠ .accA ∧ c ≠ .accB ∧ c ≠ .counter ∧ c ≠ .scratch) (word : List Bool) :
    WorkClean slots (Function.update base (control slots c) word) := by
  constructor
  · simpa [other.1.symm] using clean.accA
  · simpa [other.2.1.symm] using clean.accB
  · simpa [other.2.2.1.symm] using clean.counter
  · simpa [other.2.2.2.symm] using clean.scratch
  · intro i
    simpa [control, slots.injective.eq_iff] using clean.coefficients i

/-- One placed invocation of the already checked preserving polynomial evaluator. -/
theorem evalPhaseTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (kind : Kind) (base : K → List Bool) (value : Nat)
    (hinput : base (control slots (inputControl kind)) = encodeWord value)
    (hdest : base (control slots (outputControl kind)) = [])
    (clean : WorkClean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount kind) value]
      (some ⟨some (labels (evalStart kind)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (afterEval kind)), ((ambient, ()), none),
        Function.update base (control slots (outputControl kind))
          (encodeWord ((polynomial k s d noiseCount kind).eval value))⟩ := by
  have evaluated := SourceHeaderCounts.Eval.trace (polynomial k s d noiseCount kind)
    (evalSlots slots kind) (fun label => labels (.evaluate kind label))
    (some (labels (afterEval kind))) program (fun label => atLabels (.evaluate kind label))
    base value (by simpa using hinput)
    (fun i => by simpa using clean.coefficients (coefficientBlock k s d noiseCount kind i))
    ⟨by simpa using clean.accA, by simpa using clean.accB,
      by simpa using clean.counter, by simpa using clean.scratch⟩ ambient register
  simpa only [evalStart, MachineHorner.resultTapes, evalSlots_destination, hdest, List.append_nil]
    using evaluated

def resultTapes (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base
    (control slots .baseValue) (encodeWord (radix s d n m)))
    (control slots .capacity) (encodeWord (capacity k s d n m)))
    (control slots .reversed) ((headerBits k s d noiseCount n m).reverse ++ base (control slots .reversed))

def steps (k s d noiseCount n m : Nat) : Nat :=
  2 * n + 3 * m + 10 +
    SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .capacity) (radix s d n m) +
    SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .edges) m +
    3 * capacity k s d n m + edgeCount k s d noiseCount m + 8

def preparedBase (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Function.update base (control slots .baseValue) (encodeWord (radix s d n m))

/-- Copies preserve both operands; addition consumes only the temporary copy. -/
theorem prepareBaseTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * n + 3 * m + 10]
      (some ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none),
        preparedBase slots base n m⟩ := by
  let t1 := Function.update base (control slots .baseValue) (encodeWord n)
  let t2 := Function.update t1 (control slots .temporary) (encodeWord m)
  let t3 := Function.update (Function.update t2 (control slots .temporary) [false])
    (control slots .baseValue) (encodeWord (m + n))
  let t4 := Function.update (Function.update t3 (control slots .temporary) [])
    (control slots .baseValue) (encodeWord (radix s d n m))
  have copyingN := MachineCopy.copyTrace (control slots .variableCount)
    (control slots .baseValue) (control slots .scratch) (by simp) (by simp) (by simp)
    false (labels .copyNOut) (labels .copyNBack) (some (labels .copyMOut)) program
    (atLabels .copyNOut) (atLabels .copyNBack) base clean.scratch (ambient, ()) register
  rw [hn, clean.baseValue, List.append_nil, encodeWord_length] at copyingN
  have copyingM := MachineCopy.copyTrace (control slots .occurrenceCount)
    (control slots .temporary) (control slots .scratch) (by simp) (by simp) (by simp)
    false (labels .copyMOut) (labels .copyMBack) (some (labels .addM)) program
    (atLabels .copyMOut) (atLabels .copyMBack) t1
    (by simpa [t1] using clean.scratch) (ambient, ()) none
  have hm1 : t1 (control slots .occurrenceCount) = encodeWord m := by simpa [t1] using hm
  have ht1 : t1 (control slots .temporary) = [] := by simpa [t1] using clean.temporary
  rw [hm1, ht1, List.append_nil, encodeWord_length] at copyingM
  have adding := MachineUnaryAddAt.addFromTapes (control slots .temporary)
    (control slots .baseValue) (by simp) (labels .addM) (some (labels .seedBase)) program
    (atLabels .addM) t2 m n [] [] (by simp [t2]) (by simp [t2, t1]) (ambient, ()) none
  have added : MachineUnaryAddAt.unaryTapes (control slots .temporary)
      (control slots .baseValue) t2 0 (m + n) [] [] = t3 := by
    simp [MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, t3, encodeWord]
  rw [added] at adding
  have seeding : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seedBase), ((ambient, ()), none), t3⟩) =
      some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none), t4⟩ := by
    change some (TM2.stepAux (program (labels .seedBase)) _ _) = _
    rw [atLabels]
    simp only [statement, TM2.stepAux]
    have htemp : t3 (control slots .temporary) = [false] := by simp [t3]
    rw [htemp]
    simp only [List.tail_cons]
    rw [MachineSubstitution.stepAux_pushWord]
    simp only [TM2.stepAux]
    have different : control slots .baseValue ≠ control slots .temporary := by simp
    rw [Function.update_of_ne different]
    have hbase : t3 (control slots .baseValue) = encodeWord (m + n) := by simp [t3]
    rw [hbase]
    have wordEq : (List.replicate (baseConstant s d) true).reverse ++ encodeWord (m + n) =
        encodeWord (radix s d n m) := by
      simp [encodeWord, List.reverse_replicate, ← List.append_assoc,
        List.replicate_append_replicate, radix, Nat.add_comm, Nat.add_assoc]
    rw [wordEq]
  have combined := trace_trans _ (trace_trans _ (trace_trans _ copyingN copyingM) adding) seeding
  have timeEq : 2 * (n + 1 + 1) + 2 * (m + 1 + 1) + (m + 1) + 1 =
      2 * n + 3 * m + 10 := by omega
  rw [timeEq] at combined
  have frame : t4 = preparedBase slots base n m := by
    funext tape
    by_cases ht : tape = control slots .temporary
    · subst tape
      simp [t4, t3, t2, t1, preparedBase, clean.temporary]
    · simp [t4, t3, t2, t1, preparedBase, Function.update_apply, ht]
      split_ifs <;> rfl
  rw [frame] at combined
  exact combined

/-- Physical doubling emits the vertex-count word and restores the capacity. -/
theorem doubleTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (value : Nat)
    (hcap : base (control slots .capacity) = encodeWord value)
    (hscratch : base (control slots .scratch) = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[3 * value + 5]
      (some ⟨some (labels .doubleScan), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .alphabet), ((ambient, ()), none),
        Function.update base (control slots .reversed)
          ((encodeWord (2 * value)).reverse ++ base (control slots .reversed))⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace (control slots .capacity)
    (control slots .scratch) (control slots .reversed) (by simp) (by simp) (by simp)
    () (fun q _ => q) (fun _ : Unit => CloneMachineModel.affineEmit 2 0)
    (labels .doubleScan) (labels .doubleRestore) (fun _ symbol => labels (.doubleEmit symbol))
    (some (labels .alphabet)) program (atLabels .doubleScan)
    (by intro q symbol; cases q; exact atLabels (.doubleEmit symbol))
    (atLabels .doubleRestore) base hscratch ambient () register
  rw [hcap, CloneMachineAffine.output_eq_flatMap, CloneMachineAffine.affineEmit_word,
    Nat.zero_add, encodeWord_length] at copied
  have timeEq : 3 * (value + 1) + 2 = 3 * value + 5 := by omega
  rw [timeEq] at copied
  exact copied

/-- All arithmetic and header emission, with exact composed transition count. -/
theorem trace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps k s d noiseCount n m]
      (some ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩ := by
  let t1 := preparedBase slots base n m
  let t2 := Function.update t1 (control slots .capacity) (encodeWord (capacity k s d n m))
  let t3 := Function.update t2 (control slots .reversed)
    ((encodeWord (2 * capacity k s d n m)).reverse ++ t2 (control slots .reversed))
  let t4 := Function.update t3 (control slots .reversed)
    ((encodeWord (2 ^ s)).reverse ++ t3 (control slots .reversed))
  let t5 := Function.update t4 (control slots .temporary) (encodeWord (edgeCount k s d noiseCount m))
  have prepared := prepareBaseTrace slots labels exit program atLabels base n m hn hm clean ambient register
  have cw1 : WorkClean slots t1 := clean.toWorkClean.update_control .baseValue (by decide) _
  have evaluatedCap := evalPhaseTrace slots labels exit program atLabels .capacity t1 (radix s d n m)
    (by simp [t1, preparedBase, inputControl])
    (by simpa [t1, preparedBase, outputControl] using clean.capacity) cw1 ambient none
  simp only [polynomial_capacity_eval] at evaluatedCap
  change (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps
      (polynomial k s d noiseCount .capacity) (radix s d n m)]
    (some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none), t1⟩) =
    some ⟨some (labels .doubleScan), ((ambient, ()), none), t2⟩ at evaluatedCap
  have cw2 : WorkClean slots t2 := cw1.update_control .capacity (by decide) _
  have doubled := doubleTrace slots labels exit program atLabels t2 (capacity k s d n m)
    (by simp [t2]) cw2.scratch ambient none
  have alphabetStep : (advance (TM2.step program))^[1]
      (some ⟨some (labels .alphabet), ((ambient, ()), none), t3⟩) =
      some ⟨some (labels (evalStart .edges)), ((ambient, ()), none), t4⟩ := by
    change some (TM2.stepAux (program (labels .alphabet)) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (MachineSubstitution.pushWord _ _ _) _ _) = _
    rw [MachineSubstitution.stepAux_pushWord]
    rfl
  have cw3 : WorkClean slots t3 := cw2.update_control .reversed (by decide) _
  have cw4 : WorkClean slots t4 := cw3.update_control .reversed (by decide) _
  have evaluatedEdges := evalPhaseTrace slots labels exit program atLabels .edges t4 m
    (by simpa [t4, t3, t2, t1, preparedBase, inputControl] using hm)
    (by simpa [t4, t3, t2, t1, preparedBase, outputControl] using clean.temporary)
    cw4 ambient none
  simp only [polynomial_edges_eval] at evaluatedEdges
  change (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps
      (polynomial k s d noiseCount .edges) m]
    (some ⟨some (labels (evalStart .edges)), ((ambient, ()), none), t4⟩) =
    some ⟨some (labels .edgeTransfer), ((ambient, ()), none), t5⟩ at evaluatedEdges
  have transferred := MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
    (σ := σ × Unit) (control slots .temporary)
    (control slots .reversed) (by simp) id false (labels .edgeTransfer) exit program
    (atLabels .edgeTransfer) t5 (ambient, ()) none
  change (advance (TM2.step program))^[(t5 (control slots .temporary)).length + 1]
    (some ⟨some (labels .edgeTransfer), ((ambient, ()), none), t5⟩) = _ at transferred
  have ht5 : t5 (control slots .temporary) = encodeWord (edgeCount k s d noiseCount m) := by simp [t5]
  rw [ht5, encodeWord_length] at transferred
  simp only [List.map_id] at transferred
  have combined := trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ prepared evaluatedCap) doubled) alphabetStep) evaluatedEdges) transferred
  have timeEq : 2 * n + 3 * m + 10 +
      SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .capacity) (radix s d n m) +
      (3 * capacity k s d n m + 5) + 1 +
      SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .edges) m +
      (edgeCount k s d noiseCount m + 1 + 1) = steps k s d noiseCount n m := by
    unfold steps
    omega
  rw [timeEq] at combined
  have frame : MachineTransfer.tapesAt (control slots .temporary) (control slots .reversed)
      t5 [] ((encodeWord (edgeCount k s d noiseCount m)).reverse ++ t5 (control slots .reversed)) =
      resultTapes slots base n m := by
    funext tape
    by_cases ht : tape = control slots .temporary
    · subst tape
      simp [MachineTransfer.tapesAt, resultTapes, clean.temporary]
    · simp [MachineTransfer.tapesAt, t5, t4, t3, t2, t1, preparedBase, resultTapes,
        headerBits, encodeWords, List.reverse_append, List.append_assoc, Function.update_apply, ht]
      split_ifs <;> rfl
  rw [frame] at combined
  exact combined

def inTime (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (steps k s d noiseCount n m) where
  steps := steps k s d noiseCount n m
  evals_in_steps := trace slots labels exit program atLabels base n m hn hm clean ambient register
  steps_le_m := Nat.le_refl _

/-- A fixed polynomial in the serialized input length bounds actual steps. -/
def timePolynomial (k s d noiseCount : Nat) : Polynomial Nat :=
  let B : Polynomial Nat := Polynomial.C 2 * Polynomial.X + Polynomial.C (baseConstant s d)
  (CookLevin.PolynomialMachine.timePolynomial (polynomial k s d noiseCount .capacity)).comp B +
    CookLevin.PolynomialMachine.timePolynomial (polynomial k s d noiseCount .edges) +
    Polynomial.C 3 * (polynomial k s d noiseCount .capacity).comp B +
    polynomial k s d noiseCount .edges + Polynomial.C 5 * Polynomial.X + Polynomial.C 18

theorem steps_le_timePolynomial (k s d noiseCount n m L : Nat) (hn : n ≤ L) (hm : m ≤ L) :
    steps k s d noiseCount n m ≤ (timePolynomial k s d noiseCount).eval L := by
  have hB : radix s d n m ≤ 2 * L + baseConstant s d := by unfold radix; omega
  have hEval (p : Polynomial Nat) (a b : Nat) (hab : a ≤ b) :
      SourceHeaderCounts.Eval.steps p a ≤ (CookLevin.PolynomialMachine.timePolynomial p).eval b := by
    apply Nat.le_trans (m := (CookLevin.PolynomialMachine.timePolynomial p).eval a)
    · rw [CookLevin.PolynomialMachine.timePolynomial_eval]
      unfold SourceHeaderCounts.Eval.steps
      omega
    · exact natPolynomial_eval_mono _ hab
  have h1 := hEval (polynomial k s d noiseCount .capacity) _ _ hB
  have h2 := hEval (polynomial k s d noiseCount .edges) _ _ hm
  have hc : capacity k s d n m ≤ (2 * L + baseConstant s d) ^ (1 + 9 * k) :=
    Nat.pow_le_pow_left hB _
  have he : edgeCount k s d noiseCount m ≤ edgeCount k s d noiseCount L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_comp, polynomial_capacity_eval, polynomial_edges_eval]
  unfold steps
  omega

end Arithmetic

abbrev Layout (k s d noiseCount : Nat) := Fin 2 ⊕ Arithmetic.Layout k s d noiseCount

variable {k s d noiseCount : Nat} {K Λ σ : Type} [DecidableEq K]

def arithmeticSlots (slots : Layout k s d noiseCount ↪ K) :
    Arithmetic.Layout k s d noiseCount ↪ K :=
  (⟨Sum.inr, Sum.inr_injective⟩ : Arithmetic.Layout k s d noiseCount ↪
    Layout k s d noiseCount).trans slots

def prefixLocal (k s d noiseCount : Nat) : Fin 5 ↪ Layout k s d noiseCount where
  toFun i := match i.val with
    | 0 => .inl 0 | 1 => .inl 1
    | 2 => .inr (.inl .variableCount)
    | 3 => .inr (.inl .occurrenceCount)
    | _ => .inr (.inl .scratch)
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> cases h <;> rfl

theorem prefixLocal_apply (i : Fin 5) :
    prefixLocal k s d noiseCount i = match i.val with
      | 0 => .inl 0 | 1 => .inl 1
      | 2 => .inr (.inl .variableCount)
      | 3 => .inr (.inl .occurrenceCount)
      | _ => .inr (.inl .scratch) := by
  simp only [prefixLocal]
  rfl

def prefixSlots (slots : Layout k s d noiseCount ↪ K) : Fin 5 ↪ K :=
  (prefixLocal k s d noiseCount).trans slots

abbrev Label (k s d noiseCount : Nat) := Prefix.Label ⊕ Arithmetic.Label k s d noiseCount

def statement (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ) : Label k s d noiseCount →
      TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl label => Prefix.statement (prefixSlots slots) (fun l => labels (.inl l))
      (some (labels (.inr .copyNOut))) label
  | .inr label => Arithmetic.statement (arithmeticSlots slots) (fun l => labels (.inr l)) exit label

structure Clean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop
    extends Arithmetic.Clean (arithmeticSlots slots) base where
  readCopy : base (slots (.inl 1)) = []
  variableCount : base (Arithmetic.control (arithmeticSlots slots) .variableCount) = []
  occurrenceCount : base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) = []

/-- Prefix writes only the read-copy and the two designated count tapes. -/
theorem prefixResult_control (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) (c : Arithmetic.Control)
    (hn : c ≠ .variableCount) (hm : c ≠ .occurrenceCount) :
    Prefix.resultTapes (prefixSlots slots) base n m
      (Arithmetic.control (arithmeticSlots slots) c) =
    base (Arithmetic.control (arithmeticSlots slots) c) := by
  apply Prefix.resultTapes_other <;>
    simp [prefixSlots, prefixLocal_apply, Arithmetic.control, arithmeticSlots,
      slots.injective.eq_iff, hn, hm]

theorem prefixResult_coefficient (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) (i : Arithmetic.Coefficients k s d noiseCount) :
    Prefix.resultTapes (prefixSlots slots) base n m (arithmeticSlots slots (.inr i)) =
      base (arithmeticSlots slots (.inr i)) := by
  apply Prefix.resultTapes_other <;>
    simp [prefixSlots, prefixLocal_apply, arithmeticSlots, slots.injective.eq_iff]

theorem Clean.afterPrefix {slots : Layout k s d noiseCount ↪ K} {base : K → List Bool}
    (clean : Clean slots base) (n m : Nat) :
    Arithmetic.Clean (arithmeticSlots slots) (Prefix.resultTapes (prefixSlots slots) base n m) := by
  constructor
  · constructor
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.accA
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.accB
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.counter
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.scratch
    · intro i; rw [prefixResult_coefficient]; exact clean.coefficients i
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.baseValue
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.capacity
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.temporary

def resultTapes (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Arithmetic.resultTapes (arithmeticSlots slots)
    (Prefix.resultTapes (prefixSlots slots) base n m) n m

def inTime (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (input : SourceEncoding.Input)
    (hinput : base (slots (.inl 0)) = SourceEncoding.inputBits input)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inl .copyOut)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes slots base input.variables input.equations.length⟩)
      (Arithmetic.steps k s d noiseCount input.variables input.equations.length +
        (3 * (SourceEncoding.inputBits input).length + 6)) := by
  have parsed := Prefix.inTime (prefixSlots slots) (fun l => labels (.inl l))
    (some (labels (.inr .copyNOut))) program (fun l => atLabels (.inl l))
    base input.variables input.equations.length
    (encodeWords (input.equations.flatMap SourceEncoding.equationWords))
    (by simpa [prefixSlots, prefixLocal_apply, SourceEncoding.inputBits,
      SourceEncoding.inputWords, encodeWords, List.append_assoc] using hinput)
    clean.readCopy clean.scratch ambient register
  have hn : Prefix.resultTapes (prefixSlots slots) base input.variables input.equations.length
      (Arithmetic.control (arithmeticSlots slots) .variableCount) = encodeWord input.variables := by
    change Prefix.resultTapes (prefixSlots slots) base input.variables input.equations.length
      (prefixSlots slots 2) = _
    rw [Prefix.resultTapes_n]
    change encodeWord input.variables ++
      base (Arithmetic.control (arithmeticSlots slots) .variableCount) = _
    rw [clean.variableCount, List.append_nil]
  have hm : Prefix.resultTapes (prefixSlots slots) base input.variables input.equations.length
      (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) =
        encodeWord input.equations.length := by
    change Prefix.resultTapes (prefixSlots slots) base input.variables input.equations.length
      (prefixSlots slots 3) = _
    rw [Prefix.resultTapes_m]
    change encodeWord input.equations.length ++
      base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) = _
    rw [clean.occurrenceCount, List.append_nil]
  have arithmetic := Arithmetic.inTime (arithmeticSlots slots) (fun l => labels (.inr l))
    exit program (fun l => atLabels (.inr l))
    (Prefix.resultTapes (prefixSlots slots) base input.variables input.equations.length)
    input.variables input.equations.length hn hm
    (clean.afterPrefix input.variables input.equations.length) ambient none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ parsed arithmetic
  have sourceEq : base (prefixSlots slots 0) = SourceEncoding.inputBits input := hinput
  simpa only [resultTapes, sourceEq] using joined

def timePolynomial (k s d noiseCount : Nat) : Polynomial Nat :=
  Arithmetic.timePolynomial k s d noiseCount + Polynomial.C 3 * Polynomial.X + Polynomial.C 6

def inPolynomialTime (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (input : SourceEncoding.Input)
    (hinput : base (slots (.inl 0)) = SourceEncoding.inputBits input)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inl .copyOut)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes slots base input.variables input.equations.length⟩)
      ((timePolynomial k s d noiseCount).eval (SourceEncoding.inputBits input).length) := by
  have run := inTime slots labels exit program atLabels base input hinput clean ambient register
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans run.steps_le_m
  have bound := Arithmetic.steps_le_timePolynomial k s d noiseCount
    input.variables input.equations.length (SourceEncoding.inputBits input).length
    (SourceEncoding.inputBits_length_ge_variables input) (SourceEncoding.inputBits_length_ge_equations input)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

@[simp] theorem resultTapes_source (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots (.inl 0)) = base (slots (.inl 0)) := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots, prefixLocal_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

@[simp] theorem resultTapes_n (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .variableCount) =
      encodeWord n ++ base (Arithmetic.control (arithmeticSlots slots) .variableCount) := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots, prefixLocal_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

@[simp] theorem resultTapes_m (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) =
      encodeWord m ++ base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots, prefixLocal_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

@[simp] theorem resultTapes_base (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .baseValue) =
      encodeWord (radix s d n m) := by simp [resultTapes, Arithmetic.resultTapes]

@[simp] theorem resultTapes_capacity (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .capacity) =
      encodeWord (capacity k s d n m) := by simp [resultTapes, Arithmetic.resultTapes]

@[simp] theorem resultTapes_reversed (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .reversed) =
      (Arithmetic.headerBits k s d noiseCount n m).reverse ++
        base (Arithmetic.control (arithmeticSlots slots) .reversed) := by
  simp [resultTapes, Arithmetic.resultTapes,
    prefixResult_control slots base n m .reversed (by decide) (by decide)]

/-- No slot other than the read-copy, saved counts, B, cap, and output is changed. -/
theorem resultTapes_other (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) (tape : K)
    (hread : tape ≠ slots (.inl 1))
    (hn : tape ≠ Arithmetic.control (arithmeticSlots slots) .variableCount)
    (hm : tape ≠ Arithmetic.control (arithmeticSlots slots) .occurrenceCount)
    (hB : tape ≠ Arithmetic.control (arithmeticSlots slots) .baseValue)
    (hcap : tape ≠ Arithmetic.control (arithmeticSlots slots) .capacity)
    (hout : tape ≠ Arithmetic.control (arithmeticSlots slots) .reversed) :
    resultTapes slots base n m tape = base tape := by
  simp only [resultTapes, Arithmetic.resultTapes, Function.update_of_ne hout,
    Function.update_of_ne hcap, Function.update_of_ne hB]
  apply Prefix.resultTapes_other <;> assumption

@[simp] theorem resultTapes_readCopy (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) : resultTapes slots base n m (slots (.inl 1)) = [] := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots, prefixLocal_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

end

end UniqueGamesTheorem.Reduction.MachineAddressHeaders

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_SourceEquationLookupLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.SourceEquationLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
open SourceClauseLookup (discardFieldsTrace)

variable {σ : Type}

/-- Eight binary stacks and fixed finite control. Every loop scans one actual bit
or tests one actual counter bit. The arbitrary ambient state is preserved. -/
def program : Label → TM2.Stmt (fun _ : Tape => Bool) Label (σ × Option Bool)
  | .copyOut => Reduction.MachineTransfer.loopAt .source .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .source .work false
      .copyBack (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .guard
  | .guard => MachineUnaryCounter.guard .index (skipLabel 0) (readStart 0)
  | .skip slot => MachineLookup.discard .work (.skip slot) (skipLabel (slot.val + 1))
  | .read slot =>
      if slot.1.val < 4 then
        if slot.2 then
          fieldLoop .work (fieldDestination slot.1.val) (.read (slot.1, true))
            (some (readStart (slot.1.val + 1)))
        else fieldStart (fieldDestination slot.1.val) (.read (slot.1, true))
      else SourceFieldArray.finish .work none

theorem atSkip (r : Nat) (hr : r < 4) :
    program (σ := σ) (skipLabel r) = MachineLookup.discard .work (skipLabel r) (skipLabel (r + 1)) := by
  simp [skipLabel, hr, program]

theorem atReadStart (r : Nat) (hr : r < 4) :
    program (σ := σ) (readStart r) = fieldStart (fieldDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 4) :
    program (σ := σ) (readLoop r) = fieldLoop .work (fieldDestination r) (readLoop r)
      (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (σ := σ) (readStart 4) = SourceFieldArray.finish .work none := by
  simp [program, readStart, SourceFieldArray.boundedIndex]

/-- The two header fields are physically consumed from the work copy. -/
theorem discardHeadersTrace (base : Tape → List Bool) (variableCount equations : Nat)
    (suffix : List Bool) (hinput : base .work = encodeWords [variableCount, equations] ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[variableCount + equations + 2]
      (some ⟨some .headerFirst, (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work headerLabel program base 0 [variableCount, equations]
    suffix (by
      intro r hr
      have he : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases he with rfl | rfl <;> rfl) hinput ambient
  simpa [encodeWords_length, headerLabel] using ht

/-- The fixed skip body consumes four complete unary fields and returns to the
same counter guard, preserving the counter and every other tape. -/
theorem discardFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (skipLabel 0), (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work skipLabel program base 0 values suffix
    (by intro r hr; simpa only [Nat.zero_add] using atSkip r (by omega)) hinput ambient
  simpa [hlen, skipLabel] using ht

/-- Read the selected four fields using the already checked scanner. -/
theorem readFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length + 5]
      (some ⟨some (readStart 0), (ambient, none), base⟩) =
      some ⟨none, (ambient, none),
        SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix⟩ := by
  have ht := SourceFieldArray.sequenceTrace .work fieldDestination readStart readLoop none
    program base 0 values suffix (by intro r hr; simp [fieldDestination])
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart r (by omega))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop r (by omega))
    (by simpa [hlen] using atReadDone) hinput ambient none
  have htime : values.sum + 2 * values.length + 1 = (encodeWords values).length + 5 := by
    rw [encodeWords_length, hlen]
  simpa only [Nat.zero_add, htime] using ht

@[simp] theorem scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) : scanTapes base i indexSuffix input .work = input := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

@[simp] theorem scanTapes_index (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) :
    scanTapes base i indexSuffix input .index = encodeWord i ++ indexSuffix := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

theorem scanTapes_other (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) (p : Tape) (hi : p ≠ .index) (hw : p ≠ .work) :
    scanTapes base i indexSuffix input p = base p := by
  simp [scanTapes, MachineUnaryCounter.counterTapes, hi, hw]

theorem update_scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input replacement : List Bool) :
    Function.update (scanTapes base i indexSuffix input) .work replacement =
      scanTapes base i indexSuffix replacement := by
  funext p
  cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes]

/-- Each equation-index bit causes one genuine guard transition and exactly four
field-discard loops. The final zero guard enters the field reader. -/
theorem skipEquationsTrace {n : Nat} (base : Tape → List Bool)
    (prior : List (CloneGap.Equation (Fin n))) (indexSuffix suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      (some ⟨some .guard, (ambient, register), scanTapes base prior.length indexSuffix
        (encodeWords (prior.flatMap equationWords) ++ suffix)⟩) =
      some ⟨some (readStart 0), (ambient, none), scanTapes base 0 indexSuffix suffix⟩ := by
  induction prior generalizing register with
  | nil =>
    simpa only [List.flatMap_nil, List.length_nil, encodeWords, List.nil_append,
      Nat.zero_add, Function.iterate_one, advance_some, scanTapes] using
      MachineUnaryCounter.guardStep_zero .index .guard (skipLabel 0) (readStart 0)
        program rfl (Function.update base .work suffix) indexSuffix ambient register
  | cons equation prior ih =>
    have hencoding : encodeWords ((equation :: prior).flatMap equationWords) ++ suffix =
        encodeWords (equationWords equation) ++ (encodeWords (prior.flatMap equationWords) ++ suffix) := by
      simp only [List.flatMap_cons, encodeWords_append, List.append_assoc]
    have htime : (encodeWords ((equation :: prior).flatMap equationWords)).length +
        (equation :: prior).length + 1 =
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
          (encodeWords (equationWords equation)).length) + 1 := by
      simp only [List.flatMap_cons, encodeWords_append, List.length_append, List.length_cons]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
        (encodeWords (equationWords equation)).length]
      (TM2.step program ⟨some .guard, (ambient, register),
        MachineUnaryCounter.counterTapes .index
          (Function.update base .work (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
          (prior.length + 1) indexSuffix⟩) = _
    rw [MachineUnaryCounter.guardStep_succ .index .guard (skipLabel 0) (readStart 0)
      program rfl]
    rw [Function.iterate_add_apply]
    have hd := discardFourTrace
      (scanTapes base prior.length indexSuffix
        (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
      (equationWords equation) (equationWords_length equation)
      (encodeWords (prior.flatMap equationWords) ++ suffix) (by
        rw [scanTapes_work, hencoding]) ambient
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      ((advance (TM2.step program))^[(encodeWords (equationWords equation)).length]
        (some ⟨some (skipLabel 0), (ambient, none), scanTapes base prior.length indexSuffix
          (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix)⟩)) = _
    rw [hd, update_scanTapes_work]
    exact ih none

theorem fieldDestination_eq (j : Fin 4) : fieldDestination j.val = .field j := by
  unfold fieldDestination
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

theorem fieldDestination_injective_below (r s : Nat) (hr : r < 4) (hs : s < 4)
    (he : fieldDestination r = fieldDestination s) : r = s := by
  have hv := congrArg (fun t : Tape => match t with | .field j => j.val | _ => 4) he
  simpa [fieldDestination, Nat.min_eq_left (show r ≤ 3 by omega),
    Nat.min_eq_left (show s ≤ 3 by omega)] using hv

theorem readFour_output_field (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool) (j : Fin 4) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix (.field j) =
      encodeWord (values[j.val]'(by omega)) ++ base (.field j) := by
  have ht := SourceFieldArray.sequenceTapes_selected .work fieldDestination base 0 values
    suffix j.val (by omega) (by intro r hr; simp [fieldDestination])
    (by
      intro r s hr hs he
      apply fieldDestination_injective_below r s (by omega) (by omega)
      simpa only [Nat.zero_add] using he)
  simpa only [Nat.zero_add, fieldDestination_eq] using ht

theorem readFour_output_work (base : Tape → List Bool) (values : List Nat)
    (_hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix .work = suffix := by
  apply SourceFieldArray.sequenceTapes_source _ _ _ _ _ _ _ hinput
  intro r hr
  simp [fieldDestination]

theorem readFour_output_frame (base : Tape → List Bool) (values : List Nat)
    (suffix : List Bool) (p : Tape) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 4, p ≠ .field j) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix p = base p := by
  apply SourceFieldArray.sequenceTapes_other _ _ _ hwork
  intro r hr
  exact hfield _

def outputTapes {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) : Tape → List Bool :=
  SourceFieldArray.sequenceTapes .work fieldDestination
    (scanTapes base 0 indexSuffix (encodeWords (equationWords equation) ++ suffix))
    0 (equationWords equation) suffix

def scanSteps {n : Nat} (variableCount declaredEquations : Nat)
    (prior : List (CloneGap.Equation (Fin n))) (equation : CloneGap.Equation (Fin n)) : Nat :=
  variableCount + declaredEquations + 2 +
    (encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
    (encodeWords (equationWords equation)).length + 5

theorem scanReadTrace {n : Nat} (base : Tape → List Bool) (variableCount declaredEquations : Nat)
    (prior : List (CloneGap.Equation (Fin n))) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[scanSteps variableCount declaredEquations prior equation]
      (some ⟨some .headerFirst, (ambient, none), scanTapes base prior.length indexSuffix
        (encodeWords [variableCount, declaredEquations] ++
          (encodeWords (prior.flatMap equationWords) ++
            (encodeWords (equationWords equation) ++ suffix)))⟩) =
      some ⟨none, (ambient, none), outputTapes base equation indexSuffix suffix⟩ := by
  have hh := discardHeadersTrace
    (scanTapes base prior.length indexSuffix
      (encodeWords [variableCount, declaredEquations] ++
        (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))))
    variableCount declaredEquations
    (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))
    (by simp) ambient
  have hs := skipEquationsTrace base prior indexSuffix (encodeWords (equationWords equation) ++ suffix) ambient none
  have hr := readFourTrace
    (scanTapes base 0 indexSuffix (encodeWords (equationWords equation) ++ suffix))
    (equationWords equation) (equationWords_length equation) suffix (by simp) ambient
  rw [show scanSteps variableCount declaredEquations prior equation =
      ((encodeWords (equationWords equation)).length + 5 +
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1)) +
        (variableCount + declaredEquations + 2) by unfold scanSteps; omega]
  rw [Function.iterate_add_apply, hh, update_scanTapes_work,
    Function.iterate_add_apply, hs]
  exact hr

def lookupSteps {n : Nat} (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin n)))
    (equation : CloneGap.Equation (Fin n)) : Nat :=
  2 * ((inputBits F).length + 1) + scanSteps F.variables F.equations.length prior equation

theorem lookupWithSplitTrace (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.variables)))
    (equation : CloneGap.Equation (Fin F.variables)) (after : List (CloneGap.Equation (Fin F.variables)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[lookupSteps F prior equation]
      (some ⟨some .copyOut, (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩ := by
  have hbits : inputBits F = encodeWords [F.variables, F.equations.length] ++
      (encodeWords (prior.flatMap equationWords) ++
        (encodeWords (equationWords equation) ++ encodeWords (after.flatMap equationWords))) := by
    simp only [inputBits, inputWords, encodeWords_append]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append]
  have hc := MachineCopy.copyTrace .source .work .scratch (by decide) (by decide)
    (by decide) false .copyOut .copyBack (some .headerFirst) program rfl rfl
    base hscratch ambient register
  have htapes : Function.update base .work (base .source ++ base .work) =
      scanTapes base prior.length indexSuffix (inputBits F) := by
    funext p
    cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes, hsource, hindex, hwork]
  rw [htapes, hsource] at hc
  rw [lookupSteps, Nat.add_comm, Function.iterate_add_apply, hc, hbits]
  exact scanReadTrace base F.variables F.equations.length prior equation indexSuffix
    (encodeWords (after.flatMap equationWords)) ambient

theorem output_source {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .source = base .source := by
  rw [outputTapes, readFour_output_frame _ _ _ .source (by decide) (by intro j; simp)]
  exact scanTapes_other _ _ _ _ _ (by decide) (by decide)

theorem output_index {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .index = encodeWord 0 ++ indexSuffix := by
  rw [outputTapes, readFour_output_frame _ _ _ .index (by decide) (by intro j; simp),
    scanTapes_index]

theorem output_work {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .work = suffix := by
  apply readFour_output_work _ _ (equationWords_length equation) _
  simp

theorem output_field {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (j : Fin 4) :
    outputTapes base equation indexSuffix suffix (.field j) =
      encodeWord ((equationWords equation)[j.val]'(by simp)) ++ base (.field j) := by
  rw [outputTapes, readFour_output_field _ _ (equationWords_length equation)]
  rw [scanTapes_other _ _ _ _ (.field j) (by simp) (by simp)]

theorem output_frame {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (p : Tape) (hindex : p ≠ .index) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 4, p ≠ .field j) :
    outputTapes base equation indexSuffix suffix p = base p := by
  rw [outputTapes, readFour_output_frame _ _ _ p hwork hfield]
  exact scanTapes_other _ _ _ _ p hindex hwork

theorem lookupSteps_le_input (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.variables)))
    (equation : CloneGap.Equation (Fin F.variables)) (after : List (CloneGap.Equation (Fin F.variables)))
    (hsplit : F.equations = prior ++ equation :: after) :
    lookupSteps F prior equation ≤ 4 * (inputBits F).length + 8 := by
  have hlength : (inputBits F).length = F.variables + F.equations.length + 2 +
      (encodeWords (prior.flatMap equationWords)).length +
      (encodeWords (equationWords equation)).length +
      (encodeWords (after.flatMap equationWords)).length := by
    simp only [inputBits, inputWords, encodeWords_append, List.length_append,
      encodeWords, encodeWord_length, List.length_nil]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append, List.length_append]
    omega
  have hp : prior.length ≤ F.equations.length := by
    rw [hsplit, List.length_append, List.length_cons]
    omega
  unfold lookupSteps scanSteps
  omega

/-- A polynomial bound on the actual complete copy/skip/read execution. -/
def lookupWithSplitInTime (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.variables)))
    (equation : CloneGap.Equation (Fin F.variables)) (after : List (CloneGap.Equation (Fin F.variables)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) where
  steps := lookupSteps F prior equation
  evals_in_steps := lookupWithSplitTrace F prior equation after hsplit base indexSuffix
    hsource hindex hwork hscratch ambient register
  steps_le_m := by
    rw [timePolynomial_eval]
    exact lookupSteps_le_input F prior equation after hsplit

def lookupInTime (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none), outputTapes base F.equations[i.val] indexSuffix
        (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) := by
  have hp : (F.equations.take i.val).length = i.val := by
    rw [List.length_take, Nat.min_eq_left i.isLt.le]
  have hs : F.equations = F.equations.take i.val ++ F.equations[i.val] :: F.equations.drop (i.val + 1) := by
    rw [List.getElem_cons_drop i.isLt, List.take_append_drop]
  apply lookupWithSplitInTime F (F.equations.take i.val) F.equations[i.val]
    (F.equations.drop (i.val + 1)) hs base indexSuffix hsource
    (by simpa only [hp] using hindex) hwork hscratch ambient register

end UniqueGamesTheorem.Reduction.SourceEquationLookup

end

section

namespace UniqueGamesTheorem.Reduction.MachineSourceTuple

open Turing UniqueGamesTheorem.Foundations.Complexity
open SourceEncoding
open MachineComposition

variable {width : Nat} {Extra σ : Type}

def place (j : Fin width) : SourceEquationLookup.Tape → Tape width Extra
  | .source => .source | .index => .index | .work => .work | .scratch => .scratch
  | .field s => .field j s

def fill (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) : Tape width Extra → List Bool
  | .source => localTapes .source | .index => localTapes .index
  | .work => localTapes .work | .scratch => localTapes .scratch
  | .field i s => if i = j then localTapes (.field s) else base (.field i s)
  | p => base p

@[simp] theorem fill_place (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) (p : SourceEquationLookup.Tape) :
    fill j base localTapes (place j p) = localTapes p := by
  cases p <;> simp [fill, place]

@[simp] theorem fill_self (j : Fin width) (base : Tape width Extra → List Bool) :
    fill j base (base ∘ place j) = base := by
  funext p
  cases p <;> simp [fill, place]
  intro h
  subst h
  rfl

variable [DecidableEq Extra]

theorem fill_update (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) (p : SourceEquationLookup.Tape)
    (value : List Bool) :
    fill j base (Function.update localTapes p value) =
      Function.update (fill j base localTapes) (place j p) value := by
  funext k
  cases k <;> cases p <;> simp [fill, place, Function.update_apply]
  all_goals split <;> simp_all

def placedConfiguration (j : Fin width) (base : Tape width Extra → List Bool)
    (c : TM2.Cfg (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool)) :
    TM2.Cfg (fun _ : Tape width Extra => Bool) (Label width) ((σ × Unit) × Option Bool) :=
  ⟨placedLabel j c.l, c.var, fill j base c.stk⟩

def placedStatement (j : Fin width) :
    TM2.Stmt (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool) →
    TM2.Stmt (fun _ : Tape width Extra => Bool) (Label width) ((σ × Unit) × Option Bool)
  | .push k f next => .push (place j k) f (placedStatement j next)
  | .peek k f next => .peek (place j k) f (placedStatement j next)
  | .pop k f next => .pop (place j k) f (placedStatement j next)
  | .load f next => .load f (placedStatement j next)
  | .branch f yes no => .branch f (placedStatement j yes) (placedStatement j no)
  | .goto f => .goto (fun state => .lookup j (f state))
  | .halt => .goto (fun _ => .clearWork j)

theorem placed_stepAux (j : Fin width) (base : Tape width Extra → List Bool)
    (q : TM2.Stmt (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool))
    (state : (σ × Unit) × Option Bool) (localTapes : SourceEquationLookup.Tape → List Bool) :
    TM2.stepAux (placedStatement j q) state (fill j base localTapes) =
      placedConfiguration j base (TM2.stepAux q state localTapes) := by
  induction q generalizing state localTapes with
  | push k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih state _
  | peek k f next ih =>
    simpa only [placedStatement, TM2.stepAux, fill_place] using ih (f state _) localTapes
  | pop k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih (f state _) _
  | load f next ih => simpa only [placedStatement, TM2.stepAux] using ih (f state) localTapes
  | branch f yes no ihYes ihNo =>
    cases h : f state
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state localTapes
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state localTapes
  | goto f => rfl
  | halt => rfl

def program : Label width → TM2.Stmt (fun _ : Tape width Extra => Bool)
    (Label width) ((σ × Unit) × Option Bool)
  | .copyOut j => Reduction.MachineTransfer.loopAt (.savedIndex j) .copyScratch id false
      (.copyOut j) (some (.copyBack j))
  | .copyBack j => MachineCopy.forkLoop .copyScratch (.savedIndex j) .index false
      (.copyBack j) (some (.lookup j .copyOut))
  | .lookup j l => placedStatement j (SourceEquationLookup.program l)
  | .clearWork j => MachineDrain.drain .work (.clearWork j) (some (.clearIndex j))
  | .clearIndex j => MachineDrain.drain .index (.clearIndex j) (some (nextLabel j))
  | .done => .halt

theorem placed_step (j : Fin width) (base : Tape width Extra → List Bool)
    (a b : TM2.Cfg (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool))
    (h : TM2.step SourceEquationLookup.program a = some b) :
    TM2.step program (placedConfiguration j base a) =
      some (placedConfiguration j base b) := by
  cases a with
  | mk l state localTapes =>
    cases l with
    | none => contradiction
    | some l =>
      change some (TM2.stepAux (SourceEquationLookup.program l) state localTapes) = some b at h
      cases Option.some.inj h
      change some (TM2.stepAux (placedStatement j (SourceEquationLookup.program l))
        state (fill j base localTapes)) = _
      rw [placed_stepAux]

def lookupOutput (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool) : Tape width Extra → List Bool :=
  fill j base (SourceEquationLookup.outputTapes (base ∘ place j) F.equations[i.val] suffix
    (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords)))

noncomputable def placedLookupInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ suffix)
    (hwork : base .work = []) (hscratch : base .scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.lookup j .copyOut), ((ambient, ()), register), base⟩
      (some ⟨some (.clearWork j), ((ambient, ()), none), lookupOutput j F i base suffix⟩)
      (4 * (inputBits F).length + 8) := by
  have h := SourceEquationLookup.lookupInTime F i (base ∘ place j) suffix
    hsource hindex hwork hscratch (ambient, ()) register
  have lifted := liftExecutionInTime (TM2.step SourceEquationLookup.program) (TM2.step program)
    (placedConfiguration j base) (placed_step j base) h
  simpa only [placedConfiguration, placedLabel, fill_self,
    SourceEquationLookup.timePolynomial_eval, lookupOutput] using lifted

def copiedTapes (j : Fin width) (base : Tape width Extra → List Bool) : Tape width Extra → List Bool :=
  Function.update base .index (base (.savedIndex j))

def coordinateOutput {n : Nat} (j : Fin width) (equation : CloneGap.Equation (Fin n))
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .index | .work => []
  | .field k s => if k = j then
      encodeWord ((equationWords equation)[s.val]'(by simp)) ++ base (.field k s)
    else base (.field k s)
  | p => base p

theorem cleanup_lookupOutput (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool) :
    Function.update (Function.update
      (lookupOutput j F i (copiedTapes j base) suffix) .work []) .index [] =
      coordinateOutput j F.equations[i.val] base := by
  funext p
  cases p with
  | source => simp [lookupOutput, fill, coordinateOutput, SourceEquationLookup.output_source,
      copiedTapes, place]
  | index => simp [coordinateOutput]
  | work => simp [coordinateOutput]
  | scratch =>
    simp only [Function.update_of_ne (by simp : (Tape.scratch : Tape width Extra) ≠ .index),
      Function.update_of_ne (by simp : (Tape.scratch : Tape width Extra) ≠ .work), lookupOutput, fill,
      coordinateOutput]
    rw [SourceEquationLookup.output_frame _ _ _ _ .scratch (by simp) (by simp) (by intro s; simp)]
    simp [copiedTapes, place]
  | field k s =>
    by_cases hk : k = j
    · subst k
      simp [lookupOutput, fill, coordinateOutput, SourceEquationLookup.output_field,
        copiedTapes, place]
    · simp [lookupOutput, fill, coordinateOutput, hk, copiedTapes]
  | copyScratch => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | savedIndex k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | extra k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_savedIndex {n : Nat} (j k : Fin width) (equation : CloneGap.Equation (Fin n))
    (base : Tape width Extra → List Bool) :
    coordinateOutput j equation base (.savedIndex k) = base (.savedIndex k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_field {n : Nat} (j : Fin width) (s : Fin 4)
    (equation : CloneGap.Equation (Fin n)) (base : Tape width Extra → List Bool) :
    coordinateOutput j equation base (.field j s) =
      encodeWord ((equationWords equation)[s.val]'(by simp)) ++ base (.field j s) := by
  simp [coordinateOutput]

omit [DecidableEq Extra] in
theorem coordinateOutput_other_field {n : Nat} (j k : Fin width) (s : Fin 4)
    (equation : CloneGap.Equation (Fin n)) (base : Tape width Extra → List Bool) (h : k ≠ j) :
    coordinateOutput j equation base (.field k s) = base (.field k s) := by
  simp [coordinateOutput, h]

theorem suffix_length_le_input (F : SourceEncoding.Input) (i : Nat) :
    (encodeWords ((F.equations.drop i).flatMap equationWords)).length ≤ (inputBits F).length := by
  have hs := List.take_append_drop i F.equations
  have he : inputBits F = encodeWords [F.variables, F.equations.length] ++
      encodeWords ((F.equations.take i).flatMap equationWords) ++
      encodeWords ((F.equations.drop i).flatMap equationWords) := by
    conv_lhs => rw [inputBits, inputWords, ← hs]
    simp only [List.flatMap_append, encodeWords_append, List.append_assoc]
    rw [hs]
  rw [he, List.length_append, List.length_append]
  omega

noncomputable def coordinateInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : base (.savedIndex j) = encodeWord i.val ++ suffix)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.copyOut j), ((ambient, ()), register), base⟩
      (some ⟨some (nextLabel j), ((ambient, ()), none), coordinateOutput j F.equations[i.val] base⟩)
      (6 * (inputBits F).length + 4 * (base (.savedIndex j)).length + 20) := by
  let copied := copiedTapes j base
  let loaded := lookupOutput j F i copied suffix
  have copyRun := MachineCopy.copyInTime (.savedIndex j) .index .copyScratch
    (by simp) (by simp) (by simp) false (.copyOut j) (.copyBack j)
    (some (.lookup j .copyOut)) program rfl rfl base hcopy (ambient, ()) register
  have copied_eq : Function.update base .index (base (.savedIndex j) ++ base .index) = copied := by
    simp [copied, copiedTapes, hindex]
  rw [copied_eq] at copyRun
  have lookupRun := placedLookupInTime j F i copied suffix
    (by simpa [copied, copiedTapes] using hsource)
    (by simpa [copied, copiedTapes] using hsavedIndex)
    (by simpa [copied, copiedTapes] using hwork)
    (by simpa [copied, copiedTapes] using hscratch) ambient none
  have workRun := MachineDrain.drainInTime .work (.clearWork j) (some (.clearIndex j))
    program rfl loaded (ambient, ()) none
  have indexRun := MachineDrain.drainInTime .index (.clearIndex j) (some (nextLabel j))
    program rfl (Function.update loaded .work []) (ambient, ()) none
  have hrun := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copyRun lookupRun)
      workRun) indexRun
  have hw : loaded .work = encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords) := by
    simp [loaded, lookupOutput, fill, SourceEquationLookup.output_work]
  have hi : (Function.update loaded .work []) .index = encodeWord 0 ++ suffix := by
    simp [loaded, lookupOutput, fill, SourceEquationLookup.output_index]
  have hc : suffix.length ≤ (base (.savedIndex j)).length := by
    rw [hsavedIndex, List.length_append]
    omega
  refine { steps := hrun.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [loaded, copied, cleanup_lookupOutput] using hrun.evals_in_steps
  · apply Nat.le_trans hrun.steps_le_m
    rw [hw, hi, List.length_append, encodeWord_length]
    have hs := suffix_length_le_input F (i.val + 1)
    omega

def stageTapes (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) : Nat → Tape width Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < width then
      coordinateOutput ⟨r, h⟩ F.equations[(tuple ⟨r, h⟩).val] (stageTapes F tuple base r)
    else stageTapes F tuple base r

omit [DecidableEq Extra] in
theorem stageTapes_frame (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (p : Tape width Extra)
    (hi : p ≠ .index) (hw : p ≠ .work) (hf : ∀ j s, p ≠ .field j s) :
    stageTapes F tuple base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · cases p <;> simp_all [coordinateOutput]
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_clean (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (hi : base .index = []) (hw : base .work = []) :
    stageTapes F tuple base r .index = [] ∧ stageTapes F tuple base r .work = [] := by
  induction r with
  | zero => exact ⟨hi, hw⟩
  | succ r ih =>
    simp only [stageTapes]
    split
    · exact ⟨rfl, rfl⟩
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_field (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (j : Fin width) (s : Fin 4) :
    stageTapes F tuple base r (.field j s) = if j.val < r then
      encodeWord ((equationWords F.equations[(tuple j).val])[s.val]'(by simp)) ++ base (.field j s)
      else base (.field j s) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin width)
      · subst j
        simp only [coordinateOutput_field, ih]
        simp
      · rw [coordinateOutput_other_field _ _ _ _ _ hj, ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true, if_true]

noncomputable def prefixInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (r : Nat) (hr : r ≤ width) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨some (labelAt r), ((ambient, ()), none), stageTapes F tuple base r⟩)
      (r * (6 * (inputBits F).length + 4 * C + 20)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < width := by omega
    let j : Fin width := ⟨r, hru⟩
    let before := stageTapes F tuple base r
    have hf (p : Tape width Extra) (hi : p ≠ .index) (hw : p ≠ .work)
        (hh : ∀ j s, p ≠ .field j s) : before p = base p :=
      stageTapes_frame F tuple base r p hi hw hh
    have hd := stageTapes_clean F tuple base r hindex hwork
    have hc : before (.savedIndex j) = base (.savedIndex j) := hf _ (by simp) (by simp) (by simp)
    have one := coordinateInTime j F (tuple j) before (suffix j)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hsource)
      (by rw [hc]; exact hsavedIndex j) hd.1 hd.2
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hscratch)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hcopy) ambient none
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((ambient, ()), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((ambient, ()), none), stageTapes F tuple base (r + 1)⟩)
        (6 * (inputBits F).length + 4 * C + 20) := by
      refine { steps := one.steps, evals_in_steps := ?_, steps_le_m := ?_ }
      · simpa only [labelAt, dite_eq_left hru, nextLabel_eq, j, stageTapes, before] using
          one.evals_in_steps
      · apply Nat.le_trans one.steps_le_m
        rw [hc]
        have hs := hsize j
        omega
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

noncomputable def loadInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (6 * (inputBits F).length + 4 * C + 20) + 1) := by
  have prefixRun := prefixInTime F tuple base suffix C hsource hsavedIndex hsize
    hindex hwork hscratch hcopy width (Nat.le_refl _) ambient
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ prefixRun doneRun

theorem equations_length_le_input (F : SourceEncoding.Input) :
    F.equations.length ≤ (inputBits F).length := by
  simp only [inputBits, encodeWords_length, inputWords_length]
  omega

/-- Actual odometer digits have empty suffixes. The resulting complete loader
runs in a polynomial whose coefficients depend only on the fixed repetition k. -/
noncomputable def loadUnaryInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) := by
  have run := loadInTime F tuple base (fun _ => []) (inputBits F).length hsource
    (by simpa only [List.append_nil] using hsavedIndex)
    (by
      intro j
      rw [hsavedIndex j, encodeWord_length]
      have h := (tuple j).isLt
      have hm := equations_length_le_input F
      omega)
    hindex hwork hscratch hcopy ambient
  have he : 6 * (inputBits F).length + 4 * (inputBits F).length + 20 =
      10 * (inputBits F).length + 20 := by omega
  simpa only [he] using run

def nameField (j : Fin width) (s : Fin 3) : Tape width Extra := .field j (nameSlot s)
def rhsField (j : Fin width) : Tape width Extra := .field j 3

def equationName {n : Nat} (e : CloneGap.Equation (Fin n)) (s : Fin 3) : Nat :=
  match s.val with
  | 0 => e.first.val
  | 1 => e.second.val
  | _ => e.third.val

theorem equationWords_name {n : Nat} (e : CloneGap.Equation (Fin n)) (s : Fin 3) :
    (equationWords e)[(nameSlot s).val]'(by simp) = equationName e s := by
  obtain ⟨s, hs⟩ := s
  have h : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

omit [DecidableEq Extra] in
theorem output_name (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) (s : Fin 3) :
    stageTapes F tuple base width (nameField j s) =
      encodeWord (equationName F.equations[(tuple j).val] s) ++ base (nameField j s) := by
  rw [nameField, stageTapes_field, ite_eq_left j.isLt, equationWords_name]

omit [DecidableEq Extra] in
theorem output_rhs (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) :
    stageTapes F tuple base width (rhsField j) =
      encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++ base (rhsField j) := by
  rw [rhsField, stageTapes_field, ite_eq_left j.isLt]
  rfl

omit [DecidableEq Extra] in
theorem output_savedIndex (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) :
    stageTapes F tuple base width (.savedIndex j) = base (.savedIndex j) :=
  stageTapes_frame F tuple base width (.savedIndex j) (by simp) (by simp) (by simp)

omit [DecidableEq Extra] in
theorem output_savedIndex_unary (F : SourceEncoding.Input)
    (tuple : Fin width → Fin F.equations.length) (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val) (j : Fin width) :
    stageTapes F tuple base width (.savedIndex j) = encodeWord (tuple j).val :=
  (output_savedIndex F tuple base j).trans (hsaved j)

/-- A caller shares this complete tape arena and state, mapping only labels and
the final continuation. All saved occurrence IDs remain available to its body. -/
noncomputable def placedLoadUnaryInTime {Λ : Type}
    (labels : Label width → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape width Extra => Bool) Λ ((σ × Unit) × Option Bool))
    (atLabels : ∀ l, target (labels l) = MachineSubroutine.statement labels exit (program l))
    (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (labelAt 0)), ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) :=
  MachineSubroutine.execution labels exit program target atLabels
    (loadUnaryInTime F tuple base hsource hsaved hindex hwork hscratch hcopy ambient)

end UniqueGamesTheorem.Reduction.MachineSourceTuple

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressMachineSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.AddressMachineSpace

open UniqueGamesTheorem.Foundations.Complexity

abbrev Extra (k s d noiseCount : Nat) :=
  MachineAddressHeaders.Arithmetic.Layout k s d noiseCount ⊕
    (MachineTemplateAddress.Tape (4 * k) (1 + 9 * k) ⊕ (Fin k ⊕ Unit))

abbrev Tape (k s d noiseCount : Nat) :=
  MachineSourceTuple.Tape k (Extra k s d noiseCount)

variable (k s d noiseCount : Nat)

def headerArithmeticSlots : MachineAddressHeaders.Arithmetic.Layout k s d noiseCount ↪
    Tape k s d noiseCount where
  toFun a := .extra (.inl a)
  inj' := by intro a b h; exact Sum.inl.inj (MachineSourceTuple.Tape.extra.inj h)

def headerTape (c : MachineAddressHeaders.Arithmetic.Control) : Tape k s d noiseCount :=
  .extra (.inl (.inl c))

@[simp] theorem headerTape_eq_iff (a b : MachineAddressHeaders.Arithmetic.Control) :
    headerTape k s d noiseCount a = headerTape k s d noiseCount b ↔ a = b := by
  simp [headerTape]

def fullHeaderSlots : MachineAddressHeaders.Layout k s d noiseCount ↪ Tape k s d noiseCount where
  toFun
    | .inl 0 => .source
    | .inl 1 => .work
    | .inr a => headerArithmeticSlots k s d noiseCount a
  inj' := by
    rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> cases h <;> rfl
    · fin_cases a <;> cases h
    · fin_cases b <;> cases h
    · exact congrArg Sum.inr ((headerArithmeticSlots k s d noiseCount).injective h)

@[simp] theorem fullHeaderSlots_source : fullHeaderSlots k s d noiseCount (.inl 0) = .source := rfl
@[simp] theorem fullHeaderSlots_work : fullHeaderSlots k s d noiseCount (.inl 1) = .work := rfl
@[simp] theorem fullHeaderSlots_arithmetic (a : MachineAddressHeaders.Arithmetic.Layout k s d noiseCount) :
    fullHeaderSlots k s d noiseCount (.inr a) = headerArithmeticSlots k s d noiseCount a := rfl

@[simp] theorem arithmeticSlots_fullHeaderSlots :
    MachineAddressHeaders.arithmeticSlots (fullHeaderSlots k s d noiseCount) =
      headerArithmeticSlots k s d noiseCount := by ext a; rfl

def prefixSlots : Fin 5 ↪ Tape k s d noiseCount :=
  MachineAddressHeaders.prefixSlots (fullHeaderSlots k s d noiseCount)

@[simp] theorem prefixSlots_source : prefixSlots k s d noiseCount 0 = .source := rfl
@[simp] theorem prefixSlots_work : prefixSlots k s d noiseCount 1 = .work := rfl
@[simp] theorem prefixSlots_variables :
    prefixSlots k s d noiseCount 2 = headerTape k s d noiseCount .variableCount := rfl
@[simp] theorem prefixSlots_occurrences :
    prefixSlots k s d noiseCount 3 = headerTape k s d noiseCount .occurrenceCount := rfl
@[simp] theorem prefixSlots_scratch :
    prefixSlots k s d noiseCount 4 = headerTape k s d noiseCount .scratch := rfl

def canonicalField (position : Fin k) (slot : Fin 4) : Tape k s d noiseCount :=
  if slot = 3 then .savedIndex position else .field position slot

def rhsField (position : Fin k) : Tape k s d noiseCount := .field position 3

@[simp] theorem canonicalField_occurrence (position : Fin k) :
    canonicalField k s d noiseCount position 3 = .savedIndex position := by simp [canonicalField]

@[simp] theorem canonicalField_name (position : Fin k) (slot : Fin 3) :
    canonicalField k s d noiseCount position (MachineSourceTuple.nameSlot slot) =
      MachineSourceTuple.nameField position slot := by
  have hs : MachineSourceTuple.nameSlot slot ≠ (3 : Fin 4) := by
    intro h
    have hv := congrArg Fin.val h
    have bound := slot.isLt
    simp only [MachineSourceTuple.nameSlot] at hv
    omega
  simp [canonicalField, hs, MachineSourceTuple.nameField]

def privateAddress (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    Tape k s d noiseCount := .extra (.inr (.inl tape))

def edgeSlot : MachineAddressEdge.Tape (4 * k) (1 + 9 * k) → Tape k s d noiseCount
  | .inl (.field i) => canonicalField k s d noiseCount
      ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2
  | .inl .radix => headerTape k s d noiseCount .baseValue
  | .inl tape => privateAddress k s d noiseCount tape
  | .inr i => if i = 0 then headerTape k s d noiseCount .capacity
      else headerTape k s d noiseCount .reversed

/-- A partial inverse proves separation without a default element of `Fin k`.
It therefore applies unchanged at `k = 0`. -/
def edgeDecode : Tape k s d noiseCount →
    Option (MachineAddressEdge.Tape (4 * k) (1 + 9 * k))
  | .savedIndex j => some (.inl (.field (CanonicalBodyMachine.fieldIndex j 3)))
  | .field j slot => if slot = 3 then none
      else some (.inl (.field (CanonicalBodyMachine.fieldIndex j slot)))
  | .extra (.inl (.inl .baseValue)) => some (.inl .radix)
  | .extra (.inl (.inl .capacity)) => some (.inr 0)
  | .extra (.inl (.inl .reversed)) => some (.inr 1)
  | .extra (.inr (.inl tape)) => some (.inl tape)
  | _ => none

theorem edgeDecode_canonicalField (position : Fin k) (slot : Fin 4) :
    edgeDecode k s d noiseCount (canonicalField k s d noiseCount position slot) =
      some (.inl (.field (CanonicalBodyMachine.fieldIndex position slot))) := by
  by_cases h : slot = 3 <;> simp [canonicalField, edgeDecode, h]

theorem edgeDecode_edgeSlot (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    edgeDecode k s d noiseCount (edgeSlot k s d noiseCount tape) = some tape := by
  rcases tape with tape | i
  · cases tape <;> try rfl
    rename_i index
    rw [edgeSlot, edgeDecode_canonicalField]
    exact congrArg (fun i => some (Sum.inl (MachineTemplateAddress.Tape.field i)))
      ((CanonicalBodyMachine.fieldEquiv k).apply_symm_apply index)
  · fin_cases i <;> rfl

def addressEdgeSlots : MachineAddressEdge.Tape (4 * k) (1 + 9 * k) ↪ Tape k s d noiseCount where
  toFun := edgeSlot k s d noiseCount
  inj' := by
    intro a b h
    have decoded := congrArg (edgeDecode k s d noiseCount) h
    apply Option.some.inj
    simpa only [edgeDecode_edgeSlot] using decoded

@[simp] theorem addressEdgeSlots_fieldIndex (position : Fin k) (slot : Fin 4) :
    addressEdgeSlots k s d noiseCount
      (.inl (.field (CanonicalBodyMachine.fieldIndex position slot))) =
        canonicalField k s d noiseCount position slot := by
  change canonicalField k s d noiseCount
    ((CanonicalBodyMachine.fieldEquiv k).symm
      (CanonicalBodyMachine.fieldEquiv k (position, slot))).1
    ((CanonicalBodyMachine.fieldEquiv k).symm
      (CanonicalBodyMachine.fieldEquiv k (position, slot))).2 = _
  simp only [Equiv.symm_apply_apply]

@[simp] theorem addressSlots_name (position : Fin k) (slot : Fin 3) :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
      (.field (CanonicalBodyMachine.fieldIndex position (MachineSourceTuple.nameSlot slot))) =
        MachineSourceTuple.nameField position slot := by
  exact (addressEdgeSlots_fieldIndex k s d noiseCount position _).trans
    (canonicalField_name k s d noiseCount position slot)

@[simp] theorem addressSlots_occurrence (position : Fin k) :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
      (.field (CanonicalBodyMachine.fieldIndex position 3)) = .savedIndex position := by
  exact (addressEdgeSlots_fieldIndex k s d noiseCount position 3).trans
    (canonicalField_occurrence k s d noiseCount position)

@[simp] theorem addressSlots_radix :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount) .radix =
      headerTape k s d noiseCount .baseValue := rfl
@[simp] theorem addressSlots_capacity :
    MachineAddressEdge.capacityTape (addressEdgeSlots k s d noiseCount) =
      headerTape k s d noiseCount .capacity := rfl
@[simp] theorem addressSlots_output :
    MachineAddressEdge.outputTape (addressEdgeSlots k s d noiseCount) =
      headerTape k s d noiseCount .reversed := rfl

def current (j : Fin k) : Tape k s d noiseCount := .savedIndex j.rev
def remaining (j : Fin k) : Tape k s d noiseCount := .extra (.inr (.inr (.inl j)))
def finalOutput : Tape k s d noiseCount := .extra (.inr (.inr (.inr ())))

@[simp] theorem current_rev (j : Fin k) : current k s d noiseCount j.rev = .savedIndex j := by
  simp [current]

def odometerSlots : MachineOdometerInit.Tape k ↪ Tape k s d noiseCount where
  toFun
    | .radix => headerTape k s d noiseCount .occurrenceCount
    | .scratch => .copyScratch
    | .current j => current k s d noiseCount j
    | .remaining j => remaining k s d noiseCount j
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [headerTape, current, remaining]

@[simp] theorem odometerSlots_radix : odometerSlots k s d noiseCount .radix =
    headerTape k s d noiseCount .occurrenceCount := rfl
@[simp] theorem odometerSlots_scratch : odometerSlots k s d noiseCount .scratch = .copyScratch := rfl
@[simp] theorem odometerSlots_current (j : Fin k) :
    odometerSlots k s d noiseCount (.current j) = .savedIndex j.rev := rfl
@[simp] theorem odometerSlots_remaining (j : Fin k) :
    odometerSlots k s d noiseCount (.remaining j) = remaining k s d noiseCount j := rfl

theorem current_ne_remaining (j l : Fin k) :
    current k s d noiseCount j ≠ remaining k s d noiseCount l := by simp [current, remaining]
theorem current_ne_finalOutput (j : Fin k) :
    current k s d noiseCount j ≠ finalOutput k s d noiseCount := by simp [current, finalOutput]
theorem remaining_ne_finalOutput (j : Fin k) :
    remaining k s d noiseCount j ≠ finalOutput k s d noiseCount := by simp [remaining, finalOutput]

theorem headerTape_ne_finalOutput (c : MachineAddressHeaders.Arithmetic.Control) :
    headerTape k s d noiseCount c ≠ finalOutput k s d noiseCount := by
  simp [headerTape, finalOutput]

theorem headerTape_ne_current (c : MachineAddressHeaders.Arithmetic.Control) (j : Fin k) :
    headerTape k s d noiseCount c ≠ current k s d noiseCount j := by
  simp [headerTape, current]

theorem headerTape_ne_remaining (c : MachineAddressHeaders.Arithmetic.Control) (j : Fin k) :
    headerTape k s d noiseCount c ≠ remaining k s d noiseCount j := by
  simp [headerTape, remaining]

theorem tupleOutput_headerTape (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple base k (headerTape k s d noiseCount c) =
      base (headerTape k s d noiseCount c) :=
  MachineSourceTuple.stageTapes_frame F tuple base k _
    (by simp [headerTape])
    (by simp [headerTape])
    (by intros; simp [headerTape])

end UniqueGamesTheorem.Reduction.AddressMachineSpace

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressOdometerSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Reduction.AddressOdometerSchedule

open Turing
open UniqueGamesTheorem.Foundations.Complexity MachineTupleOdometer
open UniqueGamesTheorem.Foundations.Hastad
open MachineTransfer


noncomputable section

abbrev Tape := AddressMachineSpace.Tape

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def current (k s d noiseCount : Nat) (i : Fin k) : Tape k s d noiseCount :=
  AddressMachineSpace.current k s d noiseCount i

def remaining (k s d noiseCount : Nat) (i : Fin k) : Tape k s d noiseCount :=
  AddressMachineSpace.remaining k s d noiseCount i

def accumulator (k s d noiseCount : Nat) : Tape k s d noiseCount :=
  AddressMachineSpace.headerTape k s d noiseCount .reversed

def currentAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then current k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

def remainingAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then remaining k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

@[simp] theorem current_eq_iff (i j : Fin k) :
    current k s d noiseCount i = current k s d noiseCount j ↔ i = j := by
  simp [current, AddressMachineSpace.current]
@[simp] theorem remaining_eq_iff (i j : Fin k) :
    remaining k s d noiseCount i = remaining k s d noiseCount j ↔ i = j := by
  simp [remaining, AddressMachineSpace.remaining]
@[simp] theorem current_ne_remaining (i j : Fin k) :
    current k s d noiseCount i ≠ remaining k s d noiseCount j :=
  AddressMachineSpace.current_ne_remaining k s d noiseCount i j
@[simp] theorem remaining_ne_current (i j : Fin k) :
    remaining k s d noiseCount i ≠ current k s d noiseCount j :=
  Ne.symm (current_ne_remaining j i)
@[simp] theorem accumulator_ne_current (i : Fin k) :
    accumulator k s d noiseCount ≠ current k s d noiseCount i :=
  AddressMachineSpace.headerTape_ne_current k s d noiseCount .reversed i
@[simp] theorem accumulator_ne_remaining (i : Fin k) :
    accumulator k s d noiseCount ≠ remaining k s d noiseCount i :=
  AddressMachineSpace.headerTape_ne_remaining k s d noiseCount .reversed i
@[simp] theorem current_ne_accumulator (i : Fin k) :
    current k s d noiseCount i ≠ accumulator k s d noiseCount := Ne.symm (accumulator_ne_current i)
@[simp] theorem remaining_ne_accumulator (i : Fin k) :
    remaining k s d noiseCount i ≠ accumulator k s d noiseCount := Ne.symm (accumulator_ne_remaining i)

/-- Odometer coordinate zero is the low coordinate; physical saved positions
are reversed to match the actual occurrence-tuple enumeration. -/
def setDigits (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape k s d noiseCount → List Bool) : Tape k s d noiseCount → List Bool
  | .savedIndex i => if h : i.rev.val < q then encodeWord (digits ⟨i.rev.val, h⟩)
      else base (.savedIndex i)
  | .extra (.inr (.inr (.inl i))) => if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (.extra (.inr (.inr (.inl i))))
  | tape => base tape

def setAcc (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    Tape k s d noiseCount → List Bool := Function.update base (accumulator k s d noiseCount) bits

def putDigit (i : Fin k) (base : Tape k s d noiseCount → List Bool) (a r : Nat) :
    Tape k s d noiseCount → List Bool :=
  digitTapes (current k s d noiseCount i) (remaining k s d noiseCount i) base a r [] []

@[simp] theorem setDigits_current (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (i : Fin k) :
    setDigits m digits base (current k s d noiseCount i) =
      if h : i.val < q then encodeWord (digits ⟨i.val, h⟩) else base (current k s d noiseCount i) := by
  simp [setDigits, current, AddressMachineSpace.current]
@[simp] theorem setDigits_remaining (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (i : Fin k) :
    setDigits m digits base (remaining k s d noiseCount i) =
      if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (remaining k s d noiseCount i) := rfl

theorem setDigits_other (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (tape : Tape k s d noiseCount)
    (hc : ∀ i, tape ≠ current k s d noiseCount i)
    (hr : ∀ i, tape ≠ remaining k s d noiseCount i) : setDigits m digits base tape = base tape := by
  cases tape with
  | savedIndex i => exact (hc i.rev (by simp [current, AddressMachineSpace.current])).elim
  | extra e =>
    rcases e with a | a
    · rfl
    · rcases a with a | a
      · rfl
      · rcases a with i | unused
        · exact (hr i rfl).elim
        · rfl
  | _ => rfl

theorem digitCases {P : Tape k s d noiseCount → Prop} (tape : Tape k s d noiseCount)
    (hc : ∀ i, P (current k s d noiseCount i))
    (hr : ∀ i, P (remaining k s d noiseCount i))
    (other : ∀ tape, (∀ i, tape ≠ current k s d noiseCount i) →
      (∀ i, tape ≠ remaining k s d noiseCount i) → P tape) : P tape := by
  classical
  by_cases h : ∃ i, tape = current k s d noiseCount i
  · obtain ⟨i, rfl⟩ := h; exact hc i
  · by_cases h' : ∃ i, tape = remaining k s d noiseCount i
    · obtain ⟨i, rfl⟩ := h'; exact hr i
    · exact other tape (fun i hi => h ⟨i, hi⟩) (fun i hi => h' ⟨i, hi⟩)

@[simp] theorem setDigits_zero (m : Nat) (digits : Fin 0 → Nat)
    (base : Tape k s d noiseCount → List Bool) : setDigits m digits base = base := by
  funext tape
  apply digitCases tape
  · intro i; simp
  · intro i; simp
  · intro tape hc hr; exact setDigits_other m digits base tape hc hr

@[simp] theorem setDigits_accumulator (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) :
    setDigits m digits base (accumulator k s d noiseCount) = base (accumulator k s d noiseCount) := rfl

@[simp] theorem setAcc_self (base : Tape k s d noiseCount → List Bool) :
    setAcc base (base (accumulator k s d noiseCount)) = base := by simp [setAcc]
@[simp] theorem setAcc_setAcc (base : Tape k s d noiseCount → List Bool) (first second : List Bool) :
    setAcc (setAcc base first) second = setAcc base second := by simp [setAcc]
@[simp] theorem setAcc_apply (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    setAcc base bits (accumulator k s d noiseCount) = bits := by simp [setAcc]

theorem setDigits_setAcc (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc base bits) = setAcc (setDigits m digits base) bits := by
  funext tape
  apply digitCases tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [setDigits_other m digits _ tape hc hr, setAcc, ha]

@[simp] theorem putDigit_current (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (i : Fin k) :
    putDigit j base a r (current k s d noiseCount i) =
      if i = j then encodeWord a else base (current k s d noiseCount i) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Function.update_apply]
@[simp] theorem putDigit_remaining (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (i : Fin k) :
    putDigit j base a r (remaining k s d noiseCount i) =
      if i = j then encodeWord r else base (remaining k s d noiseCount i) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Function.update_apply]

theorem putDigit_other (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (tape : Tape k s d noiseCount)
    (hc : tape ≠ current k s d noiseCount j) (hr : tape ≠ remaining k s d noiseCount j) :
    putDigit j base a r tape = base tape := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hc, hr]

@[simp] theorem putDigit_accumulator (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) : putDigit j base a r (accumulator k s d noiseCount) =
      base (accumulator k s d noiseCount) := by
  apply putDigit_other <;> simp

theorem putDigit_setAcc (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (bits : List Bool) :
    putDigit j (setAcc base bits) a r = setAcc (putDigit j base a r) bits := by
  funext tape
  apply digitCases tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [putDigit_other j _ a r tape (hc j) (hr j), setAcc, ha]

theorem setDigits_putDigit (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (a r : Nat) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a r := by
  funext tape
  apply digitCases tape
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro tape hc hr
    simp [setDigits_other m digits _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m (Fin.snoc digits a) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a (m - 1 - a) := by
  funext tape
  apply digitCases tape
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro tape hc hr
    simp [setDigits_other m _ _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc_base (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a (m - 1 - a)) =
      setDigits m (Fin.snoc digits a) base := by
  rw [setDigits_putDigit, setDigits_snoc]

@[simp] theorem setDigits_savedIndex (m : Nat) (digits : Fin k → Nat)
    (base : Tape k s d noiseCount → List Bool) (j : Fin k) :
    setDigits m digits base (.savedIndex j) = encodeWord (digits j.rev) := by
  have h : j.rev.val < k := j.rev.isLt
  simp only [setDigits, h, dite_eq_left]

@[simp] theorem setAcc_other (base : Tape k s d noiseCount → List Bool)
    (bits : List Bool) (tape : Tape k s d noiseCount)
    (h : tape ≠ accumulator k s d noiseCount) : setAcc base bits tape = base tape := by
  simp [setAcc, h]

def allBits {q : ℕ} (bits : (Fin q → Fin m) → List Bool) : List Bool :=
  (tupleOrder m q).flatMap bits

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

def blocks {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) (d : ℕ) : List Bool :=
  if h : d < m then allBits (fun c => bits (Fin.snoc c ⟨d, h⟩)) else []

theorem blockPrefix_all {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) :
    blockPrefix (blocks bits) m = allBits bits := by
  rw [blockPrefix_eq_ofFn]
  simp only [blocks, Fin.isLt, ↓reduceDIte, allBits, tupleOrder_snoc]
  simp only [List.flatMap_assoc, List.flatMap_map]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]

def configuration (label : Λ) (canonical : σ) (tapes : Tape k s d noiseCount → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ := ⟨some label, (canonical, none), tapes⟩

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ)
    {q : ℕ} (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc base ((bits c).reverse ++ output))))

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (digit : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c digit i).val) =
      Fin.snoc (fun i => (c i).val) digit.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) : Configuration (Tape k s d noiseCount) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc base ((allBits bits).reverse ++ base (accumulator k s d noiseCount))))

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ k)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (accumulator k s d noiseCount))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt k s d noiseCount)
      (remaining := remainingAt k s d noiseCount) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical base bits) count rfl rfl hrun
    exact ⟨tree, by
      dsimp only [tree]
      erw [NestedCycle.LeafBound]
      exact hcount⟩
  | succ q ih =>
    have hqu : q < k := by omega
    let schedule : CycleSchedule (Tape k s d noiseCount) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (accumulator k s d noiseCount))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
            (checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.register schedule.base), tree.LeafBound B := by
      let digit : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c digit)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (accumulator k s d noiseCount)))
        digit.val (m - 1 - digit.val)
      have hrem : m - 1 - digit.val = r.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = digit.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = digit.val + 1 := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, digit.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c digit) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical childBase childBits =
          checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
            schedule.ambient schedule.register schedule.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_accumulator, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) schedule children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, schedule,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        finalConfiguration (next (q + 1)) canonical base bits := by
      simp only [cycleExit, finalConfiguration, configuration, schedule, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
        (cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

/-- The time bound is derived from the concrete schedule, not from the number
of tuples alone. Dimension zero consists of its single actual body trace. -/
theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B : ℕ) (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin k → Fin m) → List Bool)
    (atCheck : ∀ i, i < k → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < k → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) k bodyLabel canonical base)
      (some (finalConfiguration (next k) canonical base bits))
      ((B + 2 * k) * m ^ k)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical
    positive B k (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

@[simp] theorem initial_current (base : Tape k s d noiseCount → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin k) :
    (initialConfiguration (m := m) k bodyLabel canonical base).stk (current k s d noiseCount i) =
      encodeWord 0 := by simp [initialConfiguration, configuration]

@[simp] theorem initial_remaining (base : Tape k s d noiseCount → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin k) :
    (initialConfiguration (m := m) k bodyLabel canonical base).stk (remaining k s d noiseCount i) =
      encodeWord (m - 1) := by simp [initialConfiguration, configuration]

@[simp] theorem final_current (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) (i : Fin k) :
    (finalConfiguration exitLabel canonical base bits).stk (current k s d noiseCount i) =
      encodeWord 0 := by simp [finalConfiguration, configuration]

@[simp] theorem final_remaining (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) (i : Fin k) :
    (finalConfiguration exitLabel canonical base bits).stk (remaining k s d noiseCount i) =
      encodeWord (m - 1) := by simp [finalConfiguration, configuration]

@[simp] theorem final_accumulator (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical base bits).stk (accumulator k s d noiseCount) =
      ((tupleOrder m k).flatMap bits).reverse ++ base (accumulator k s d noiseCount) := by
  simp [finalConfiguration, configuration, allBits]

/-- Traversal frames every tape outside the digits and reversed output. -/
theorem final_other (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ) (bits : (Fin k → Fin m) → List Bool)
    (tape : Tape k s d noiseCount)
    (hc : ∀ i, tape ≠ current k s d noiseCount i)
    (hr : ∀ i, tape ≠ remaining k s d noiseCount i)
    (ha : tape ≠ accumulator k s d noiseCount) :
    (finalConfiguration exitLabel canonical base bits).stk tape = base tape := by
  simp only [finalConfiguration, configuration, setDigits_other m _ _ tape hc hr,
    setAcc_other _ _ tape ha]

end
end UniqueGamesTheorem.Reduction.AddressOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_OutputTranslationsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Executable direct addresses for the actual canonical game. Every original
edge occurrence and its translation table is retained, in the same order.
Addresses not representing realized bodies are isolated vertices. No vertex
list, duplicate removal, or inverse enumeration is evaluated by the output. -/

namespace UniqueGamesTheorem.Reduction.AddressGame

open ActualSource
open Foundations.Target
open Integration.VertexEmbedding

abbrev bodyCapacity (S : Source) (k s d : Nat) : Nat :=
  CanonicalAddress.capacity S.variables S.occurrences k s d

def vertexCount (S : Source) (k s d : Nat) : Nat := 2 * bodyCapacity S k s d

/-- Both bipartite sides remain distinct address blocks. -/
def vertexAddress (S : Source) (k s d : Nat) (v : ActualGame.TwoSidedVertex S k s d) :
    Fin (vertexCount S k s d) :=
  Encoding.sideEquiv (bodyCapacity S k s d) (v.1, CanonicalAddress.bodyAddress v.2.val)

/-- This is the endpoint routine used at runtime: canonicalize, serialize,
apply Horner radix arithmetic, and add the side block. -/
def queryAddress (S : Source) (k s d : Nat) (side : Bool) (q : ActualGame.Query S k s d) :
    Fin (vertexCount S k s d) :=
  Encoding.sideEquiv (bodyCapacity S k s d)
    (side, CanonicalAddress.bodyAddress (ActualOrbit.body (ActualGame.canonical S k s d) q))

@[simp] theorem vertexAddress_query (S : Source) (k s d : Nat) (side : Bool)
    (q : ActualGame.Query S k s d) :
    vertexAddress S k s d (side, ActualGame.vertex S k s d q) =
      queryAddress S k s d side q := rfl

def addressEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : ActualGame.Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := queryAddress S k s d false (ActualGame.leftQuery S k g ω)
  target := queryAddress S k s d true (ActualGame.rightQuery S k g ω)
  permutation := Encoding.translationTable
    (ActualGame.offset S k s d (ActualGame.leftQuery S k g ω))
    (ActualGame.offset S k s d (ActualGame.rightQuery S k g ω))

@[simp] theorem addressEdge_permutation (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    (addressEdge S k g ω).permutation = (ActualGame.explicitEdge S k g ω).permutation := rfl

/-- Only canonical words, bounded radix arithmetic, and the explicit outcome
list occur in the runtime path. The correcting function is not inspected. -/
def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (addressEdge S k g)
  nonempty h := by
    have hempty := List.map_eq_nil_iff.mp h
    apply (ActualGame.outputInstanceWithEnumeration S k g en).nonempty
    change (ActualGame.explicitOutcomes S k g en).map (ActualGame.explicitEdge S k g) = []
    rw [hempty]
    rfl

@[simp] theorem outputInstance_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstance S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstance, List.length_map, ActualGame.explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

/-- The concrete vector-table interface contains no correcting-map witness. -/
def tableOutput (S : Source) (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    Instance (2^s) :=
  outputInstance S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

end UniqueGamesTheorem.Reduction.AddressGame

end

section

namespace UniqueGamesTheorem.Reduction.AddressByteSemantics

open Integration.BinaryLinear Foundations.Complexity ActualSource

def queryWords {k s d : Nat} (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) : List Nat :=
  CanonicalBodyTemplate.evalTemplate fields
    (CanonicalBodyTemplate.template (X (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple X) b)

def queryRank {k s d : Nat} (base : Nat) (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) : Nat :=
  CanonicalAddress.radix base (queryWords fields X b)

def permutationWords {k s d : Nat} (X Y : ActualGame.Map k s d)
    (b : Fin k → F2) : List Nat :=
  tableWords (Encoding.translationTable
    (CanonicalBodyTemplate.alphabetOffset (X (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple X) b)
    (CanonicalBodyTemplate.alphabetOffset (Y (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple Y) b))

def edgeWords {k s d : Nat} (base capacity : Nat) (fields : Fin k → Fin 4 → Nat)
    (X Y : ActualGame.Map k s d) (b : Fin k → F2) : List Nat :=
  [queryRank base fields X b, capacity + queryRank base fields Y b] ++
    permutationWords X Y b

def edgeBits {k s d : Nat} (base capacity : Nat) (fields : Fin k → Fin 4 → Nat)
    (X Y : ActualGame.Map k s d) (b : Fin k → F2) : List Bool :=
  encodeWords (edgeWords base capacity fields X Y b)

@[simp] theorem queryWords_length {k s d : Nat} (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) :
    (queryWords fields X b).length = 1 + 9*k := by
  simp only [queryWords, CanonicalBodyTemplate.evalTemplate, List.length_map,
    CanonicalBodyTemplate.template_length]

@[simp] theorem permutationWords_length {k s d : Nat} (X Y : ActualGame.Map k s d)
    (b : Fin k → F2) : (permutationWords X Y b).length = 2^s :=
  tableWords_length _

theorem queryWords_actual (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    queryWords (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) =
      CanonicalEncoding.bodyWords (ActualOrbit.body (ActualGame.canonical S k s d) q) :=
  CanonicalBodyTemplate.eval_actualQuery S q

theorem queryAddress_false (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (AddressGame.queryAddress S k s d false q).val =
      queryRank (CanonicalAddress.base S.variables S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_false_val _

theorem queryAddress_true (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (AddressGame.queryAddress S k s d true q).val =
      AddressGame.bodyCapacity S k s d +
      queryRank (CanonicalAddress.base S.variables S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_true_val _

/-- Exact full serialized edge, including every forward permutation image. -/
theorem addressEdge_words (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    constraintWords (AddressGame.addressEdge S k g omega) =
      edgeWords (CanonicalAddress.base S.variables S.occurrences s d)
        (AddressGame.bodyCapacity S k s d)
        (CanonicalBodyTemplate.sourceFields omega.1.1 (ActualGame.names S))
        omega.1.2 (ActualGame.rightQuery S k g omega).2
        (fun j => ActualGame.rhs S (omega.1.1 j)) := by
  unfold constraintWords
  change [ (AddressGame.queryAddress S k s d false (ActualGame.leftQuery S k g omega)).val,
      (AddressGame.queryAddress S k s d true (ActualGame.rightQuery S k g omega)).val ] ++ _ = _
  rw [queryAddress_false, queryAddress_true]
  rfl

theorem addressEdge_bits (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    encodeWords (constraintWords (AddressGame.addressEdge S k g omega)) =
      edgeBits (CanonicalAddress.base S.variables S.occurrences s d)
        (AddressGame.bodyCapacity S k s d)
        (CanonicalBodyTemplate.sourceFields omega.1.1 (ActualGame.names S))
        omega.1.2 (ActualGame.rightQuery S k g omega).2
        (fun j => ActualGame.rhs S (omega.1.1 j)) := by
  rw [addressEdge_words]
  rfl

/-- The actual edge emitter's three payloads concatenate to the codec exactly. -/
theorem edgeBits_split {k s d : Nat} (base capacity : Nat)
    (fields : Fin k → Fin 4 → Nat) (X Y : ActualGame.Map k s d) (b : Fin k → F2) :
    edgeBits base capacity fields X Y b =
      encodeWords [queryRank base fields X b, capacity + queryRank base fields Y b] ++
        encodeWords (permutationWords X Y b) := by
  exact encodeWords_append _ _

end UniqueGamesTheorem.Reduction.AddressByteSemantics

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_FixedOutcomes
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration UniqueGamesTheorem.Reduction.Explicit

variable {N : Type*}

abbrev Parameter (k s d : Nat) (N : Type*) :=
  (E k →ₗ[F2] ActualEnumeration.Ambient s d) × (N × (E k →ₗ[F2] F2))

/-- Ambient linear map, noise occurrence index, scalar linear functional,
in exactly the original nested enumeration order. -/
def fixedParams (k s d : Nat) (indices : List N) : List (Parameter k s d N) :=
  pairs (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))

def assemble {m k s d : Nat} (U : Fin k → Fin m) (p : Parameter k s d N) :
    Query m k s d × (N × (E k →ₗ[F2] F2)) :=
  ((U, p.1), p.2)

theorem indexedOutcomes_factor (m k s d : Nat) (indices : List N) :
    ActualEnumeration.indexedOutcomes m k s d indices =
      (occurrenceTuples m k).flatMap (fun U => (fixedParams k s d indices).map (assemble U)) := by
  exact pairs_associate (functions (List.finRange m) k)
    (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))

theorem fixedParams_length (k s d : Nat) (indices : List N) :
    (fixedParams k s d indices).length = 2^((2*k+1)*(s+d+1)) * indices.length := by
  simp only [fixedParams, length_pairs, length_allLinearMaps, length_ambientVectors,
    List.length_cons, List.length_nil, ← pow_mul]
  change 2^((s+d)*(2*k+1)) * (indices.length * 2^(2*k+1)) =
    2^((2*k+1)*(s+d+1)) * indices.length
  rw [show (2*k+1)*(s+d+1) = (s+d)*(2*k+1)+(2*k+1) by ring, pow_add]
  ring

def tableParams (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    List (Parameter k s d (Fin T.vectors.length)) :=
  fixedParams k s d (List.finRange T.vectors.length)

theorem tableParams_length (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    (tableParams k T).length = 2^((2*k+1)*(s+d+1)) * T.vectors.length := by
  simp only [tableParams, fixedParams_length, List.length_finRange]

theorem outputInstance_constraints (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (AddressGame.outputInstance S k g en).constraints =
      (occurrenceTuples S.occurrences k).flatMap (fun U =>
        (fixedParams k s d en.indices).map (fun p =>
          AddressGame.addressEdge S k g (assemble U p))) := by
  change (ActualEnumeration.indexedOutcomes S.occurrences k s d en.indices).map
    (AddressGame.addressEdge S k g) = _
  rw [indexedOutcomes_factor]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

theorem tableOutput_constraints (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    (AddressGame.tableOutput S k T).constraints =
      (occurrenceTuples S.occurrences k).flatMap (fun U =>
        (tableParams k T).map (fun p => AddressGame.addressEdge S k
          (Integration.TableReduction.tableSkeleton T) (assemble U p))) :=
  outputInstance_constraints S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

end UniqueGamesTheorem.Reduction.FixedOutcomes

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressOutcomeSpecs
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

abbrev Parameter (k : Nat) {sourceDimension targetDimension : Nat}
    (T : NoiseTables.Table sourceDimension targetDimension) :=
  FixedOutcomes.Parameter k sourceDimension targetDimension (Fin T.vectors.length)

def bitVector {k : Nat} (b : Fin k → Bool) : Fin k → F2 := fun j => ofBit (b j)

def rightMap {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T) :
    ActualGame.Map k s d := p.1 + p.2.2.smulRight (T.vectors.get p.2.1)

def row {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T)
    (b : Fin k → Bool) : Spec k where
  left := CanonicalBodyMachine.template (p.1 (ActualHomogeneous.hBasis k))
    (ActualCanonical.standardTriple p.1) (bitVector b)
  right := CanonicalBodyMachine.template (rightMap T p (ActualHomogeneous.hBasis k))
    (ActualCanonical.standardTriple (rightMap T p)) (bitVector b)
  permutation := encodeWords (AddressByteSemantics.permutationWords p.1 (rightMap T p) (bitVector b))

def rows (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    List (MachineOutcomeRows.Row k (4*k) (1+9*k)) :=
  (FixedOutcomes.tableParams k T).map (row T)

@[simp] theorem row_left_length {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) : (row T p b).left.length = 1+9*k :=
  CanonicalBodyMachine.template_length _ _ _

@[simp] theorem row_right_length {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) : (row T p b).right.length = 1+9*k :=
  CanonicalBodyMachine.template_length _ _ _

@[simp] theorem rows_length (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    (rows k T).length = 2^((2*k+1)*(s+d+1)) * T.vectors.length := by
  simp only [rows, List.length_map, FixedOutcomes.tableParams_length]

@[simp] theorem selected_rows (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (b : Fin k → Bool) :
    MachineOutcomeRows.selected (rows k T) b =
      (FixedOutcomes.tableParams k T).map (fun p => row T p b) := by
  simp only [MachineOutcomeRows.selected, rows, List.map_map, Function.comp_def]

def values {k : Nat} (fields : Fin k → Fin 4 → Nat) (spec : Spec k) : Values k where
  left := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields))).val
  right := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields))).val
  left_length := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields))).property
  right_length := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields))).property

theorem row_left_output {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T)
    (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    MachineFieldTemplate.templateOutput (row T p b).left (CanonicalBodyMachine.savedFields fields) =
      encodeWords (AddressByteSemantics.queryWords fields p.1 (bitVector b)) :=
  CanonicalBodyMachine.templateOutput_lowerTemplate fields _

theorem row_right_output {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T)
    (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    MachineFieldTemplate.templateOutput (row T p b).right (CanonicalBodyMachine.savedFields fields) =
      encodeWords (AddressByteSemantics.queryWords fields (rightMap T p) (bitVector b)) :=
  CanonicalBodyMachine.templateOutput_lowerTemplate fields _

@[simp] theorem values_row_left {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    (values fields (row T p b)).left =
      AddressByteSemantics.queryWords fields p.1 (bitVector b) := by
  change (interpreted (1+9*k) _).val = _
  rw [row_left_output]
  exact interpreted_encoded _ _ (AddressByteSemantics.queryWords_length _ _ _)

@[simp] theorem values_row_right {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    (values fields (row T p b)).right =
      AddressByteSemantics.queryWords fields (rightMap T p) (bitVector b) := by
  change (interpreted (1+9*k) _).val = _
  rw [row_right_output]
  exact interpreted_encoded _ _ (AddressByteSemantics.queryWords_length _ _ _)

theorem correct_rows {k s d : Nat} (T : NoiseTables.Table s d)
    (fields : Fin k → Fin 4 → Nat) (b : Fin k → Bool) :
    ∀ spec ∈ MachineOutcomeRows.selected (rows k T) b,
      MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields) =
        encodeWords (values fields spec).left ∧
      MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields) =
        encodeWords (values fields spec).right := by
  rw [selected_rows]
  intro spec hspec
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hspec
  constructor
  · rw [values_row_left]
    exact row_left_output T p b fields
  · rw [values_row_right]
    exact row_right_output T p b fields

theorem payload_row {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat)
    (B C : Nat) :
    MachineOutcomeRows.payload B C (values fields) (row T p b) =
      AddressByteSemantics.edgeBits B C fields p.1 (rightMap T p) (bitVector b) := by
  unfold MachineOutcomeRows.payload MachineAddressEdge.edgeBits
  rw [values_row_left, values_row_right, AddressByteSemantics.edgeBits_split]
  rfl

def rhsBits (S : Source) {k : Nat} (U : ActualGame.Question S k) : Fin k → Bool :=
  fun j => (S.equation (U j)).rhs

@[simp] theorem bitVector_rhsBits (S : Source) {k : Nat} (U : ActualGame.Question S k) :
    bitVector (rhsBits S U) = fun j => ActualGame.rhs S (U j) := rfl

theorem rightMap_actual (S : Source) {k s d : Nat} (T : NoiseTables.Table s d)
    (U : ActualGame.Question S k) (p : Parameter k T) :
    rightMap T p =
      (ActualGame.rightQuery S k (TableReduction.tableSkeleton T) (FixedOutcomes.assemble U p)).2 := rfl

/-- Each static row emits exactly the concrete game's constraint encoding. -/
theorem payload_row_actual (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (U : ActualGame.Question S k) (p : Parameter k T) :
    MachineOutcomeRows.payload
        (CanonicalAddress.base S.variables S.occurrences s d) (AddressGame.bodyCapacity S k s d)
        (values (CanonicalBodyTemplate.sourceFields U (ActualGame.names S)))
        (row T p (rhsBits S U)) =
      encodeWords (constraintWords (AddressGame.addressEdge S k (TableReduction.tableSkeleton T)
        (FixedOutcomes.assemble U p))) := by
  rw [payload_row, bitVector_rhsBits, rightMap_actual S T U p]
  exact (AddressByteSemantics.addressEdge_bits S k (TableReduction.tableSkeleton T)
    (FixedOutcomes.assemble U p)).symm

def tupleBits (S : Source) (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (U : ActualGame.Question S k) : List Bool :=
  (FixedOutcomes.tableParams k T).flatMap (fun p =>
    encodeWords (constraintWords (AddressGame.addressEdge S k (TableReduction.tableSkeleton T)
      (FixedOutcomes.assemble U p))))

theorem tuplePayload_actual (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (U : ActualGame.Question S k) :
    (MachineOutcomeRows.selected (rows k T) (rhsBits S U)).flatMap
        (MachineOutcomeRows.payload
          (CanonicalAddress.base S.variables S.occurrences s d) (AddressGame.bodyCapacity S k s d)
          (values (CanonicalBodyTemplate.sourceFields U (ActualGame.names S)))) =
      tupleBits S k T U := by
  rw [selected_rows, List.flatMap_map]
  simp only [payload_row_actual, tupleBits]
  rfl

/-- Complete output-byte factorization used by the actual outer loop. -/
theorem gameBits_factor (S : Source) (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    gameBits (AddressGame.tableOutput S k T) =
      encodeWords [(AddressGame.tableOutput S k T).vertices, 2^s,
        (AddressGame.tableOutput S k T).constraints.length] ++
      (FixedOutcomes.occurrenceTuples S.occurrences k).flatMap (tupleBits S k T) := by
  rw [gameBits, gameWords, encodeWords_append, encodeWords_flatMap]
  rw [FixedOutcomes.tableOutput_constraints]
  erw [List.flatMap_assoc]
  congr 1
  apply List.flatMap_congr
  intro U _
  erw [List.flatMap_map]
  rfl

end UniqueGamesTheorem.Reduction.AddressOutcomeSpecs

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressTupleCleanupLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Integration.AddressTupleCleanup

open Turing UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Complexity

variable (k s d noiseCount : Nat)

/-- The executable field order is slot-major within each tuple position. -/
def loadedFields : List (AddressMachineSpace.Tape k s d noiseCount) :=
  List.ofFn (fun i : Fin (4 * k) =>
    MachineSourceTuple.Tape.field ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2)

@[simp] theorem loadedFields_length : (loadedFields k s d noiseCount).length = 4 * k := by
  simp only [loadedFields, List.length_ofFn]

theorem mem_loadedFields (tape : AddressMachineSpace.Tape k s d noiseCount) :
    tape ∈ loadedFields k s d noiseCount ↔
      ∃ position : Fin k, ∃ slot : Fin 4, tape = .field position slot := by
  unfold loadedFields
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact ⟨((CanonicalBodyMachine.fieldEquiv k).symm i).1,
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2, hi.symm⟩
  · rintro ⟨position, slot, rfl⟩
    apply List.mem_ofFn.mpr
    refine ⟨CanonicalBodyMachine.fieldEquiv k (position, slot), ?_⟩
    simp only [Equiv.symm_apply_apply]

abbrev Label := MachineDrainMany.Label (loadedFields k s d noiseCount)

noncomputable abbrev cleared (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.finalTapes (loadedFields k s d noiseCount) base

/-- Proof-side cost on the shared arena. Its arithmetic-header tape dimensions
use the fixed polynomial coefficient representation in `PolynomialMachine`.
The executable drain list, entry, and instructions do not evaluate this cost. -/
noncomputable abbrev steps (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.steps (loadedFields k s d noiseCount) base

noncomputable abbrev budget (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.lengthSum (loadedFields k s d noiseCount) base + 4 * k

@[simp] theorem cleared_field (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (position : Fin k) (slot : Fin 4) :
    cleared k s d noiseCount base (.field position slot) = [] :=
  MachineDrainMany.finalTapes_mem (loadedFields k s d noiseCount) base (.field position slot)
    ((mem_loadedFields k s d noiseCount _).2 ⟨position, slot, rfl⟩)

/-- Every tape outside the physical loaded fields is preserved verbatim. -/
theorem cleared_outside (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (tape : AddressMachineSpace.Tape k s d noiseCount)
    (outside : ∀ position : Fin k, ∀ slot : Fin 4, tape ≠ .field position slot) :
    cleared k s d noiseCount base tape = base tape := by
  apply MachineDrainMany.finalTapes_not_mem
  intro h
  obtain ⟨position, slot, same⟩ := (mem_loadedFields k s d noiseCount tape).1 h
  exact outside position slot same

@[simp] theorem cleared_source (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .source = base .source := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_savedIndex
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) (position : Fin k) :
    cleared k s d noiseCount base (.savedIndex position) = base (.savedIndex position) := by
  apply cleared_outside
  intro other slot h
  cases h

@[simp] theorem cleared_extra (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (extra : AddressMachineSpace.Extra k s d noiseCount) :
    cleared k s d noiseCount base (.extra extra) = base (.extra extra) := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_index (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .index = base .index := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_work (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .work = base .work := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_scratch (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .scratch = base .scratch := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_copyScratch (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .copyScratch = base .copyScratch := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_headerTape
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (header : MachineAddressHeaders.Arithmetic.Control) :
    cleared k s d noiseCount base (AddressMachineSpace.headerTape k s d noiseCount header) =
      base (AddressMachineSpace.headerTape k s d noiseCount header) := by
  simpa only [AddressMachineSpace.headerTape, AddressMachineSpace.headerArithmeticSlots] using
    cleared_extra k s d noiseCount base (.inl (.inl header))

@[simp] theorem cleared_current (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (position : Fin k) :
    cleared k s d noiseCount base (AddressMachineSpace.current k s d noiseCount position) =
      base (AddressMachineSpace.current k s d noiseCount position) := by
  simpa only [AddressMachineSpace.current] using
    cleared_savedIndex k s d noiseCount base position.rev

@[simp] theorem cleared_remaining (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (position : Fin k) :
    cleared k s d noiseCount base (AddressMachineSpace.remaining k s d noiseCount position) =
      base (AddressMachineSpace.remaining k s d noiseCount position) := by
  simpa only [AddressMachineSpace.remaining] using
    cleared_extra k s d noiseCount base (.inr (.inr (.inl position)))

@[simp] theorem cleared_finalOutput
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base (AddressMachineSpace.finalOutput k s d noiseCount) =
      base (AddressMachineSpace.finalOutput k s d noiseCount) := by
  simpa only [AddressMachineSpace.finalOutput] using
    cleared_extra k s d noiseCount base (.inr (.inr (.inr ())))

theorem steps_le (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    steps k s d noiseCount base ≤ budget k s d noiseCount base := by
  simpa only [loadedFields_length] using
    MachineDrainMany.steps_le (loadedFields k s d noiseCount) base

variable {Λ : Type}

abbrev entry (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :=
  MachineDrainMany.entry (loadedFields k s d noiseCount) labels exit

/-- Fixed concrete drain instructions on the actual shared address state. -/
def instruction (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :
    Label k s d noiseCount → TM2.Stmt
      (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool) Λ (AddressMachineSpace.State k) :=
  MachineDrainMany.instruction (loadedFields k s d noiseCount) labels exit

theorem trace (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[steps k s d noiseCount base]
      (some ⟨entry k s d noiseCount labels exit, (control, register), base⟩) =
    some ⟨exit, (control, MachineDrainMany.finalRegister (loadedFields k s d noiseCount) register),
      cleared k s d noiseCount base⟩ :=
  MachineDrainMany.trace (loadedFields k s d noiseCount) labels exit program atLabels
    base control register

noncomputable def execution (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry k s d noiseCount labels exit, (control, register), base⟩
      (some ⟨exit,
        (control, MachineDrainMany.finalRegister (loadedFields k s d noiseCount) register),
        cleared k s d noiseCount base⟩) (budget k s d noiseCount base) where
  steps := steps k s d noiseCount base
  evals_in_steps := trace k s d noiseCount labels exit program atLabels base control register
  steps_le_m := steps_le k s d noiseCount base

end UniqueGamesTheorem.Integration.AddressTupleCleanup

end

section

namespace UniqueGamesTheorem.Integration.AddressTupleLoaded

open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Complexity

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

variable {k s d noiseCount : Nat}

/-- The explicit field assignment performed by all `k` real lookup stages.
Unrelated tapes, including the loader's empty index/work tapes, are unchanged. -/
def fieldAssignment (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool
  | .field j slot => encodeWord
      ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) ++
        baseArena (.field j slot)
  | tape => baseArena tape

theorem stageTapes_eq (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hindex : baseArena .index = []) (hwork : baseArena .work = []) :
    MachineSourceTuple.stageTapes F tuple baseArena k = fieldAssignment F tuple baseArena := by
  funext tape
  cases tape with
  | index => exact (MachineSourceTuple.stageTapes_clean F tuple baseArena k hindex hwork).1.trans hindex.symm
  | work => exact (MachineSourceTuple.stageTapes_clean F tuple baseArena k hindex hwork).2.trans hwork.symm
  | field j slot =>
    simp only [MachineSourceTuple.stageTapes_field, ite_eq_left j.isLt, fieldAssignment]
  | source =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | scratch =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | copyScratch =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | savedIndex j =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | extra value =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)

theorem loaded_field (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.field j slot) =
      encodeWord ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) := by
  rw [MachineSourceTuple.stageTapes_field, ite_eq_left j.isLt, hempty, List.append_nil]

theorem loaded_extra (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (extra : AddressMachineSpace.Extra k s d noiseCount) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.extra extra) = baseArena (.extra extra) :=
  MachineSourceTuple.stageTapes_frame F tuple baseArena k _
    (by simp) (by simp) (by intros; simp)

theorem loaded_header (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (header : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.headerTape k s d noiseCount header) =
        baseArena (AddressMachineSpace.headerTape k s d noiseCount header) :=
  AddressMachineSpace.tupleOutput_headerTape k s d noiseCount F tuple baseArena header

theorem loaded_radix (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (B : Nat)
    (hB : baseArena (AddressMachineSpace.headerTape k s d noiseCount .baseValue) = encodeWord B) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        .radix) = encodeWord B := by
  rw [AddressMachineSpace.addressSlots_radix, loaded_header, hB]

theorem loaded_capacity (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (C : Nat)
    (hC : baseArena (AddressMachineSpace.headerTape k s d noiseCount .capacity) = encodeWord C) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.capacityTape (AddressMachineSpace.addressEdgeSlots k s d noiseCount)) =
        encodeWord C := by
  rw [AddressMachineSpace.addressSlots_capacity, loaded_header, hC]

theorem loaded_privateAddress (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.privateAddress k s d noiseCount tape) =
        baseArena (AddressMachineSpace.privateAddress k s d noiseCount tape) :=
  loaded_extra F tuple baseArena _

/-- Cleanliness of the actual edge machine is preserved by the actual loader.
All of these local work tapes occupy the private disjoint arena block. -/
theorem loaded_clean (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (clean : MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      baseArena) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      (MachineSourceTuple.stageTapes F tuple baseArena k) := by
  constructor
  · constructor
    · exact (loaded_privateAddress F tuple baseArena .reversed).trans clean.address.reversed
    · exact (loaded_privateAddress F tuple baseArena .forward).trans clean.address.forward
    · exact (loaded_privateAddress F tuple baseArena .copyScratch).trans clean.address.copyScratch
    · exact (loaded_privateAddress F tuple baseArena .accA).trans clean.address.accA
    · exact (loaded_privateAddress F tuple baseArena .accB).trans clean.address.accB
    · exact (loaded_privateAddress F tuple baseArena .counter).trans clean.address.counter
    · exact (loaded_privateAddress F tuple baseArena .hornerScratch).trans clean.address.hornerScratch
    · intro j
      exact (loaded_privateAddress F tuple baseArena (.digit j)).trans (clean.address.digit j)
  · exact (loaded_privateAddress F tuple baseArena .output).trans clean.work

theorem loaded_name (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 3) :
    MachineSourceTuple.stageTapes F tuple baseArena k (MachineSourceTuple.nameField j slot) =
      encodeWord (MachineSourceTuple.equationName F.equations[(tuple j).val] slot) := by
  rw [MachineSourceTuple.output_name]
  change _ ++ baseArena (.field j (MachineSourceTuple.nameSlot slot)) = _
  rw [hempty, List.append_nil]

theorem loaded_occurrence (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val) (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.savedIndex j) = encodeWord (tuple j).val :=
  MachineSourceTuple.output_savedIndex_unary F tuple baseArena hsaved j

def canonicalValues (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (j : Fin k) : Fin 4 → Nat :=
  CanonicalBodyTemplate.recordFields
    (MachineSourceTuple.equationName F.equations[(tuple j).val]) (tuple j).val

/-- The three names and the distinct saved occurrence field are exact unary
values; the RHS remains on its separate field tape. -/
theorem loaded_canonicalField (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.canonicalField k s d noiseCount j slot) =
        encodeWord (canonicalValues F tuple j slot) := by
  fin_cases slot
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 0
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 1
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 2
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields] using
      loaded_occurrence F tuple baseArena hsaved j

/-- Literal input function used by the generic field-template machine. -/
theorem loaded_savedFields (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) :
    (fun i => MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (.field i))) = CanonicalBodyMachine.savedFields (canonicalValues F tuple) := by
  funext i
  change MachineSourceTuple.stageTapes F tuple baseArena k
    (AddressMachineSpace.canonicalField k s d noiseCount
      ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2) = _
  exact loaded_canonicalField F tuple baseArena hsaved hempty _ _

end UniqueGamesTheorem.Integration.AddressTupleLoaded

end

section

/-!
# The exact frame after a tuple body and its field cleanup

Loading replaces the initially empty equation-field tapes. Appending writes
only the shared reversed-output header, which is outside those fields. The
actual field drains therefore restore the original arena with precisely the
same appended bytes. Saved occurrence indices and the odometer survive.
-/

namespace UniqueGamesTheorem.Integration.AddressTupleFrame

open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Complexity

variable {k s d noiseCount : Nat}

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

/-- Clearing the physical fields commutes with an append to any other tape. -/
theorem cleared_outputTapes (base : Arena k s d noiseCount → List Bool)
    (output : Arena k s d noiseCount) (bits : List Bool)
    (outside : ∀ j : Fin k, ∀ slot : Fin 4, output ≠ .field j slot) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineFieldTemplate.outputTapes base output bits) =
      MachineFieldTemplate.outputTapes
        (AddressTupleCleanup.cleared k s d noiseCount base) output bits := by
  funext tape
  by_cases h : tape = output
  · subst tape
    rw [AddressTupleCleanup.cleared_outside k s d noiseCount _ output outside,
      MachineFieldTemplate.outputTapes_output, MachineFieldTemplate.outputTapes_output,
      AddressTupleCleanup.cleared_outside k s d noiseCount base output outside]
  · rw [MachineFieldTemplate.outputTapes_other _ output bits tape h]
    change MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount)
        (MachineFieldTemplate.outputTapes base output bits) tape =
      MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount) base tape
    rw [MachineDrainMany.finalTapes_apply, MachineDrainMany.finalTapes_apply,
      MachineFieldTemplate.outputTapes_other base output bits tape h]

/-- The actual edge-output slot is a header tape, not a loaded equation field. -/
theorem cleared_appended (base : Arena k s d noiseCount → List Bool) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          base bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (AddressTupleCleanup.cleared k s d noiseCount base) bits := by
  apply cleared_outputTapes
  intro j slot
  simp [AddressMachineSpace.addressSlots_output, AddressMachineSpace.headerTape]

/-- Cleanup erases exactly the fields assigned by the tuple loader. -/
theorem cleared_fieldAssignment (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hfields : ∀ j slot, base (.field j slot) = []) :
    AddressTupleCleanup.cleared k s d noiseCount
      (AddressTupleLoaded.fieldAssignment F tuple base) = base := by
  funext tape
  cases tape <;> simp [AddressTupleLoaded.fieldAssignment, hfields]

theorem cleared_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) :
    AddressTupleCleanup.cleared k s d noiseCount
      (MachineSourceTuple.stageTapes F tuple base k) = base := by
  rw [AddressTupleLoaded.stageTapes_eq F tuple base hindex hwork]
  exact cleared_fieldAssignment F tuple base hfields

/-- Exact endpoint of load, edge-byte append, and actual loaded-field cleanup. -/
theorem cleared_appended_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          (MachineSourceTuple.stageTapes F tuple base k) bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        base bits := by
  rw [cleared_appended, cleared_loaded F tuple base hindex hwork hfields]

end UniqueGamesTheorem.Integration.AddressTupleFrame

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressTupleBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace


variable {k s d noiseCount : Nat} {Λ : Type}

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount
abbrev Rows (k : Nat) := List (MachineOutcomeRows.Row k (4*k) (1+9*k))
abbrev Slots (k s d noiseCount : Nat) := AddressMachineSpace.addressEdgeSlots k s d noiseCount
abbrev CleanupLabel (k s d noiseCount : Nat) :=
  AddressTupleCleanup.Label k s d noiseCount
abbrev RowLabel (k s d noiseCount : Nat) (rows : Rows k) :=
  MachineOutcomeRows.Label (Slots k s d noiseCount) rows
abbrev Label (k s d noiseCount : Nat) (rows : Rows k) :=
  MachineSourceTuple.Label k ⊕ (Unit ⊕
    (RowLabel k s d noiseCount rows ⊕ (CleanupLabel k s d noiseCount ⊕ Unit)))

instance labelFintype (rows : Rows k) : Fintype (Label k s d noiseCount rows) := by
  unfold Label CleanupLabel RowLabel
  infer_instance

variable {rows : Rows k}

def sourceLabels (labels : Label k s d noiseCount rows → Λ) : MachineSourceTuple.Label k → Λ :=
  fun l => labels (.inl l)
def rhsLabel (labels : Label k s d noiseCount rows → Λ) : Λ := labels (.inr (.inl ()))
def rowLabels (labels : Label k s d noiseCount rows → Λ) : RowLabel k s d noiseCount rows → Λ :=
  fun l => labels (.inr (.inr (.inl l)))
def cleanupLabels (labels : Label k s d noiseCount rows → Λ) : CleanupLabel k s d noiseCount → Λ :=
  fun l => labels (.inr (.inr (.inr (.inl l))))
def resetLabel (labels : Label k s d noiseCount rows → Λ) : Λ :=
  labels (.inr (.inr (.inr (.inr ()))))

def main (rows : Rows k) : Label k s d noiseCount rows := .inl (MachineSourceTuple.labelAt 0)

def reset (exit : Option Λ) : TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k) :=
  .load (fun _ => initialState k) (MachineFieldTemplate.jump exit)

def instruction (rows : Rows k) (labels : Label k s d noiseCount rows → Λ) (exit : Option Λ) :
    Label k s d noiseCount rows →
      TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k)
  | .inl l => MachineSubroutine.statement (sourceLabels labels) (some (rhsLabel labels))
      (MachineSourceTuple.program l)
  | .inr (.inl _) => MachineRhsLoad.statement (rhsField k s d noiseCount)
      (some (rowLabels labels (.inl ())))
  | .inr (.inr (.inl l)) => MachineOutcomeRows.instruction (Slots k s d noiseCount) rows
      (rowLabels labels)
      (AddressTupleCleanup.entry k s d noiseCount (cleanupLabels labels) (some (resetLabel labels))) l
  | .inr (.inr (.inr (.inl l))) => AddressTupleCleanup.instruction k s d noiseCount
      (cleanupLabels labels) (some (resetLabel labels)) l
  | .inr (.inr (.inr (.inr _))) => reset exit

def rhs (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) : Fin k → Bool :=
  fun j => F.equations[(tuple j).val].rhs

def loaded (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  MachineSourceTuple.stageTapes F tuple base k

def tupleBits (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) : List Bool :=
  (MachineOutcomeRows.selected rows (rhs F tuple)).flatMap (MachineOutcomeRows.payload B C values)

noncomputable def emitted (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  MachineAddressEdge.appended (Slots k s d noiseCount) (loaded F tuple base)
    (tupleBits rows B C values F tuple)

noncomputable def finalTapes (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  AddressTupleCleanup.cleared k s d noiseCount (emitted rows B C values F tuple base)

structure Ready (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Prop where
  source : base .source = SourceEncoding.inputBits F
  saved : ∀j, base (.savedIndex j) = encodeWord (tuple j).val
  index : base .index = []
  work : base .work = []
  scratch : base .scratch = []
  copy : base .copyScratch = []
  fields : ∀j slot, base (.field j slot) = []

noncomputable def budget (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Nat :=
  (k * (10 * (SourceEncoding.inputBits F).length + 20) + 1) + 1 +
    ((MachineOutcomeRows.rowCosts (Slots k s d noiseCount) B C values
      (MachineOutcomeRows.selected rows (rhs F tuple)) (loaded F tuple base)).sum + 1) +
    AddressTupleCleanup.budget k s d noiseCount (emitted rows B C values F tuple base) + 1

noncomputable def run (rows : Rows k) (labels : Label k s d noiseCount rows → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction rows labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (oldRhs : Fin k → Bool) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (valid : MachineOutcomeRows.Invariant (Slots k s d noiseCount) B C values
      (MachineOutcomeRows.selected rows (rhs F tuple)) (loaded F tuple base)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main rows)), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, finalTapes rows B C values F tuple base⟩)
      (budget rows B C values F tuple base) := by
  have sourceRun := MachineSourceTuple.placedLoadUnaryInTime
    (sourceLabels labels) (some (rhsLabel labels)) P (fun l => atLabels (.inl l))
    F tuple base ready.source ready.saved ready.index ready.work ready.scratch ready.copy (oldRhs, ())
  have rhsRun := MachineRhsLoad.loadInTime (rhsField k s d noiseCount)
    (rhsLabel labels) (some (rowLabels labels (.inl ()))) P (atLabels (.inr (.inl ())))
    (((oldRhs, ()), ()), none) (loaded F tuple base) (rhs F tuple) (fun _ => [])
    (by
      intro j
      change loaded F tuple base (MachineSourceTuple.rhsField j) = _
      rw [loaded, MachineSourceTuple.output_rhs]
      change encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++
        base (.field j 3) = _
      rw [ready.fields j 3]
      rfl)
  have rowsRun := MachineOutcomeRows.phaseInTime (Slots k s d noiseCount) rows
    (rowLabels labels)
    (AddressTupleCleanup.entry k s d noiseCount (cleanupLabels labels) (some (resetLabel labels)))
    P (fun l => atLabels (.inr (.inr (.inl l))))
    (loaded F tuple base) (rhs F tuple) () none B C values valid
  have cleanupRun := AddressTupleCleanup.execution k s d noiseCount
    (cleanupLabels labels) (some (resetLabel labels)) P
    (fun l => atLabels (.inr (.inr (.inr (.inl l)))))
    (emitted rows B C values F tuple base) (((rhs F tuple), ()), ()) none
  simp only [MachineDrainMany.finalRegister_none] at cleanupRun
  have resetRun : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (resetLabel labels), ((((rhs F tuple), ()), ()), none),
        finalTapes rows B C values F tuple base⟩
      (some ⟨exit, initialState k, finalTapes rows B C values F tuple base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step P ⟨some (resetLabel labels), _, _⟩ = _
    change some (TM2.stepAux (P (resetLabel labels)) _ _) = _
    rw [show P (resetLabel labels) = reset exit from atLabels (.inr (.inr (.inr (.inr ()))))]
    cases exit <;> rfl
  have first := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ sourceRun rhsRun
  have second := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ first rowsRun
  have third := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ second cleanupRun
  have last := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ third resetRun
  refine { steps := last.steps, evals_in_steps := last.evals_in_steps, steps_le_m := ?_ }
  exact last.steps_le_m.trans (by dsimp only [budget]; omega)

def source (F : SourceEncoding.Input) : ActualSource.Source :=
  ActualSource.Source.ofList F.equations F.nonempty

theorem rhs_eq_actual (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) :
    rhs F tuple = AddressOutcomeSpecs.rhsBits (source F) tuple := rfl

theorem canonicalValues_eq_actual (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) :
    AddressTupleLoaded.canonicalValues F tuple =
      CanonicalBodyTemplate.sourceFields tuple (ActualGame.names (source F)) := by
  funext j
  apply congrArg (fun names => CanonicalBodyTemplate.recordFields names (tuple j).val)
  funext slot
  fin_cases slot <;> rfl

theorem tupleBits_actual (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (T : NoiseTables.Table s d) :
    tupleBits (AddressOutcomeSpecs.rows k T)
      (CanonicalAddress.base F.variables F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple =
      AddressOutcomeSpecs.tupleBits (source F) k T tuple := by
  unfold tupleBits
  rw [rhs_eq_actual, canonicalValues_eq_actual]
  exact AddressOutcomeSpecs.tuplePayload_actual (source F) k T tuple

/-- All generic template-correctness obligations are discharged from the
actual loader's canonical field values and the checked fixed-row specs. -/
theorem actualInvariant (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (T : NoiseTables.Table s d) (base : Arena k s d noiseCount → List Bool)
    (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) (B C : Nat)
    (hB : base (headerTape k s d noiseCount .baseValue) = encodeWord B)
    (hC : base (headerTape k s d noiseCount .capacity) = encodeWord C) :
    MachineOutcomeRows.Invariant (Slots k s d noiseCount) B C
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
      (loaded F tuple base) := by
  constructor
  · exact AddressTupleLoaded.loaded_clean F tuple base clean
  · exact AddressTupleLoaded.loaded_radix F tuple base B hB
  · exact AddressTupleLoaded.loaded_capacity F tuple base C hC
  · intro spec member
    have fields := AddressTupleLoaded.loaded_savedFields F tuple base ready.saved ready.fields
    change (fun i => loaded F tuple base (MachineAddressEdge.addressSlots
      (Slots k s d noiseCount) (.field i))) = _ at fields
    rw [fields]
    exact AddressOutcomeSpecs.correct_rows T (AddressTupleLoaded.canonicalValues F tuple)
      (rhs F tuple) spec member

/-- Actual fixed-row execution. Physical readiness and stored header values
are its only data hypotheses; no template or body-execution premise remains. -/
noncomputable def run_fixed_rows (T : NoiseTables.Table s d)
    (labels : Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool) (B C : Nat)
    (hB : base (headerTape k s d noiseCount .baseValue) = encodeWord B)
    (hC : base (headerTape k s d noiseCount .capacity) = encodeWord C) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k,
        finalTapes (AddressOutcomeSpecs.rows k T) B C
          (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base⟩)
      (budget (AddressOutcomeSpecs.rows k T) B C
        (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base) :=
  run (AddressOutcomeSpecs.rows k T) labels exit P atLabels F tuple base ready oldRhs B C
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
    (actualInvariant F tuple T base ready clean B C hB hC)

theorem finalTapes_eq (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base) :
    finalTapes rows B C values F tuple base = MachineAddressEdge.appended
      (Slots k s d noiseCount) base (tupleBits rows B C values F tuple) :=
  AddressTupleFrame.cleared_appended_loaded F tuple base ready.index ready.work ready.fields _

noncomputable def run_actual (T : NoiseTables.Table s d)
    (labels : Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.variables F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      (budget (AddressOutcomeSpecs.rows k T)
        (CanonicalAddress.base F.variables F.equations.length s d)
        (AddressGame.bodyCapacity (source F) k s d)
        (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base) := by
  have actual := run_fixed_rows T labels exit P atLabels F tuple base ready clean oldRhs
    (CanonicalAddress.base F.variables F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d) hB hC
  rw [finalTapes_eq _ _ _ _ F tuple base ready, tupleBits_actual] at actual
  exact actual

end UniqueGamesTheorem.Integration.AddressTupleBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressTupleBudget
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Integration.AddressTupleBudget

open Reduction Foundations.Complexity
open AddressTupleBody


variable {k s d noiseCount : Nat}

theorem source_counts_le (F : SourceEncoding.Input) :
    F.variables+F.equations.length ≤ (SourceEncoding.inputBits F).length := by
  rw [SourceEncoding.inputBits_length]
  omega

theorem radix_le (F : SourceEncoding.Input) (s d : Nat) :
    CanonicalAddress.base F.variables F.equations.length s d ≤
      radixBound s d (SourceEncoding.inputBits F).length := by
  have h := source_counts_le F
  simp only [CanonicalAddress.base_eq, radixBound]
  omega

theorem radix_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    CanonicalAddress.base F.variables F.equations.length s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := radix_le F s d
  unfold magnitude
  omega

theorem capacity_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    AddressGame.bodyCapacity (source F) k s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := Nat.pow_le_pow_left (radix_le F s d) (1+9*k)
  change (CanonicalAddress.base F.variables F.equations.length s d)^(1+9*k) ≤ _
  unfold magnitude
  omega

theorem canonicalValues_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    AddressTupleLoaded.canonicalValues F tuple j slot ≤
      (SourceEncoding.inputBits F).length := by
  rw [canonicalValues_eq_actual]
  unfold CanonicalBodyTemplate.sourceFields CanonicalBodyTemplate.recordFields
  split_ifs with h
  · have hname := (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).isLt
    have hvars := SourceEncoding.inputBits_length_ge_variables F
    change _ < F.variables at hname
    change (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).val ≤
      (SourceEncoding.inputBits F).length
    exact (Nat.le_of_lt hname).trans hvars
  · have hocc := (tuple j).isLt
    have hcount := SourceEncoding.inputBits_length_ge_equations F
    omega

theorem loaded_fields_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (i : Fin (4*k)) :
    ((loaded F tuple base) (MachineAddressEdge.addressSlots
      (Slots k s d noiseCount) (.field i))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have fields := AddressTupleLoaded.loaded_savedFields F tuple base ready.saved ready.fields
  have atField := congrFun fields i
  change loaded F tuple base (MachineAddressEdge.addressSlots
    (Slots k s d noiseCount) (.field i)) = _ at atField
  rw [atField]
  simp only [CanonicalBodyMachine.savedFields, encodeWord_length]
  exact (Nat.add_le_add_right (canonicalValues_le F tuple _ _) 1).trans
    (field_length_le_magnitude k s d _)

/-- These are the actual canonical words, not arbitrary interpreted templates. -/
theorem queryWords_lt_radix (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (w : Nat) (hw : w ∈ AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) :
    w < CanonicalAddress.base F.variables F.equations.length s d := by
  rw [canonicalValues_eq_actual, rhs_eq_actual] at hw
  erw [AddressOutcomeSpecs.bitVector_rhsBits] at hw
  erw [AddressByteSemantics.queryWords_actual (source F) (tuple,X)] at hw
  exact CanonicalAddress.bodyWords_lt_base _ w hw

theorem queryWords_encoded_length_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d) :
    (encodeWords (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hwords := encodeWords_length_le
    (AddressByteSemantics.queryWords (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))
    (radixBound s d (SourceEncoding.inputBits F).length)
    (fun w hw => (Nat.le_of_lt (queryWords_lt_radix F tuple X w hw)).trans (radix_le F s d))
  rw [AddressByteSemantics.queryWords_length] at hwords
  unfold magnitude
  omega

theorem queryWords_digits_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (i : Nat) (hi : i < 1+9*k) :
    MachineTemplateAddress.digits (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) i ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hi' : i < (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))).length := by
    simpa only [AddressByteSemantics.queryWords_length] using hi
  simp only [MachineTemplateAddress.digits, List.getElem?_eq_getElem hi', Option.getD_some]
  exact (Nat.le_of_lt (queryWords_lt_radix F tuple X _ (List.getElem_mem hi'))).trans
    (radix_le_magnitude F k s d)

theorem selected_values_bound (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d) :
    ∀ row ∈ MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple),
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) := by
  rw [AddressOutcomeSpecs.selected_rows]
  intro row member
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
  simp only [AddressOutcomeSpecs.values_row_left, AddressOutcomeSpecs.values_row_right]
  exact ⟨queryWords_encoded_length_le_magnitude F tuple p.1,
    queryWords_encoded_length_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p),
    queryWords_digits_le_magnitude F tuple p.1,
    queryWords_digits_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p)⟩

/-- Both canonical templates have exactly the same fixed token count. -/
noncomputable def rowPolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  Polynomial.C (2^((2*k+1)*(s+d+1))*T.vectors.length) *
    MachineAddressEdge.timePolynomial (1+9*k) (1+9*k) (1+9*k) + 1

theorem selected_polynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (b : Fin k → Bool) (M : Nat) :
    (MachineOutcomeRows.timePolynomial
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) b)).eval M =
        (rowPolynomial k T).eval M := by
  simp only [MachineOutcomeRows.timePolynomial, AddressOutcomeSpecs.selected_rows,
    List.map_map, Function.comp_def, AddressOutcomeSpecs.row_left_length,
    AddressOutcomeSpecs.row_right_length, Polynomial.eval_add, Polynomial.eval_one,
    eval_sum_constant, FixedOutcomes.tableParams_length, rowPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem rows_budget_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    (MachineOutcomeRows.rowCosts (Slots k s d noiseCount)
      (CanonicalAddress.base F.variables F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
      (loaded F tuple base)).sum+1 ≤
        (rowPolynomial k T).eval (magnitude k s d (SourceEncoding.inputBits F).length) := by
  have h := MachineOutcomeRows.phaseCost_le_timePolynomial (Slots k s d noiseCount)
    (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
    (loaded F tuple base) _ _
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
    (magnitude k s d (SourceEncoding.inputBits F).length)
    (AddressTupleLoaded.loaded_clean F tuple base clean)
    (loaded_fields_le_magnitude F tuple base ready)
    (radix_le_magnitude F k s d) (capacity_le_magnitude F k s d)
    (selected_values_bound F tuple T)
  simpa only [selected_polynomial_eval] using h

theorem physicalField_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) ≤
      (SourceEncoding.inputBits F).length := by
  have hv := SourceEncoding.inputBits_length_ge_variables F
  have hl := SourceEncoding.inputBits_length F
  have h₁ := F.equations[(tuple j).val].first.isLt
  have h₂ := F.equations[(tuple j).val].second.isLt
  have h₃ := F.equations[(tuple j).val].third.isLt
  fin_cases slot <;>
    simp only [SourceEncoding.equationWords, List.getElem_cons_zero,
      List.getElem_cons_succ] <;> (try split_ifs) <;> omega

/-- Cleanup sees only the four loaded fields per position; output is not scanned. -/
theorem cleanup_budget_le (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base) :
    AddressTupleCleanup.budget k s d noiseCount (emitted rows B C values F tuple base) ≤
      4*k*((SourceEncoding.inputBits F).length+2) := by
  have h := lengthSum_le_of_mem (AddressTupleCleanup.loadedFields k s d noiseCount)
    (emitted rows B C values F tuple base) ((SourceEncoding.inputBits F).length+1) (by
      intro tape member
      obtain ⟨j, slot, rfl⟩ :=
        (AddressTupleCleanup.mem_loadedFields k s d noiseCount tape).mp member
      rw [emitted, MachineAddressEdge.appended_other]
      · rw [loaded, AddressTupleLoaded.loaded_field F tuple base ready.fields, encodeWord_length]
        exact Nat.add_le_add_right (physicalField_le F tuple j slot) 1
      · rw [AddressMachineSpace.addressSlots_output]
        simp [AddressMachineSpace.headerTape])
  rw [AddressTupleCleanup.loadedFields_length] at h
  change MachineDrainMany.lengthSum _ _ + 4*k ≤ _
  calc
    _ ≤ 4*k*((SourceEncoding.inputBits F).length+1)+4*k := Nat.add_le_add_right h _
    _ = 4*k*((SourceEncoding.inputBits F).length+2) := by ring

/-- Fixed program dimensions determine this explicit polynomial in input bits. -/
noncomputable def timePolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  (Polynomial.C k*(Polynomial.C 10*Polynomial.X+Polynomial.C 20)+1)+1+
    (rowPolynomial k T).comp (magnitudePolynomial k s d)+
    Polynomial.C (4*k)*(Polynomial.X+Polynomial.C 2)+1

theorem timePolynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) (L : Nat) :
    (timePolynomial k T).eval L =
      (k*(10*L+20)+1)+1+(rowPolynomial k T).eval (magnitude k s d L)+4*k*(L+2)+1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, magnitudePolynomial_eval]

/-- Uniform bound for the actual tuple body, with all canonical values instantiated. -/
theorem budget_le_timePolynomial (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    AddressTupleBody.budget (AddressOutcomeSpecs.rows k T)
      (CanonicalAddress.base F.variables F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ≤
        (timePolynomial k T).eval (SourceEncoding.inputBits F).length := by
  have rowsBound := rows_budget_le F tuple T base ready clean
  have cleanupBound := cleanup_budget_le (AddressOutcomeSpecs.rows k T)
    (CanonicalAddress.base F.variables F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d)
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ready
  rw [AddressTupleBody.budget, timePolynomial_eval]
  omega

end UniqueGamesTheorem.Integration.AddressTupleBudget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressTuplePolynomialLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Integration.AddressTuplePolynomial

open Turing Reduction Foundations.Complexity
open AddressTupleBody AddressMachineSpace


variable {k s d noiseCount : Nat} {Λ : Type}

noncomputable def run_actual (T : NoiseTables.Table s d)
    (labels : AddressTupleBody.Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : AddressTupleBody.Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀ l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : AddressTupleBody.Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.variables F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have actual := AddressTupleBody.run_actual T labels exit P atLabels F tuple base
    ready clean oldRhs hB hC
  exact {
    steps := actual.steps
    evals_in_steps := actual.evals_in_steps
    steps_le_m := actual.steps_le_m.trans
      (AddressTupleBudget.budget_le_timePolynomial F tuple T base ready clean)
  }

end UniqueGamesTheorem.Integration.AddressTuplePolynomial



namespace UniqueGamesTheorem.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration
open MachineComposition


noncomputable section

abbrev Tape (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :=
  AddressMachineSpace.Tape k s d T.vectors.length

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

def accumulator : Tape k T := AddressMachineSpace.headerTape k s d T.vectors.length .reversed
def output : Tape k T := AddressMachineSpace.finalOutput k s d T.vectors.length

theorem accumulator_ne_output : accumulator k T ≠ output k T :=
  AddressMachineSpace.headerTape_ne_finalOutput k s d T.vectors.length .reversed

/-- The finalizer visits every other tape in a fixed finite order. -/
def clearKeys : List (Tape k T) := by
  classical
  exact ((Finset.univ : Finset (Tape k T)).filter
    (fun tape : Tape k T => tape ≠ accumulator k T ∧ tape ≠ output k T)).toList

@[simp] theorem mem_clearKeys (tape : Tape k T) :
    tape ∈ clearKeys k T ↔ tape ≠ accumulator k T ∧ tape ≠ output k T := by
  classical
  simp [clearKeys]

@[simp] theorem accumulator_not_mem_clearKeys : accumulator k T ∉ clearKeys k T := by simp
@[simp] theorem output_not_mem_clearKeys : output k T ∉ clearKeys k T := by simp

theorem clearKeys_covers (tape : Tape k T) (ha : tape ≠ accumulator k T)
    (ho : tape ≠ output k T) : tape ∈ clearKeys k T := (mem_clearKeys k T tape).2 ⟨ha,ho⟩

abbrev HeaderLabel := MachineAddressHeaders.Label k s d T.vectors.length
abbrev BodyLabel := Integration.AddressTupleBody.Label k s d T.vectors.length
  (AddressOutcomeSpecs.rows k T)
abbrev FinishLabel := SourceRuntimeFinish.Label (clearKeys k T)

inductive Label (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
  | header (localLabel : HeaderLabel k T)
  | initialize_ (localLabel : MachineOdometerInit.Label k)
  | body (localLabel : BodyLabel k T)
  | check (digit : Fin k)
  | reset (digit : Fin k)
  | finishStart
  | finish (localLabel : FinishLabel k T)
  deriving DecidableEq, Fintype

def headerLabels : HeaderLabel k T → Label k T := Label.header
def initializeLabels : MachineOdometerInit.Label k → Label k T := Label.initialize_
def bodyLabels : BodyLabel k T → Label k T := Label.body
def finishLabels : FinishLabel k T → Label k T := Label.finish

def start : Label k T := .header (.inl .copyOut)
def initializeStart : Label k T := MachineOdometerInit.labelAt (initializeLabels k T) 0
def bodyStart : Label k T := .body (Integration.AddressTupleBody.main (AddressOutcomeSpecs.rows k T))
def checkLabel (j : Fin k) : Label k T := .check j
def resetLabel (j : Fin k) : Label k T := .reset j
def finishStart : Label k T := .finishStart

def next (r : Nat) : Label k T :=
  if h : r < k then checkLabel k T ⟨r,h⟩ else finishStart k T

def resetAt (r : Nat) : Label k T :=
  if h : r < k then resetLabel k T ⟨r,h⟩ else finishStart k T

@[simp] theorem next_lt (r : Nat) (h : r < k) :
    next k T r = checkLabel k T ⟨r,h⟩ := by simp [next,h]
@[simp] theorem next_ge (r : Nat) (h : k ≤ r) : next k T r = finishStart k T := by
  simp [next, Nat.not_lt.mpr h]
@[simp] theorem resetAt_lt (r : Nat) (h : r < k) :
    resetAt k T r = resetLabel k T ⟨r,h⟩ := by simp [resetAt,h]

/-- Header, digit initialization, physical tuple body, carry loops, and complete
finalization are placed in a single actual finite transition program. -/
def program : Label k T → TM2.Stmt (fun _ : Tape k T => Bool) (Label k T) (State k)
  | .header l => MachineAddressHeaders.statement
      (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (headerLabels k T) (some (initializeStart k T)) l
  | .initialize_ l => MachineOdometerInit.statement
      (AddressMachineSpace.odometerSlots k s d T.vectors.length)
      (initializeLabels k T) (some (bodyStart k T)) l
  | .body l => Integration.AddressTupleBody.instruction (AddressOutcomeSpecs.rows k T)
      (bodyLabels k T) (some (next k T 0)) l
  | .check j => MachineTupleOdometer.increment
      (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (bodyStart k T) (resetLabel k T j)
  | .reset j => MachineTupleOdometer.reset
      (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (resetLabel k T j) (next k T (j.val+1))
  | .finishStart => MachineFieldTemplate.jump
      (SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T))
  | .finish l => SourceRuntimeFinish.statement (clearKeys k T) (accumulator k T) (output k T)
      (AddressMachineSpace.initialState k).1 (finishLabels k T) none l

@[simp] theorem atHeader (l : HeaderLabel k T) : program k T (headerLabels k T l) =
    MachineAddressHeaders.statement (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (headerLabels k T) (some (initializeStart k T)) l := rfl

@[simp] theorem atInitialize (l : MachineOdometerInit.Label k) :
    program k T (initializeLabels k T l) =
      MachineOdometerInit.statement (AddressMachineSpace.odometerSlots k s d T.vectors.length)
        (initializeLabels k T) (some (bodyStart k T)) l := rfl

@[simp] theorem atBody (l : BodyLabel k T) : program k T (bodyLabels k T l) =
    Integration.AddressTupleBody.instruction (AddressOutcomeSpecs.rows k T)
      (bodyLabels k T) (some (next k T 0)) l := rfl

@[simp] theorem atCheck (j : Fin k) : program k T (checkLabel k T j) =
    MachineTupleOdometer.increment (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (bodyStart k T) (resetLabel k T j) := rfl

@[simp] theorem atReset (j : Fin k) : program k T (resetLabel k T j) =
    MachineTupleOdometer.reset (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (resetLabel k T j) (next k T (j.val+1)) := rfl

@[simp] theorem atFinish (l : FinishLabel k T) : program k T (finishLabels k T l) =
    SourceRuntimeFinish.statement (clearKeys k T) (accumulator k T) (output k T)
      (AddressMachineSpace.initialState k).1 (finishLabels k T) none l := rfl

/-- This bridge has no data-dependent action and costs exactly one transition. -/
theorem finishStartStep (state : State k) (base : Tape k T → List Bool) :
    TM2.step (program k T) ⟨some (finishStart k T),state,base⟩ =
      some ⟨SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T),state,base⟩ := by
  change some (TM2.stepAux (MachineFieldTemplate.jump
    (SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T))) state base) = _
  cases SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T) <;> rfl

def finishStartInTime (state : State k) (base : Tape k T → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program k T))
      ⟨some (finishStart k T),state,base⟩
      (some ⟨SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T),state,base⟩) 1 where
  steps := 1
  evals_in_steps := finishStartStep k T state base
  steps_le_m := Nat.le_refl _

/-- All alphabets and registers are finite. Counts live solely on Bool stacks. -/
def machine : FinTM2 where
  K := Tape k T
  k₀ := .source
  k₁ := output k T
  Γ := fun _ => Bool
  Λ := Label k T
  main := start k T
  σ := State k
  initialState := AddressMachineSpace.initialState k
  m := program k T

@[simp] theorem machine_main : (machine k T).main = start k T := rfl
@[simp] theorem machine_program : (machine k T).m = program k T := rfl
@[simp] theorem machine_initialState : (machine k T).initialState = AddressMachineSpace.initialState k := rfl
@[simp] theorem machine_input : (machine k T).k₀ = (MachineSourceTuple.Tape.source : Tape k T) := rfl
@[simp] theorem machine_output : (machine k T).k₁ = output k T := rfl

def inputTapes (bits : List Bool) : Tape k T → List Bool :=
  Function.update (fun _ => []) .source bits

def outputTapes (bits : List Bool) : Tape k T → List Bool :=
  SourceRuntimeFinish.canonicalTapes (output k T) bits

@[simp] theorem inputTapes_source (bits : List Bool) : inputTapes k T bits .source = bits := by
  simp [inputTapes]

@[simp] theorem inputTapes_other (bits : List Bool) (tape : Tape k T) (h : tape ≠ .source) :
    inputTapes k T bits tape = [] := by simp [inputTapes,h]

@[simp] theorem outputTapes_output (bits : List Bool) : outputTapes k T bits (output k T) = bits := by
  simp [outputTapes, SourceRuntimeFinish.canonicalTapes]

@[simp] theorem outputTapes_other (bits : List Bool) (tape : Tape k T) (h : tape ≠ output k T) :
    outputTapes k T bits tape = [] := by simp [outputTapes,SourceRuntimeFinish.canonicalTapes,h]

theorem initList_eq (bits : List Bool) : initList (machine k T) bits =
    ⟨some (start k T),AddressMachineSpace.initialState k,inputTapes k T bits⟩ := by
  change (⟨some (start k T),AddressMachineSpace.initialState k,
    (initList (machine k T) bits).stk⟩ : (machine k T).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨some (start k T),AddressMachineSpace.initialState k,tapes⟩ : (machine k T).Cfg))
  funext tape
  by_cases h : tape = .source
  · subst tape; simp [initList,machine,inputTapes]; rfl
  · simp [initList,machine,inputTapes]
    erw [dite_eq_right h, Function.update_of_ne h]

theorem haltList_eq (bits : List Bool) : haltList (machine k T) bits =
    ⟨none,AddressMachineSpace.initialState k,outputTapes k T bits⟩ := by
  change (⟨none,AddressMachineSpace.initialState k,
    (haltList (machine k T) bits).stk⟩ : (machine k T).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨none,AddressMachineSpace.initialState k,tapes⟩ : (machine k T).Cfg))
  funext tape
  by_cases h : tape = output k T
  · subst tape; simp [haltList,machine,outputTapes,SourceRuntimeFinish.canonicalTapes]; rfl
  · simp [haltList,machine,outputTapes,SourceRuntimeFinish.canonicalTapes]
    erw [dite_eq_right h, Function.update_of_ne h]

end
end UniqueGamesTheorem.Reduction.AddressMachineProgram



/-!
The actual address machine's final bridge, cleanup, reversal, and halt. The
polynomial cleanup bound follows from space used by the supplied actual prefix
execution. The complete reduction supplies that prefix in `MachineAddressGame`.
-/

namespace UniqueGamesTheorem.Reduction.AddressMachineFinish

open Turing Foundations.Complexity Foundations.Hastad


noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def timePolynomial (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (AddressMachineProgram.machine k T)
    (AddressMachineProgram.clearKeys k T).length (prefixTime + 1)

/-- Finish the concrete program, including its one-step finalizer entry bridge.
The runtime bound uses all actual intermediate tapes, with no output-size or
private-space assumption. -/
def completePrefix (input : List Bool) (prefixTime : Polynomial Nat)
    (base : AddressMachineProgram.Tape k T → List Bool)
    (execution : StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) input)
      (some ⟨some (AddressMachineProgram.finishStart k T),
        AddressMachineSpace.initialState k, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base (AddressMachineProgram.output k T) = []) :
    TM2OutputsInTime (AddressMachineProgram.machine k T) input
      (some (base (AddressMachineProgram.accumulator k T)).reverse)
      ((timePolynomial k T prefixTime).eval input.length) := by
  let bridge := AddressMachineProgram.finishStartInTime k T
    (AddressMachineSpace.initialState k) base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) input)
      (some ⟨SourceRuntimeFinish.entry (AddressMachineProgram.clearKeys k T)
          (AddressMachineProgram.finishLabels k T), AddressMachineSpace.initialState k, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using
        joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime
    (AddressMachineProgram.clearKeys k T)
    (AddressMachineProgram.accumulator k T) (AddressMachineProgram.output k T)
    (AddressMachineProgram.accumulator_ne_output k T)
    (AddressMachineProgram.accumulator_not_mem_clearKeys k T)
    (AddressMachineProgram.output_not_mem_clearKeys k T)
    (AddressMachineProgram.clearKeys_covers k T)
    (AddressMachineSpace.initialState k).1 (AddressMachineProgram.finishLabels k T) none
    (AddressMachineProgram.program k T) (AddressMachineProgram.atFinish k T)
    base outputEmpty (AddressMachineSpace.initialState k).1 none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (AddressMachineProgram.machine k T)
    input (prefixTime + 1) prefixRun
    (AddressMachineProgram.clearKeys k T)
    (AddressMachineProgram.accumulator k T) (AddressMachineProgram.output k T)
    (AddressMachineProgram.accumulator_not_mem_clearKeys k T)
    (AddressMachineProgram.output_not_mem_clearKeys k T)
    (AddressMachineProgram.clearKeys_covers k T) base outputEmpty (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
    (initList (AddressMachineProgram.machine k T) input)
    (some (haltList (AddressMachineProgram.machine k T)
      (base (AddressMachineProgram.accumulator k T)).reverse)) _
  rw [AddressMachineProgram.haltList_eq]
  exact run

end
end UniqueGamesTheorem.Reduction.AddressMachineFinish

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressMachineInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Reduction.AddressMachineInitial

open Turing UniqueGamesTheorem.Foundations.Complexity


noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def afterHeaders (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineAddressHeaders.resultTapes (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
    (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F))
    F.variables F.equations.length

def initialized (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineOdometerInit.stageTapes (AddressMachineSpace.odometerSlots k s d T.vectors.length)
    F.equations.length (afterHeaders k T F) k

theorem input_header (F : SourceEncoding.Input)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
      (AddressMachineSpace.headerTape k s d T.vectors.length c) = [] := by
  apply AddressMachineProgram.inputTapes_other
  simp [AddressMachineSpace.headerTape]

theorem input_headerClean (F : SourceEncoding.Input) :
    MachineAddressHeaders.Clean (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)) := by
  refine {
    accA := input_header k T F .accA
    accB := input_header k T F .accB
    counter := input_header k T F .counter
    scratch := input_header k T F .scratch
    coefficients := ?_
    baseValue := input_header k T F .baseValue
    capacity := input_header k T F .capacity
    temporary := input_header k T F .temporary
    readCopy := ?_
    variableCount := input_header k T F .variableCount
    occurrenceCount := input_header k T F .occurrenceCount }
  · intro i
    change AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
      (.extra (.inl (.inr i))) = []
    exact AddressMachineProgram.inputTapes_other k T _ _ (by simp)
  · exact AddressMachineProgram.inputTapes_other k T _ .work (by simp)

theorem afterHeaders_frame (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hw : p ≠ .work)
    (hn : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .variableCount)
    (hm : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount)
    (hb : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .baseValue)
    (hc : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .capacity)
    (hr : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    afterHeaders k T F p = AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F) p :=
  MachineAddressHeaders.resultTapes_other _ _ _ _ p hw hn hm hb hc hr

theorem afterHeaders_empty (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hs : p ≠ .source) (hw : p ≠ .work)
    (hn : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .variableCount)
    (hm : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount)
    (hb : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .baseValue)
    (hc : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .capacity)
    (hr : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    afterHeaders k T F p = [] :=
  (afterHeaders_frame k T F p hw hn hm hb hc hr).trans
    (AddressMachineProgram.inputTapes_other k T _ p hs)

@[simp] theorem afterHeaders_source (F : SourceEncoding.Input) :
    afterHeaders k T F .source = SourceEncoding.inputBits F := by
  exact (MachineAddressHeaders.resultTapes_source _ _ F.variables F.equations.length).trans
    (AddressMachineProgram.inputTapes_source k T _)

@[simp] theorem afterHeaders_variables (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) =
      encodeWord F.variables := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .variableCount) = _
  rw [MachineAddressHeaders.resultTapes_n]
  change encodeWord F.variables ++ AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
    (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) = _
  rw [input_header, List.append_nil]

@[simp] theorem afterHeaders_occurrences (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) =
      encodeWord F.equations.length := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .occurrenceCount) = _
  rw [MachineAddressHeaders.resultTapes_m]
  change encodeWord F.equations.length ++ AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
    (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) = _
  rw [input_header, List.append_nil]

@[simp] theorem afterHeaders_base (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.variables F.equations.length) :=
  MachineAddressHeaders.resultTapes_base _ _ _ _

@[simp] theorem afterHeaders_capacity (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.variables F.equations.length) :=
  MachineAddressHeaders.resultTapes_capacity _ _ _ _

@[simp] theorem afterHeaders_reversed (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.variables F.equations.length).reverse := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .reversed) = _
  rw [MachineAddressHeaders.resultTapes_reversed]
  change (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
    F.variables F.equations.length).reverse ++ AddressMachineProgram.inputTapes k T
      (SourceEncoding.inputBits F) (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) = _
  rw [input_header, List.append_nil]

@[simp] theorem afterHeaders_work (F : SourceEncoding.Input) : afterHeaders k T F .work = [] :=
  MachineAddressHeaders.resultTapes_readCopy _ _ _ _

@[simp] theorem afterHeaders_current (F : SourceEncoding.Input) (j : Fin k) :
    afterHeaders k T F (AddressMachineSpace.current k s d T.vectors.length j) = [] := by
  apply afterHeaders_empty <;> simp [AddressMachineSpace.current, AddressMachineSpace.headerTape]

@[simp] theorem afterHeaders_remaining (F : SourceEncoding.Input) (j : Fin k) :
    afterHeaders k T F (AddressMachineSpace.remaining k s d T.vectors.length j) = [] := by
  apply afterHeaders_empty <;> simp [AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

@[simp] theorem afterHeaders_copyScratch (F : SourceEncoding.Input) :
    afterHeaders k T F .copyScratch = [] := by
  apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]

theorem initialized_frame (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hc : ∀ j, p ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀ j, p ≠ AddressMachineSpace.remaining k s d T.vectors.length j) :
    initialized k T F p = afterHeaders k T F p :=
  MachineOdometerInit.stageTapes_frame _ _ _ _ p hc hr

@[simp] theorem initialized_header (F : SourceEncoding.Input)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) =
      afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) :=
  initialized_frame k T F _
    (AddressMachineSpace.headerTape_ne_current k s d T.vectors.length c)
    (AddressMachineSpace.headerTape_ne_remaining k s d T.vectors.length c)

@[simp] theorem initialized_source (F : SourceEncoding.Input) :
    initialized k T F .source = SourceEncoding.inputBits F := by
  rw [initialized_frame k T F .source
    (by intro j; simp [AddressMachineSpace.current])
    (by intro j; simp [AddressMachineSpace.remaining])]
  exact afterHeaders_source k T F

@[simp] theorem initialized_variables (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) =
      encodeWord F.variables := by rw [initialized_header, afterHeaders_variables]
@[simp] theorem initialized_occurrences (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) =
      encodeWord F.equations.length := by rw [initialized_header, afterHeaders_occurrences]
@[simp] theorem initialized_base (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.variables F.equations.length) := by
  rw [initialized_header, afterHeaders_base]
@[simp] theorem initialized_capacity (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.variables F.equations.length) := by
  rw [initialized_header, afterHeaders_capacity]
@[simp] theorem initialized_reversed (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.variables F.equations.length).reverse := by
  rw [initialized_header, afterHeaders_reversed]

@[simp] theorem initialized_current (F : SourceEncoding.Input) (j : Fin k) :
    initialized k T F (AddressMachineSpace.current k s d T.vectors.length j) = encodeWord 0 :=
  MachineOdometerInit.output_current _ (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    F.equations.length (afterHeaders k T F) j

@[simp] theorem initialized_remaining (F : SourceEncoding.Input) (j : Fin k) :
    initialized k T F (AddressMachineSpace.remaining k s d T.vectors.length j) =
      encodeWord (F.equations.length - 1) :=
  MachineOdometerInit.output_remaining _ (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    F.equations.length (afterHeaders k T F) j

@[simp] theorem initialized_savedIndex (F : SourceEncoding.Input) (j : Fin k) :
    initialized k T F (.savedIndex j) = encodeWord 0 := by
  simpa only [AddressMachineSpace.current_rev] using initialized_current k T F j.rev

theorem initialized_empty (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hbefore : afterHeaders k T F p = [])
    (hc : ∀ j, p ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀ j, p ≠ AddressMachineSpace.remaining k s d T.vectors.length j) :
    initialized k T F p = [] := (initialized_frame k T F p hc hr).trans hbefore

@[simp] theorem initialized_work (F : SourceEncoding.Input) : initialized k T F .work = [] := by
  apply initialized_empty k T F _ (afterHeaders_work k T F) <;>
    intro j <;> simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_index (F : SourceEncoding.Input) : initialized k T F .index = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]
  all_goals
    intro j
    simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_scratch (F : SourceEncoding.Input) : initialized k T F .scratch = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]
  all_goals
    intro j
    simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_copyScratch (F : SourceEncoding.Input) :
    initialized k T F .copyScratch = [] := by
  apply initialized_empty k T F _ (afterHeaders_copyScratch k T F) <;>
    intro j <;> simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_field (F : SourceEncoding.Input) (j : Fin k) (slot : Fin 4) :
    initialized k T F (.field j slot) = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]
  all_goals
    intro i
    simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_finalOutput (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.finalOutput k s d T.vectors.length) = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;>
      simp [AddressMachineSpace.finalOutput, AddressMachineSpace.headerTape]
  all_goals
    intro i
    simp [AddressMachineSpace.finalOutput, AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_privateAddress (F : SourceEncoding.Input)
    (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    initialized k T F (AddressMachineSpace.privateAddress k s d T.vectors.length tape) = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;>
      simp [AddressMachineSpace.privateAddress, AddressMachineSpace.headerTape]
  all_goals
    intro i
    simp [AddressMachineSpace.privateAddress, AddressMachineSpace.current, AddressMachineSpace.remaining]

/-- Actual two-phase initialization from the concrete machine input. -/
def inTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits F))
      (some ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k,
        initialized k T F⟩)
      ((MachineAddressHeaders.timePolynomial k s d T.vectors.length).eval
        (SourceEncoding.inputBits F).length + k * (2 * (SourceEncoding.inputBits F).length + 6) + 1) := by
  have header := MachineAddressHeaders.inPolynomialTime
    (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
    (AddressMachineProgram.headerLabels k T) (some (AddressMachineProgram.initializeStart k T))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atHeader k T)
    (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)) F
    (AddressMachineProgram.inputTapes_source k T _) (input_headerClean k T F)
    (AddressMachineSpace.initialState k).1.1 none
  have digits := MachineOdometerInit.initializeInTime
    (AddressMachineSpace.odometerSlots k s d T.vectors.length)
    (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    (AddressMachineProgram.initializeLabels k T) (some (AddressMachineProgram.bodyStart k T))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atInitialize k T)
    F.equations.length (List.length_pos_iff.mpr F.nonempty) (afterHeaders k T F)
    (afterHeaders_occurrences k T F) (afterHeaders_current k T F)
    (afterHeaders_remaining k T F) (afterHeaders_copyScratch k T F)
    (AddressMachineSpace.initialState k).1
  have run := StateTransition.EvalsToInTime.trans (AddressMachineProgram.machine k T).step
    _ _ _ _ _ header digits
  refine { steps := run.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · rw [AddressMachineProgram.initList_eq]
    exact run.evals_in_steps
  · apply Nat.le_trans run.steps_le_m
    have hm := SourceEncoding.inputBits_length_ge_equations F
    have hmul := Nat.mul_le_mul_left k (show 2 * F.equations.length + 6 ≤
      2 * (SourceEncoding.inputBits F).length + 6 by omega)
    omega

def timePolynomial : Polynomial Nat :=
  MachineAddressHeaders.timePolynomial k s d T.vectors.length +
    Polynomial.C k * (Polynomial.C 2 * Polynomial.X + Polynomial.C 6) + Polynomial.C 1

theorem timePolynomial_eval (N : Nat) :
    (timePolynomial k T).eval N =
      (MachineAddressHeaders.timePolynomial k s d T.vectors.length).eval N +
        k * (2 * N + 6) + 1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

def inPolynomialTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits F))
      (some ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k,
        initialized k T F⟩)
      ((timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  rw [timePolynomial_eval]
  exact inTime k T F

end
end UniqueGamesTheorem.Reduction.AddressMachineInitial

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressOutputSize
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.AddressOutputSize

open ActualSource
open UniqueGamesTheorem.Integration
open UniqueGamesTheorem.Foundations

variable {s d : Nat}

theorem table_constraints_eq (S : Source) (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput S k T).constraints.length =
      Explicit.edgeCount S.occurrences k (s + d) T.vectors.length := by
  unfold AddressGame.tableOutput
  erw [AddressGame.outputInstance_length]
  simp only [TableReduction.tableEnumeration]
  erw [List.length_finRange]

end UniqueGamesTheorem.Reduction.AddressOutputSize

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressMachineLoopLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Reduction.AddressMachineLoop

open Turing Foundations.Complexity Integration


noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

def bits (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) : List Bool :=
  AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T
    (OccurrenceTupleOrder.readCoordinates digits)

def stateTapes (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    AddressMachineProgram.Tape k T → List Bool :=
  AddressOdometerSchedule.setDigits F.equations.length (fun j => (digits j).val)
    (AddressOdometerSchedule.setAcc (AddressMachineInitial.initialized k T F) output)

theorem stateTapes_frame (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (tape : AddressMachineProgram.Tape k T)
    (hc : ∀j, tape ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀j, tape ≠ AddressMachineSpace.remaining k s d T.vectors.length j)
    (ha : tape ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    stateTapes k T F digits output tape = AddressMachineInitial.initialized k T F tape := by
  rw [stateTapes, AddressOdometerSchedule.setDigits_other _ _ _ tape hc hr]
  exact AddressOdometerSchedule.setAcc_other _ _ tape ha

@[simp] theorem stateTapes_savedIndex (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) (j : Fin k) :
    stateTapes k T F digits output (.savedIndex j) = encodeWord (digits j.rev).val := by
  exact AddressOdometerSchedule.setDigits_savedIndex _ _ _ j

@[simp] theorem stateTapes_private (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (tape : MachineTemplateAddress.Tape (4*k) (1+9*k)) :
    stateTapes k T F digits output (AddressMachineSpace.privateAddress k s d T.vectors.length tape) = [] := by
  rw [stateTapes_frame]
  · exact AddressMachineInitial.initialized_privateAddress k T F tape
  all_goals simp [AddressMachineSpace.privateAddress, AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

@[simp] theorem stateTapes_header (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (c : MachineAddressHeaders.Arithmetic.Control) (hc : c ≠ .reversed) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length c) =
      AddressMachineInitial.initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) := by
  apply stateTapes_frame
  · exact AddressMachineSpace.headerTape_ne_current k s d T.vectors.length c
  · exact AddressMachineSpace.headerTape_ne_remaining k s d T.vectors.length c
  · intro h
    exact hc ((AddressMachineSpace.headerTape_eq_iff k s d T.vectors.length c .reversed).mp h)

theorem stateTapes_ready (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    AddressTupleBody.Ready F (OccurrenceTupleOrder.readCoordinates digits)
      (stateTapes k T F digits output) := by
  constructor
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_source k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j
    exact stateTapes_savedIndex k T F digits output j
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_index k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_work k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_scratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_copyScratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j slot
    rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_field k T F j slot
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

theorem stateTapes_clean (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) := by
  constructor
  · constructor
    · exact stateTapes_private k T F digits output .reversed
    · exact stateTapes_private k T F digits output .forward
    · exact stateTapes_private k T F digits output .copyScratch
    · exact stateTapes_private k T F digits output .accA
    · exact stateTapes_private k T F digits output .accB
    · exact stateTapes_private k T F digits output .counter
    · exact stateTapes_private k T F digits output .hornerScratch
    · intro j; exact stateTapes_private k T F digits output (.digit j)
  · exact stateTapes_private k T F digits output .output

theorem stateTapes_base (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (CanonicalAddress.base F.variables F.equations.length s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_base]
  congr 1
  simp [MachineAddressHeaders.radix, MachineAddressHeaders.baseConstant,
    CanonicalAddress.base_eq, Nat.add_assoc]

theorem stateTapes_capacity (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (AddressGame.bodyCapacity (AddressTupleBody.source F) k s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_capacity]
  congr 1
  change MachineAddressHeaders.capacity k s d F.variables F.equations.length =
    CanonicalAddress.capacity F.variables F.equations.length k s d
  simp [MachineAddressHeaders.capacity, MachineAddressHeaders.radix,
    MachineAddressHeaders.baseConstant, CanonicalAddress.capacity,
    CanonicalAddress.base_eq, Nat.add_assoc]

/-- Appending actual tuple bytes is exactly the schedule's accumulator update. -/
theorem appended_stateTapes (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output payload : List Bool) :
    MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) payload =
      stateTapes k T F digits (payload.reverse ++ output) := by
  change AddressOdometerSchedule.setAcc (stateTapes k T F digits output)
    (payload.reverse ++ stateTapes k T F digits output
      (AddressOdometerSchedule.accumulator k s d T.vectors.length)) = _
  simp only [stateTapes, AddressOdometerSchedule.setDigits_accumulator, AddressOdometerSchedule.setAcc_apply]
  rw [AddressOdometerSchedule.setDigits_setAcc, AddressOdometerSchedule.setAcc_setAcc,
    ← AddressOdometerSchedule.setDigits_setAcc]

/-- The local-body premise of the odometer theorem is derived from the actual
placed tuple-body implementation and its actual uniform budget theorem. -/
theorem bodyTrace (F : SourceEncoding.Input) :
    AddressOdometerSchedule.BodyTrace (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F)
      (bits k T F) ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  intro digits output
  let base := stateTapes k T F digits output
  have ready := stateTapes_ready k T F digits output
  have clean := stateTapes_clean k T F digits output
  have actual := AddressTuplePolynomial.run_actual T (AddressMachineProgram.bodyLabels k T) (some (AddressMachineProgram.next k T 0))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atBody k T) F
    (OccurrenceTupleOrder.readCoordinates digits) base ready clean (fun _ => false)
    (stateTapes_base k T F digits output) (stateTapes_capacity k T F digits output)
  refine ⟨actual.steps, actual.steps_le_m, ?_⟩
  have hemit : MachineAddressEdge.appended (AddressTupleBody.Slots k s d T.vectors.length)
      base (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T
        (OccurrenceTupleOrder.readCoordinates digits)) =
      stateTapes k T F digits ((bits k T F digits).reverse ++ output) :=
    appended_stateTapes k T F digits output _
  exact actual.evals_in_steps.trans (congrArg
    (fun tapes => some (AddressOdometerSchedule.configuration
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 tapes)) hemit)

/-- The all-zero assignment is already physically present after initialization. -/
theorem setDigits_initialized_zero (F : SourceEncoding.Input) :
    AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
      (AddressMachineInitial.initialized k T F) = AddressMachineInitial.initialized k T F := by
  funext tape
  cases tape with
  | savedIndex j =>
    rw [AddressOdometerSchedule.setDigits_savedIndex, AddressMachineInitial.initialized_savedIndex]
  | extra e =>
    rcases e with e | e
    · rfl
    · rcases e with e | e
      · rfl
      · rcases e with j | e
        · change AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
            (AddressMachineInitial.initialized k T F) (AddressOdometerSchedule.remaining k s d T.vectors.length j) = _
          simp only [AddressOdometerSchedule.setDigits_remaining, Fin.isLt, dite_eq_left, Nat.sub_zero]
          exact (AddressMachineInitial.initialized_remaining k T F j).symm
        · rfl
  | _ => rfl

def finalTapes (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  (AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
    (AddressMachineInitial.initialized k T F) (bits k T F)).stk

/-- Actual complete tuple traversal, before the final output reversal. -/
def traversal (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      (((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length + 2*k) *
        F.equations.length^k) := by
  have actual := AddressOdometerSchedule.traversalInTime (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
    (AddressMachineProgram.next k T) (AddressMachineProgram.resetAt k T) (AddressMachineSpace.initialState k).1
    (List.length_pos_iff.mpr F.nonempty)
    ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length)
    (AddressMachineInitial.initialized k T F) (bits k T F)
    (by
      intro i hi
      simp only [AddressMachineProgram.next_lt k T i hi, AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atCheck k T ⟨i,hi⟩)
    (by
      intro i hi
      simp only [AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atReset k T ⟨i,hi⟩)
    (bodyTrace k T F)
  have run := Classical.choice actual
  have hstart : AddressOdometerSchedule.initialConfiguration (m := F.equations.length) k
      (AddressMachineProgram.bodyStart k T) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F) =
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩ := by
    simp only [AddressOdometerSchedule.initialConfiguration, AddressOdometerSchedule.configuration,
      setDigits_initialized_zero, AddressMachineSpace.initialState]
  have hfinish : AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
      (AddressMachineInitial.initialized k T F) (bits k T F) =
      ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩ := by
    simp only [AddressOdometerSchedule.finalConfiguration, AddressOdometerSchedule.configuration, finalTapes,
      AddressMachineProgram.next_ge k T k (Nat.le_refl _), AddressMachineSpace.initialState]
  rw [hstart, hfinish] at run
  exact run

/-- Exact output order, including repeated constraints and the original header. -/
theorem allBits_eq (F : SourceEncoding.Input) :
    AddressOdometerSchedule.allBits (bits k T F) =
      (FixedOutcomes.occurrenceTuples F.equations.length k).flatMap
        (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T) := by
  exact (OccurrenceTupleOrder.functions_flatMap F.equations.length k _).symm

@[simp] theorem final_reversed (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      ((FixedOutcomes.occurrenceTuples F.equations.length k).flatMap
        (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T)).reverse ++
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.variables F.equations.length).reverse := by
  change (AddressOdometerSchedule.finalConfiguration _ _ _ _).stk (AddressOdometerSchedule.accumulator _ _ _ _) = _
  rw [AddressOdometerSchedule.final_accumulator]
  change (AddressOdometerSchedule.allBits (bits k T F)).reverse ++ _ = _
  rw [allBits_eq]
  congr 1
  exact AddressMachineInitial.initialized_reversed k T F

/-- The actual header machine emits exactly the target instance's three headers. -/
theorem headerBits_eq (F : SourceEncoding.Input) :
    MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
      F.variables F.equations.length =
      encodeWords [(AddressGame.tableOutput (AddressTupleBody.source F) k T).vertices, 2^s,
        (AddressGame.tableOutput (AddressTupleBody.source F) k T).constraints.length] := by
  have hcap : MachineAddressHeaders.capacity k s d F.variables F.equations.length =
      AddressGame.bodyCapacity (AddressTupleBody.source F) k s d := by
    change MachineAddressHeaders.capacity k s d F.variables F.equations.length =
      CanonicalAddress.capacity F.variables F.equations.length k s d
    simp [MachineAddressHeaders.capacity, MachineAddressHeaders.radix,
      MachineAddressHeaders.baseConstant, CanonicalAddress.capacity,
      CanonicalAddress.base_eq, Nat.add_assoc]
  have hedge : MachineAddressHeaders.edgeCount k s d T.vectors.length F.equations.length =
      (AddressGame.tableOutput (AddressTupleBody.source F) k T).constraints.length := by
    rw [AddressOutputSize.table_constraints_eq]
    change MachineAddressHeaders.edgeCount k s d T.vectors.length F.equations.length =
      Explicit.edgeCount F.equations.length k (s+d) T.vectors.length
    unfold MachineAddressHeaders.edgeCount MachineAddressHeaders.edgeFactor Explicit.edgeCount
    ring
  rw [MachineAddressHeaders.Arithmetic.headerBits, hcap, hedge]
  rfl

/-- The final reversed tape is exactly the complete encoded actual instance. -/
theorem final_accumulator (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineProgram.accumulator k T) =
      (gameBits (AddressGame.tableOutput (AddressTupleBody.source F) k T)).reverse := by
  rw [AddressOutcomeSpecs.gameBits_factor, ← headerBits_eq k T F, List.reverse_append]
  exact final_reversed k T F

theorem final_other (F : SourceEncoding.Input) (tape : AddressMachineProgram.Tape k T)
    (hc : ∀j, tape ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀j, tape ≠ AddressMachineSpace.remaining k s d T.vectors.length j)
    (ha : tape ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    finalTapes k T F tape = AddressMachineInitial.initialized k T F tape :=
  AddressOdometerSchedule.final_other _ _ _ _ tape hc hr ha

@[simp] theorem final_outputEmpty (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineProgram.output k T) = [] := by
  rw [final_other]
  · exact AddressMachineInitial.initialized_finalOutput k T F
  · intro j
    exact Ne.symm (AddressMachineSpace.current_ne_finalOutput k s d T.vectors.length j)
  · intro j
    exact Ne.symm (AddressMachineSpace.remaining_ne_finalOutput k s d T.vectors.length j)
  · exact Ne.symm (AddressMachineSpace.headerTape_ne_finalOutput k s d T.vectors.length .reversed)

@[simp] theorem final_current (F : SourceEncoding.Input) (j : Fin k) :
    finalTapes k T F (AddressMachineSpace.current k s d T.vectors.length j) = encodeWord 0 :=
  AddressOdometerSchedule.final_current _ _ _ _ j

@[simp] theorem final_remaining (F : SourceEncoding.Input) (j : Fin k) :
    finalTapes k T F (AddressMachineSpace.remaining k s d T.vectors.length j) =
      encodeWord (F.equations.length-1) :=
  AddressOdometerSchedule.final_remaining _ _ _ _ j

/-- The exponent and coefficients depend only on fixed reduction parameters. -/
def timePolynomial : Polynomial Nat :=
  (AddressTupleBudget.timePolynomial k T + Polynomial.C (2*k)) * Polynomial.X^k

@[simp] theorem timePolynomial_eval (N : Nat) :
    (timePolynomial k T).eval N = ((AddressTupleBudget.timePolynomial k T).eval N + 2*k)*N^k := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

def inPolynomialTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      ((timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have run := traversal k T F
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  rw [timePolynomial_eval]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (SourceEncoding.inputBits_length_ge_equations F) k)

end
end UniqueGamesTheorem.Reduction.AddressMachineLoop



/-!
# The complete addressed outer-reduction machine

The fixed finite machine reads an encoded nonempty E3LIN occurrence list and
writes the exact encoded addressed Unique Games instance. Its execution covers
all headers, all occurrence tuples, every fixed noise/coefficient outcome,
every permutation image, reversal, and complete tape cleanup.
-/

namespace UniqueGamesTheorem.Reduction.MachineAddressGame

open Turing Foundations.Complexity


noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def output (input : SourceEncoding.Input) : Foundations.Target.Instance (2 ^ s) :=
  AddressGame.tableOutput
    (ActualSource.Source.ofList input.equations input.nonempty) k T

def prefixPolynomial : Polynomial Nat :=
  AddressMachineInitial.timePolynomial k T + AddressMachineLoop.timePolynomial k T

def timePolynomial : Polynomial Nat :=
  AddressMachineFinish.timePolynomial k T (prefixPolynomial k T)

/-- The complete actual prefix, with both initialization and every tuple body
supplied by their constructed finite programs. -/
def prefixInTime (input : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input))
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k,
        AddressMachineLoop.finalTapes k T input⟩)
      ((prefixPolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let initial := AddressMachineInitial.inPolynomialTime k T input
  let loop := AddressMachineLoop.inPolynomialTime k T input
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initial loop
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm] using run.steps_le_m

/-- Literal `initList` to literal `haltList`, including all private tape and
finite-state cleanup. This theorem has no runtime premise. -/
def fullRunInTime (input : SourceEncoding.Input) :
    TM2OutputsInTime (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input)
      (some (gameBits (output k T input)))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let run := AddressMachineFinish.completePrefix k T (SourceEncoding.inputBits input)
    (prefixPolynomial k T) (AddressMachineLoop.finalTapes k T input)
    (prefixInTime k T input) (AddressMachineLoop.final_outputEmpty k T input)
  simpa only [AddressMachineLoop.final_accumulator, List.reverse_reverse, output,
    Integration.AddressTupleBody.source, timePolynomial] using run

def computableInPolyTime :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) where
  tm := AddressMachineProgram.machine k T
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial k T
  outputsFun input := by
    change TM2OutputsInTime (AddressMachineProgram.machine k T)
      ((SourceEncoding.inputBits input).map id)
      (some ((gameBits (output k T input)).map id))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length)
    have input_eq : @List.map
        ((AddressMachineProgram.machine k T).Γ (AddressMachineProgram.machine k T).k₀)
        ((AddressMachineProgram.machine k T).Γ (AddressMachineProgram.machine k T).k₀)
        id (SourceEncoding.inputBits input) = SourceEncoding.inputBits input := List.map_id _
    have output_eq : @List.map
        ((AddressMachineProgram.machine k T).Γ (AddressMachineProgram.machine k T).k₁)
        ((AddressMachineProgram.machine k T).Γ (AddressMachineProgram.machine k T).k₁)
        id (gameBits (output k T input)) = gameBits (output k T input) := List.map_id _
    erw [input_eq, output_eq]
    exact fullRunInTime k T input

end
end UniqueGamesTheorem.Reduction.MachineAddressGame

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSingleOrbitBridgeLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The old addressed producer is reused only as a code generator. Its exact output
is the doubled codec of the new single-orbit game. The proved physical
postprocessor then yields the new game, with no premise about the value of the
legacy game and no legacy gadget or inverse theorem used.
-/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

open Turing UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Complexity
open ActualSource MachineSingleOrbitCodec

namespace SingleAddress

abbrev addressEdge := Decoder.TableKeysAddressGame.addressEdge
abbrev outputInstance := Decoder.TableKeysAddressGame.outputInstance
abbrev tableOutput := Decoder.TableKeysAddressGame.tableOutput

end SingleAddress

theorem old_addressEdge_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    AddressGame.addressEdge S k g ω = doubleConstraint (SingleAddress.addressEdge S k g ω) := by
  unfold AddressGame.addressEdge doubleConstraint SingleAddress.addressEdge
    Decoder.TableKeysAddressGame.addressEdge
  congr 1
  apply Fin.ext
  exact Encoding.sideEquiv_true_val _

/-- Exact equality of the ordered, fully serialized constraint data. -/
theorem old_outputInstance_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    AddressGame.outputInstance S k g en = doubleInstance (SingleAddress.outputInstance S k g en) := by
  unfold AddressGame.outputInstance doubleInstance SingleAddress.outputInstance
    Decoder.TableKeysAddressGame.outputInstance
  congr 1
  simp only [List.map_map, Function.comp_def, ← old_addressEdge_eq_double]
  rfl

theorem old_tableOutput_eq_double (S : Source) (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d) :
    AddressGame.tableOutput S k T = doubleInstance (SingleAddress.tableOutput S k T) :=
  old_outputInstance_eq_double S k _ _

def output (k : Nat) {s d : Nat} (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d)
    (input : SourceEncoding.Input) : UniqueGamesTheorem.Foundations.Target.Instance (2 ^ s) :=
  SingleAddress.tableOutput (Source.ofList input.equations input.nonempty) k T

theorem old_output_eq_double (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d) (input : SourceEncoding.Input) :
    MachineAddressGame.output k T input = doubleInstance (output k T input) :=
  old_tableOutput_eq_double _ k T

noncomputable section

/-- Reinterpret the existing producer using the proved exact codec equality. -/
def doubledComputableInPolyTime (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits
      (fun I => gameBits (doubleInstance I)) (output k T) := by
  let old := MachineAddressGame.computableInPolyTime k T
  refine {
    tm := old.tm
    inputAlphabet := old.inputAlphabet
    outputAlphabet := old.outputAlphabet
    time := old.time
    outputsFun := ?_ }
  intro input
  rw [← old_output_eq_double k T input]
  exact old.outputsFun input

def computableInPolyTime (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) :=
  MachineSequential.composeBits (f := output k T) (g := id) (doubledComputableInPolyTime k T)
    (MachineSingleOrbitRuntime.computableInPolyTime (2 ^ s))

end

end UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

end

section

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

theorem workAlphabetFinite (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d)
    (tape : (computableInPolyTime k T).tm.K) :
    Finite ((computableInPolyTime k T).tm.Γ tape) := by
  rcases tape with first | second
  · change Finite Bool
    infer_instance
  · rcases second with localTape | bridgeTape
    · change Finite Bool
      infer_instance
    · change Finite Bool
      infer_instance

end UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubdivisionDynamicRowsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Four-edge subdivision row emission with a physical permutation-table field.

The program depends only on the fixed identity table. Five saved endpoint words
and the entire final forward permutation table are physical tape contents. In
particular an input-dependent permutation is not inserted into a program label
or literal instruction. The last row is oriented `v → r`; for binary-vector
translations its table equals the inverse table of the original `u → v` edge.
-/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionDynamicRows

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionRows (identityTable inverseTable)

/-- The last table is the actual table for the left-to-right `v → r` row. -/
def rows {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List (Constraint n q) :=
  [⟨vertices 0, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 3, identityTable q⟩,
   ⟨vertices 4, vertices 3, p⟩]

def rowBits {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List Bool := encodeWords ((rows vertices p).flatMap constraintWords)

end UniqueGamesTheorem.Explicit.MachineSubdivisionDynamicRows

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionProgram

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction

def headerTokens (q : Nat) : List (MachineFieldTemplate.Token 2) :=
  [.copy 0, .literal (encodeWord q), .copy 1]

inductive Label (q : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | initialize_ (i : Fin 9) (phase : Fin 3)
  | emitHeader (label : MachineFieldTemplate.Label (headerTokens q).length)
  | guard
  | startU | readU | startV | readV
  | readTable (completed : Fin (q + 1))
  | reverseTable
  | emitRows (label : MachineFieldTemplate.Label (rowTokens q).length)
  | drainU | drainV | drainPermutation
  | increment
  | finishStart
  | finish (label : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def headerNext {q : Nat} (i : Fin 3) : Label q :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .initialize_ 0 0

def initNext {q : Nat} (i : Fin 9) : Label q :=
  if h : i.val + 1 < 9 then .initialize_ ⟨i.val + 1, h⟩ 0
  else .emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)

def rowEntry (q : Nat) : Label q :=
  .emitRows (MachineFieldTemplate.startAt (rowTokens q).length 0)

/-- A fixed finite program: the table reader counts only `q` delimiters in
finite control, while all unbounded integers are physical unary tape contents. -/
def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .initialize_ i 0 =>
      match (initOp i).seed with
      | some offset => MachineUnaryAffineAt.seed (initOp i).destination offset (.initialize_ i 1)
      | none => .goto (fun _ => .initialize_ i 1)
  | .initialize_ i 1 => MachineUnaryAffineAt.scan (initOp i).source .affineScratch
      (initOp i).destination (initOp i).coefficient (.initialize_ i 1) (.initialize_ i 2)
  | .initialize_ i 2 => MachineTransfer.loopAt .affineScratch (initOp i).source
      id false (.initialize_ i 2) (some (initNext i))
  | .emitHeader label => MachineFieldTemplate.instruction (headerTokens q)
      newHeaderField .copyScratch .accumulator Label.emitHeader (some .guard) label
  | .guard => MachineUnaryCounter.guard .remaining .startU .finishStart
  | .startU => SourceMachine.fieldStart .u .readU
  | .readU => SourceMachine.fieldLoop .input .u .readU (some .startV)
  | .startV => SourceMachine.fieldStart .v .readV
  | .readV => SourceMachine.fieldLoop .input .v .readV (some (.readTable 0))
  | .readTable completed =>
      if h : completed.val < q then
        .pop .input (fun state head => (state.1, head))
          (.push .permutationReverse (fun state => state.2.getD false)
            (.branch (fun state => state.2.getD false)
              (.goto fun _ => .readTable completed)
              (.load (fun state => (state.1, none))
                (.goto fun _ => .readTable ⟨completed.val + 1, by omega⟩))))
      else .load (fun state => (state.1, none)) (.goto fun _ => .reverseTable)
  | .reverseTable => MachineTransfer.loopAt .permutationReverse .permutation
      id false .reverseTable (some (rowEntry q))
  | .emitRows label => MachineFieldTemplate.instruction (rowTokens q)
      rowField .copyScratch .accumulator Label.emitRows (some .drainU) label
  | .drainU => MachineDrain.drain .u .drainU (some .drainV)
  | .drainV => MachineDrain.drain .v .drainV (some .drainPermutation)
  | .drainPermutation => MachineDrain.drain .permutation .drainPermutation (some .increment)
  | .increment => .push .middle (fun _ => true)
      (.push .first (fun _ => true) (.push .first (fun _ => true)
        (.push .last (fun _ => true) (.push .last (fun _ => true)
          (.load (fun _ => initialState) (.goto fun _ => .guard))))))
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program q

end UniqueGamesTheorem.Explicit.MachineSubdivisionProgram

/-! Actual cleanup, output reversal, and polynomial finishing overhead. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionFinish

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineSubdivisionProgram

noncomputable def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

theorem haltList_eq (q : Nat) (bits : List Bool) :
    haltList (machine q) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  (cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes, Function.update]); rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .finishStart) initialState base) = _
    simp only [program, TM2.stepAux]
    rfl
  steps_le_m := Nat.le_refl _

noncomputable def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (q := q)) none (program q) (fun _ => rfl)
    base outputEmpty ((), ()) none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q)
    input (prefixTime + 1) prefixRun clearKeys Tape.accumulator Tape.output
    accumulator_not_mem_clearKeys output_not_mem_clearKeys covers base outputEmpty
    (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end UniqueGamesTheorem.Explicit.MachineSubdivisionFinish

/-! Exact execution of the three input-header reads of subdivision. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionHeaders

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineSubdivisionProgram

def afterVertices (n : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n else []

def afterAlphabet (n q : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n
    else if k = .alphabetHeader then encodeWord q else []

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabetHeader then encodeWord q
    else if k = .occurrences then encodeWord Q else []

theorem initList_eq (q : Nat) (bits : List Bool) :
    initList (machine q) bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1

theorem first_result (n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .vertices
      (inputTapes (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes (encodeWord n ++ rest) .vertices) =
      afterVertices n rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices]

theorem second_result (n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .alphabetHeader
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabetHeader) =
      afterAlphabet n q rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet]

theorem third_result (n q Q : Nat) (body : List Bool) :
    SourceMachine.fieldTapes Tape.input .occurrences
      (afterAlphabet n q (encodeWord Q ++ body)) body
      (encodeWord Q ++ afterAlphabet n q (encodeWord Q ++ body) .occurrences) =
      resultTapes n q Q body := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterAlphabet, resultTapes]

/-- The input headers are consumed literally; all unread constraint bits retain
their original order and no tape contains an implicit runtime number. -/
def headersInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.initialize_ 0 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label q) (.headerRead 0) (some (.headerStart 1))
    (program q) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabetHeader (by decide)
    (.headerStart 1 : Label q) (.headerRead 1) (some (.headerStart 2))
    (program q) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label q) (.headerRead 2) (some (.initialize_ 0 0))
    (program q) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  simpa only [encodeWords, List.nil_append, List.append_assoc, machine, FinTM2.step, FinTM2.Cfg, initialState]
    using! ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program q))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.initialize_ 0 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

end UniqueGamesTheorem.Explicit.MachineSubdivisionHeaders

/-! Physical header arithmetic and private-vertex initialization. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionInit

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

def priorWord (seed : Option Nat) (b : Nat) : List Bool :=
  match seed with
  | none => encodeWord b
  | some _ => []

theorem operationTrace (q : Nat) (i : Fin 9) (base : Tape → List Bool) (a b : Nat)
    (sourceWord : base (initOp i).source = encodeWord a)
    (scratchEmpty : base .affineScratch = [])
    (destinationWord : base (initOp i).destination = priorWord (initOp i).seed b) :
    (MachineComposition.advance (machine q).step)^[2 * (a + 1) + 1]
      (some ⟨some (.initialize_ i 0), initialState, base⟩) =
      some ⟨some (initNext i), initialState,
        Function.update base (initOp i).destination
          (encodeWord ((initOp i).coefficient * a + (initOp i).seed.getD b))⟩ := by
  cases seedValue : (initOp i).seed with
  | some offset =>
    have run := MachineUnaryAffineAt.seededAffineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient offset
      (.initialize_ i 0 : Label q) (.initialize_ i 1) (.initialize_ i 2)
      (some (initNext i)) (program q)
      (by simp [program, seedValue]) rfl rfl base a []
      (by simpa using sourceWord) scratchEmpty ((), ()) none
    have hd : base (initOp i).destination = [] := by
      simpa [priorWord, seedValue] using destinationWord
    simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState, hd, List.append_nil, seedValue,
      Option.getD_some] using! run
  | none =>
    have hd : base (initOp i).destination = encodeWord b := by
      simpa [priorWord, seedValue] using destinationWord
    have frame (word : List Bool) :
        MachineUnaryAffineAt.tapes (initOp i).source Tape.affineScratch
          (initOp i).destination base (encodeWord a ++ []) [] word =
        Function.update base (initOp i).destination word := by
      simp only [List.append_nil]
      rw [← sourceWord, ← scratchEmpty]
      simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes,
        Function.update_eq_self]
    have run := MachineUnaryAffineAt.affineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient (.initialize_ i 1 : Label q) (.initialize_ i 2)
      (some (initNext i)) (program q) rfl rfl base a b [] [] ((), ()) none
    rw [frame, frame] at run
    simp only [List.append_nil, ← hd, Function.update_eq_self] at run
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine q).step)^[2 * (a + 1)]
      (some (TM2.stepAux (program q (.initialize_ i 0)) initialState base)) = _
    simp only [program, seedValue, TM2.stepAux]
    simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState, seedValue, Option.getD_none] using! run

def frame (n q Q : Nat) (body : List Bool) : Nat → Tape → List Bool
  | 0 => MachineSubdivisionHeaders.resultTapes n q Q body
  | r + 1 => if h : r < 9 then
      Function.update (frame n q Q body r) (initOp ⟨r, h⟩).destination
        (encodeWord (afterValue n Q ⟨r, h⟩))
    else frame n q Q body r

theorem frame_source (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).source = encodeWord (sourceValue n Q i) := by
  fin_cases i <;>
    simp [frame, sourceValue, initOp, MachineSubdivisionHeaders.resultTapes]

theorem frame_scratch (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val .affineScratch = [] := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes]

theorem frame_destination (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).destination =
      priorWord (initOp i).seed (beforeValue n i) := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes,
    afterValue, sourceValue, beforeValue, priorWord]

def atStage (q r : Nat) : Label q :=
  if h : r < 9 then .initialize_ ⟨r, h⟩ 0
  else .emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)

theorem initNext_eq_atStage (q : Nat) (i : Fin 9) :
    (initNext i : Label q) = atStage q (i.val + 1) := by
  simp [initNext, atStage]

def prefixInTime (q n Q : Nat) (body : List Bool) (r : Nat) (hr : r ≤ 9) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize_ 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (atStage q r), initialState, frame n q Q body r⟩)
      (r * stageCost n Q) := by
  induction r with
  | zero =>
    refine { steps := 0, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp [atStage, frame]
    · simp
  | succ r ih =>
    have hlt : r < 9 := by omega
    let i : Fin 9 := ⟨r, hlt⟩
    have before := ih (by omega)
    have opTrace := operationTrace q i (frame n q Q body r)
      (sourceValue n Q i) (beforeValue n i)
      (frame_source n q Q body i) (frame_scratch n q Q body i)
      (frame_destination n q Q body i)
    have op : StateTransition.EvalsToInTime (machine q).step
        ⟨some (atStage q r), initialState, frame n q Q body r⟩
        (some ⟨some (atStage q (r + 1)), initialState, frame n q Q body (r + 1)⟩)
        (stageCost n Q) := {
      steps := 2 * (sourceValue n Q i + 1) + 1
      evals_in_steps := by
        change (MachineComposition.advance (TM2.step (program q)))^[_] _ = _
        simpa only [FinTM2.step, FinTM2.Cfg, machine, atStage, hlt,
          ↓reduceDIte, i, initNext_eq_atStage, frame, afterValue] using! opTrace
      steps_le_m := by
        have bound := sourceValue_le n Q i
        dsimp [stageCost]
        omega }
    have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ before op
    exact {
      toEvalsTo := joined.toEvalsTo
      steps_le_m := by
        calc
          joined.steps ≤ stageCost n Q + r * stageCost n Q := joined.steps_le_m
          _ = (r + 1) * stageCost n Q := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
    }

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => body
  | .vertices => encodeWord n
  | .alphabetHeader => encodeWord q
  | .occurrences => encodeWord Q
  | .remaining => encodeWord Q
  | .newVertices => encodeWord (n + 3 * Q)
  | .newEdges => encodeWord (4 * Q)
  | .middle => encodeWord n
  | .first => encodeWord (n + Q)
  | .last => encodeWord (n + Q + 1)
  | _ => []

theorem final_frame (n q Q : Nat) (body : List Bool) :
    frame n q Q body 9 = resultTapes n q Q body := by
  funext tape
  cases tape <;>
    simp [frame, resultTapes, initOp, MachineSubdivisionHeaders.resultTapes,
      afterValue, sourceValue, beforeValue, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]

/-- The actual initialized loop counters and fresh numeric vertex IDs are
proved outputs of unary arithmetic, including the runtime vertex header. -/
def initializeInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize_ 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, resultTapes n q Q body⟩)
      (9 * stageCost n Q) := by
  simpa only [atStage, show ¬ (9 < 9) by omega, ↓reduceDIte, final_frame]
    using prefixInTime q n Q body 9 (by omega)

end UniqueGamesTheorem.Explicit.MachineSubdivisionInit

/-! Literal output-header emission and the initial occurrence-loop frame. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionEmission

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineSubdivisionInit.resultTapes n q Q body)
    .accumulator (headerBits n q Q).reverse

theorem header_template (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      headerBits n q Q := by
  simp [MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput,
    headerTokens, newHeaderField, MachineSubdivisionInit.resultTapes,
    headerBits, encodeWords]

theorem header_copiedLength (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      n + 7 * Q + 2 := by
  simp [MachineFieldTemplate.copiedLength, headerTokens, newHeaderField,
    MachineSubdivisionInit.resultTapes]
  omega

theorem header_result (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.outputTapes (MachineSubdivisionInit.resultTapes n q Q body)
      .accumulator (headerBits n q Q) = resultTapes n q Q body := by
  simp only [MachineFieldTemplate.outputTapes, MachineSubdivisionInit.resultTapes,
    List.append_nil, resultTapes]

def headerInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, MachineSubdivisionInit.resultTapes n q Q body⟩
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (3 * (n + 7 * Q + 2) + 10) := by
  have run := MachineFieldTemplate.phaseInTime (headerTokens q) newHeaderField
    Tape.copyScratch Tape.accumulator
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide) (by decide)
    (Label.emitHeader : MachineFieldTemplate.Label (headerTokens q).length → Label q)
    (some .guard) (program q) (fun _ => rfl)
    (MachineSubdivisionInit.resultTapes n q Q body) rfl initialState
  rw [header_template, header_copiedLength, header_result] at run
  simpa only [machine, FinTM2.step, FinTM2.Cfg, MachineFieldTemplate.reset, initialState,
    headerTokens, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
    using! run

/-- From raw input headers to the running occurrence loop, including all finite
arithmetic phases and literal output-header emission. -/
def prepareInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6 + 9 * MachineSubdivisionInit.stageCost n Q +
        (3 * (n + 7 * Q + 2) + 10)) := by
  have h := MachineSubdivisionHeaders.headersInTime q n Q body
  have i := MachineSubdivisionInit.initializeInTime q n Q body
  have e := headerInTime q n Q body
  have hi := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h i
  have hie := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hi e
  exact {
    toEvalsTo := hie.toEvalsTo
    steps_le_m := by
      have bound := hie.steps_le_m
      omega }

end UniqueGamesTheorem.Explicit.MachineSubdivisionEmission

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubdivisionTableRead
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual execution of the subdivision controller's full-table reader.
The reader consumes exactly the fixed number of zero-delimited table entries,
retains the unread input suffix, and reverses the saved table into forward order.
No table entry is stored in finite control; only the number of delimiters is.
-/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionTableRead

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

theorem step_true (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (true :: input) reversed⟩ =
      some ⟨some (.readTable completed), (ambient, some true),
        tapes base input (true :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input, update_reverse]

theorem step_false (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (false :: input) reversed⟩ =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input (false :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input, update_reverse]

/-- One encoded entry consumes its final delimiter in the same transition that
increments the finite completed-entry counter. -/
theorem readWordTrace (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (value : Nat) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[value + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWord value ++ input) reversed⟩) =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input ((encodeWord value).reverse ++ reversed)⟩ := by
  induction value generalizing reversed register with
  | zero =>
    simpa [encodeWord, MachineComposition.advance] using
      step_false q completed valid base input reversed ambient register
  | succ value ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append,
      MachineComposition.advance_some]
    rw [step_true q completed valid]
    have h := ih (true :: reversed) (some true)
    simpa only [encodeWord, List.reverse_cons, List.reverse_append,
      List.append_assoc, List.singleton_append] using h

/-- Read a suffix of the q-entry table, stopping before any following data. -/
theorem readWordsTrace (q : Nat) (words : List Nat) (completed : Fin (q + 1))
    (complete : completed.val + words.length = q) (base : Tape → List Bool)
    (suffix reversed : List Bool) (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWords words ++ suffix) reversed⟩) =
      some ⟨some .reverseTable, (ambient, none),
        tapes base suffix ((encodeWords words).reverse ++ reversed)⟩ := by
  induction words generalizing completed reversed register with
  | nil =>
    have hc : ¬ completed.val < q := by simpa using complete.ge
    simp [encodeWords, MachineComposition.advance, TM2.step, program, hc, TM2.stepAux]
  | cons value words ih =>
    have valid : completed.val < q := by simp only [List.length_cons] at complete; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at complete
      dsimp [next]
      omega
    have first := readWordTrace q completed valid base value (encodeWords words ++ suffix)
      reversed ambient register
    have second := ih next hn ((encodeWord value).reverse ++ reversed) none
    rw [encodeWords, List.length_append, encodeWord_length,
      show value + 1 + (encodeWords words).length + 1 =
        ((encodeWords words).length + 1) + (value + 1) by omega,
      Function.iterate_add_apply]
    simp only [List.append_assoc]
    rw [first]
    simpa only [next, List.reverse_append, List.append_assoc] using second

/-- Full exact table phase: read q delimited entries and reverse the physical
saved stack, arriving at the actual row-emission label. -/
theorem tableTrace (q : Nat) (words : List Nat) (length : words.length = q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[2 * (encodeWords words).length + 2]
      (some ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords words ++ suffix) []⟩) =
      some ⟨some (rowEntry q), (ambient, none), finalTapes base suffix (encodeWords words)⟩ := by
  have read := readWordsTrace q words 0 (by simpa using length) base suffix [] ambient register
  simp only [List.append_nil] at read
  have reverse := MachineTransfer.transferAt_fromTapes
    Tape.permutationReverse Tape.permutation (by decide) id false
    Label.reverseTable (some (rowEntry q)) (program q) rfl
    (tapes base suffix (encodeWords words).reverse) ambient none
  have finish : MachineTransfer.tapesAt Tape.permutationReverse Tape.permutation
      (tapes base suffix (encodeWords words).reverse) []
      (((tapes base suffix (encodeWords words).reverse) .permutationReverse).reverse.map id ++
        (tapes base suffix (encodeWords words).reverse) .permutation) =
      finalTapes base suffix (encodeWords words) := by
    funext k
    cases k <;> simp [MachineTransfer.tapesAt, tapes, finalTapes]
  rw [finish] at reverse
  simp only [tapes_reverse, List.length_reverse] at reverse
  rw [show 2 * (encodeWords words).length + 2 =
      ((encodeWords words).length + 1) + ((encodeWords words).length + 1) by omega,
    Function.iterate_add_apply, read]
  exact reverse

/-- Timed witness for the actual controller, with a fixed alphabet-dependent
bound on its full forward table. Other row fields and unread input are preserved. -/
def tableInTime {q : Nat} (table : Target.PermutationTable q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords (tableWords table) ++ suffix) []⟩
      (some ⟨some (rowEntry q), (ambient, none),
        finalTapes base suffix (encodeWords (tableWords table))⟩)
      (2 * (q * (q + 1)) + 2) where
  steps := 2 * (encodeWords (tableWords table)).length + 2
  evals_in_steps := tableTrace q (tableWords table) (tableWords_length table)
    base suffix ambient register
  steps_le_m := by
    have h := GameEncodingSize.tableBits_length_le table
    omega

end UniqueGamesTheorem.Explicit.MachineSubdivisionTableRead

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubdivisionBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
One whole occurrence iteration of the actual subdivision controller.
The proved trace includes both endpoint loads, the dynamic full-table reader,
the four-row template, all three local drains, and private-index increments.
-/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionBody

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

structure Ready {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Prop where
  input : base .input = encodeWord u ++ encodeWord v ++ tableBits table ++ suffix
  uEmpty : base .u = []
  vEmpty : base .v = []
  permutationEmpty : base .permutation = []
  reverseEmpty : base .permutationReverse = []
  scratchEmpty : base .copyScratch = []

def afterU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .u base u (encodeWord v ++ tableBits table ++ suffix)

def afterV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .v (afterU base u v table suffix) v (tableBits table ++ suffix)

def afterTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineSubdivisionTableRead.finalTapes (afterV base u v table suffix) suffix (tableBits table)

def rowPayload {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : List Bool :=
  MachineFieldTemplate.templateOutput (rowTokens q)
    (fun j => afterTable base u v table suffix (rowField j))

def afterRows {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterTable base u v table suffix) .accumulator
    (rowPayload base u v table suffix)

def afterDrainU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterRows base u v table suffix) .u []

def afterDrainV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainU base u v table suffix) .v []

def afterDrainTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainV base u v table suffix) .permutation []

def bodyResult {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  incrementTapes (afterDrainTable base u v table suffix)

def bodyBudget {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Nat :=
  (u + 2) + (v + 2) + (2 * (q * (q + 1)) + 2) +
    (3 * MachineFieldTemplate.copiedLength (rowTokens q)
      (fun j => afterTable base u v table suffix (rowField j)) + 37) +
    ((afterRows base u v table suffix .u).length + 1) +
    ((afterDrainU base u v table suffix .v).length + 1) +
    ((afterDrainV base u v table suffix .permutation).length + 1) + 1

def incrementInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .increment, initialState, base⟩
      (some ⟨some .guard, initialState, incrementTapes base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .increment) initialState base) = _
    simp [program, TM2.stepAux, incrementTapes, initialState]
  steps_le_m := Nat.le_refl _

/-- Complete actual `.startU → .guard` execution, without a phase-run premise. -/
def bodyInTime {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .startU, initialState, base⟩
      (some ⟨some .guard, initialState, bodyResult base u v table suffix⟩)
      (bodyBudget base u v table suffix) := by
  have hu : base .input = encodeWord u ++ (encodeWord v ++ tableBits table ++ suffix) := by
    simpa only [List.append_assoc] using ready.input
  let p₀ := SourceMachine.fieldInTime Tape.input Tape.u (by decide)
    Label.startU Label.readU (some .startV) (program q) rfl rfl base u
    (encodeWord v ++ tableBits table ++ suffix) hu ((), ()) none
  have hv : afterU base u v table suffix .input =
      encodeWord v ++ (tableBits table ++ suffix) := by
    simp [afterU, SourceMachine.afterField, SourceMachine.fieldTapes, List.append_assoc]
  let p₁ := SourceMachine.fieldInTime Tape.input Tape.v (by decide)
    Label.startV Label.readV (some (.readTable 0)) (program q) rfl rfl
    (afterU base u v table suffix) v (tableBits table ++ suffix) hv ((), ()) none
  have tableStart : MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
      (tableBits table ++ suffix) [] = afterV base u v table suffix := by
    funext k
    cases k <;> simp [MachineSubdivisionTableRead.tapes, afterV, afterU,
      SourceMachine.afterField, SourceMachine.fieldTapes, ready.reverseEmpty]
  have p₂ : StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), initialState, afterV base u v table suffix⟩
      (some ⟨some (rowEntry q), initialState, afterTable base u v table suffix⟩)
      (2 * (q * (q + 1)) + 2) := by
    have h := MachineSubdivisionTableRead.tableInTime table
      (afterV base u v table suffix) suffix ((), ()) none
    change StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨_, _, MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
        (tableBits table ++ suffix) []⟩ _ _ at h
    rw [tableStart] at h
    exact h
  have scratch : afterTable base u v table suffix .copyScratch = [] := by
    simp [afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
      afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, ready.scratchEmpty]
  let p₃ := MachineFieldTemplate.phaseInTime (rowTokens q) rowField
    Tape.copyScratch Tape.accumulator rowField_ne_scratch rowField_ne_accumulator (by decide)
    Label.emitRows (some .drainU) (program q) (fun _ => rfl)
    (afterTable base u v table suffix) scratch initialState
  let p₄ := MachineDrain.drainInTime Tape.u Label.drainU (some .drainV)
    (program q) rfl (afterRows base u v table suffix) ((), ()) none
  let p₅ := MachineDrain.drainInTime Tape.v Label.drainV (some .drainPermutation)
    (program q) rfl (afterDrainU base u v table suffix) ((), ()) none
  let p₆ := MachineDrain.drainInTime Tape.permutation Label.drainPermutation (some .increment)
    (program q) rfl (afterDrainV base u v table suffix) ((), ()) none
  let p₇ := incrementInTime q (afterDrainTable base u v table suffix)
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅
  let p₀₁₂₃₄₅₆ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆
  let full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅₆ p₇
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      have h := full.steps_le_m
      have tokens_length : (rowTokens q).length = 12 := rfl
      unfold bodyBudget
      omega
  }

end UniqueGamesTheorem.Explicit.MachineSubdivisionBody

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubdivisionBodySpecLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Exact tape framing, row serialization, and a uniform polynomial bound for
the already constructed whole subdivision-body execution. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionBodySpec

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram MachineSubdivisionBody

def resultTapes {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .u | .v | .permutation | .permutationReverse => []
  | .middle => true :: base .middle
  | .first => true :: true :: base .first
  | .last => true :: true :: base .last
  | .accumulator => (rowPayload base u v table suffix).reverse ++ base .accumulator
  | k => base k

/-- Every tape at the body boundary, including all preserved headers and counters. -/
theorem bodyResult_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix = resultTapes base u v table suffix := by
  cases ready
  funext k
  cases k <;> simp [bodyResult, incrementTapes, afterDrainTable, afterDrainV,
    afterDrainU, afterRows, MachineFieldTemplate.outputTapes, afterTable,
    MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, resultTapes]

theorem result_input {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .input = suffix := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem result_accumulator {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .accumulator =
      (rowPayload base u v table suffix).reverse ++ base .accumulator := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem encodeWord_succ (n : Nat) : encodeWord (n + 1) = true :: encodeWord n := by
  simp [encodeWord, List.replicate_succ]

theorem result_indices {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyResult base u v table suffix .middle = encodeWord (n + (e + 1)) ∧
    bodyResult base u v table suffix .first = encodeWord (n + Q + 2 * (e + 1)) ∧
    bodyResult base u v table suffix .last = encodeWord (n + Q + 2 * (e + 1) + 1) := by
  rw [bodyResult_eq base u v table suffix ready]
  have hm : n + (e + 1) = (n + e) + 1 := by omega
  have hf : n + Q + 2 * (e + 1) = (n + Q + 2 * e) + 1 + 1 := by omega
  simp [resultTapes, middle, first, last, hm, hf, encodeWord_succ]

/-- Four whole rows, with the final table already in left-to-right orientation. -/
def rowBits {q : Nat} (u middle first last v : Nat) (table : Target.PermutationTable q) :
    List Bool :=
  encodeWords
    ([u, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, last] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [v, last] ++ tableWords table)

theorem rowPayload_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (middle first last : Nat)
    (hm : base .middle = encodeWord middle) (hf : base .first = encodeWord first)
    (hl : base .last = encodeWord last) :
    rowPayload base u v table suffix = rowBits u middle first last v table := by
  simp [rowPayload, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput, rowField,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, hm, hf, hl,
    rowBits, tableBits, encodeWords, List.append_assoc]

/-- The natural-word description is literally the established finite-target
constraint codec, rather than an alternative encoding. -/
theorem rowBits_eq_dynamic {N q : Nat} (vertices : Fin 5 → Fin N)
    (table : Target.PermutationTable q) :
    rowBits (vertices 0).val (vertices 2).val (vertices 1).val (vertices 3).val
      (vertices 4).val table = MachineSubdivisionDynamicRows.rowBits vertices table := by
  simp [rowBits, MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionDynamicRows.rows,
    constraintWords, List.append_assoc]

/-- One conservative bound uniform over all occurrences in this output.
Only the fixed alphabet and the runtime header sizes appear in the polynomial. -/
theorem bodyBudget_le {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (hu : u < n) (hv : v < n) (he : e ≤ Q)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyBudget base u v table suffix ≤ 100 * (n + 3 * Q + q * (q + 1) + 1) := by
  have ht : (tableBits table).length ≤ q * (q + 1) :=
    GameEncodingSize.tableBits_length_le table
  simp [bodyBudget, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.copiedLength, rowField,
    afterDrainV, afterDrainU, afterRows, MachineFieldTemplate.outputTapes,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, middle, first, last] at *
  omega

end UniqueGamesTheorem.Explicit.MachineSubdivisionBodySpec

/-! Concrete frames and literal row words for the subdivision occurrence loop. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionLoopFrame

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

def bodyBits {n q : Nat} (edges : List (Constraint n q)) : List Bool :=
  encodeWords (edges.flatMap constraintWords)

@[simp] theorem bodyBits_nil {n q : Nat} : bodyBits ([] : List (Constraint n q)) = [] := rfl

theorem bodyBits_cons {n q : Nat} (edge : Constraint n q) (edges : List (Constraint n q)) :
    bodyBits (edge :: edges) =
      encodeWord edge.source.val ++ encodeWord edge.target.val ++
        MachineSubdivisionBody.tableBits edge.permutation ++ bodyBits edges := by
  simp [bodyBits, constraintWords, encodeWords, MachineSubdivisionBody.tableBits,
    List.append_assoc]

def rowBits {n q : Nat} (Q e : Nat) (edge : Constraint n q) : List Bool :=
  encodeWords [edge.source.val, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e + 1] ++ identityBits q ++
  encodeWords [edge.target.val, n + Q + 2 * e + 1] ++
    MachineSubdivisionBody.tableBits edge.permutation

def outputRows {n q : Nat} (Q : Nat) : Nat → List (Constraint n q) → List Bool
  | _, [] => []
  | e, edge :: edges => rowBits Q e edge ++ outputRows Q (e + 1) edges

def frame {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => bodyBits edges
  | .remaining => encodeWord edges.length
  | .middle => encodeWord (n + e)
  | .first => encodeWord (n + Q + 2 * e)
  | .last => encodeWord (n + Q + 2 * e + 1)
  | .accumulator => emitted.reverse
  | _ => MachineSubdivisionInit.resultTapes n q Q [] tape

def afterGuard {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) : Tape → List Bool :=
  Function.update (frame Q e (edge :: edges) emitted) .remaining (encodeWord edges.length)

theorem frame_prepared {n q : Nat} (edges : List (Constraint n q)) :
    frame edges.length 0 edges (MachineSubdivisionEmission.headerBits n q edges.length) =
      MachineSubdivisionEmission.resultTapes n q edges.length (bodyBits edges) := by
  funext tape
  cases tape <;> simp [frame, MachineSubdivisionEmission.resultTapes,
    MachineSubdivisionInit.resultTapes]

theorem guard_cons {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    (machine q).step ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ =
      some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩ := by
  have before : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) (edges.length + 1) [] =
      frame Q e (edge :: edges) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e (edge :: edges) emitted) Tape.remaining
      ((frame Q e (edge :: edges) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have after : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) edges.length [] =
      afterGuard Q e edge edges emitted := by
    simp [MachineUnaryCounter.counterTapes, afterGuard]
  have run := MachineUnaryCounter.guardStep_succ Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e (edge :: edges) emitted) edges.length [] ((), ()) none
  rw [before, after] at run
  simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState] using! run

theorem guard_nil (n q Q e : Nat) (emitted : List Bool) :
    (machine q).step
      ⟨some .guard, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ =
      some ⟨some .finishStart, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ := by
  have framed : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e ([] : List (Constraint n q)) emitted) 0 [] =
      frame Q e ([] : List (Constraint n q)) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e ([] : List (Constraint n q)) emitted) Tape.remaining
      ((frame Q e ([] : List (Constraint n q)) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have run := MachineUnaryCounter.guardStep_zero Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e ([] : List (Constraint n q)) emitted) [] ((), ()) none
  rw [framed] at run
  simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState] using! run

theorem ready {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.Ready (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) := by
  constructor
  · simpa only [afterGuard, Function.update_of_ne (by decide : Tape.input ≠ .remaining),
      frame] using bodyBits_cons edge edges
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]

end UniqueGamesTheorem.Explicit.MachineSubdivisionLoopFrame

/-! The actual streamed bytes coincide with the numbered semantic subdivision.
The controller copies the last table unchanged, so its input contract explicitly
requires involutive tables; binary translations satisfy this condition. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionCorrespondence

open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionLoopFrame

def Involutive {q : Nat} (H : Instance q) : Prop :=
  ∀ e : Fin H.constraints.length,
    MachineSubdivisionRows.inverseTable H.constraints[e].permutation = H.constraints[e].permutation

theorem inverseTable_eq {q : Nat} (p : PermutationTable q)
    (same : p.inverseImages = p.images) : MachineSubdivisionRows.inverseTable p = p := by
  cases p with
  | mk images inverseImages left right =>
    dsimp at same
    cases same
    rfl

theorem translations_involutive {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (translations : Integration.TranslationTarget.IsTranslationInstance coordinates H) :
    Involutive H := by
  intro e
  apply inverseTable_eq
  apply Vector.ext
  intro i hi
  apply coordinates.injective
  obtain ⟨shift, law⟩ := translations H.constraints[e] (List.getElem_mem e.isLt)
  have h := law (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)])
  rw [H.constraints[e].permutation.rightInverse] at h
  have cancel : shift + shift = 0 := by
    ext j
    simp [CharTwo.add_self_eq_zero]
  have doubled := congrArg (fun x => x + shift) h
  have inverseLaw : coordinates (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)]) =
      coordinates ⟨i, hi⟩ + shift := by
    simpa only [add_assoc, cancel, add_zero] using doubled.symm
  exact inverseLaw.trans (law ⟨i, hi⟩).symm

theorem rowBits_eq_semantic {q : Nat} (H : Instance q) (e : Fin H.constraints.length)
    (involutive : Involutive H) :
    rowBits H.constraints.length e.val H.constraints[e] =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
  have words := MachineSubdivisionBodySpec.rowBits_eq_dynamic
    (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation
  have vertices (j : Fin 5) := SubdivisionTarget.vertexFields_val H e j
  simp only [MachineSubdivisionRows.subdivisionVertexWords] at vertices
  have dynamic : MachineSubdivisionDynamicRows.rowBits
      (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
    simp only [MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionRows.rowBits,
      MachineSubdivisionDynamicRows.rows, MachineSubdivisionRows.rows, involutive e]
  rw [← dynamic, ← words]
  simp only [vertices, MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem outputRows_eq_ofFn {n q : Nat} (Q e : Nat) (edges : List (Constraint n q)) :
    outputRows Q e edges =
      (List.ofFn (fun i : Fin edges.length => rowBits Q (e + i.val) edges[i])).flatten := by
  induction edges generalizing e with
  | nil => rfl
  | cons edge edges ih =>
    rw [outputRows, ih, List.ofFn_succ]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem outputRows_eq_semantic {q : Nat} (H : Instance q) (involutive : Involutive H) :
    outputRows H.constraints.length 0 H.constraints =
      (List.finRange H.constraints.length).flatMap (fun e =>
        MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
          H.constraints[e].permutation) := by
  rw [outputRows_eq_ofFn]
  simp only [Nat.zero_add, rowBits_eq_semantic H _ involutive, List.ofFn_eq_map,
    List.flatMap_def]

/-- Exact complete serialized output, including the changed headers and every
forward permutation-table entry, in occurrence order. -/
theorem output_eq_gameBits {q : Nat} (H : Instance q) (involutive : Involutive H) :
    MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints =
      gameBits (SubdivisionTarget.subdivide H) := by
  rw [SubdivisionEncoding.subdivide_gameBits, outputRows_eq_semantic H involutive]
  rfl

end UniqueGamesTheorem.Explicit.MachineSubdivisionCorrespondence

/-! Complete physical occurrence traversal of the subdivision program. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionLoop

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame

theorem rowPayload_eq {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.rowPayload (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) = rowBits Q e edge := by
  rw [MachineSubdivisionBodySpec.rowPayload_eq _ _ _ _ _ (ready Q e edge edges emitted)
    (n + e) (n + Q + 2 * e) (n + Q + 2 * e + 1) rfl rfl rfl]
  simp only [MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem bodyResult_eq_frame {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.bodyResult (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) =
      frame Q (e + 1) edges (emitted ++ rowBits Q e edge) := by
  have indices := MachineSubdivisionBodySpec.result_indices
    (afterGuard Q e edge edges emitted) edge.source.val edge.target.val edge.permutation
    (bodyBits edges) (ready Q e edge edges emitted) n Q e rfl rfl rfl
  funext tape
  cases tape with
  | middle => exact indices.1
  | first => exact indices.2.1
  | last => exact indices.2.2
  | input => exact MachineSubdivisionBodySpec.result_input _ _ _ _ _ (ready Q e edge edges emitted)
  | accumulator =>
    rw [MachineSubdivisionBodySpec.result_accumulator _ _ _ _ _ (ready Q e edge edges emitted),
      rowPayload_eq]
    simp [afterGuard, frame, List.reverse_append]
  | _ =>
    rw [MachineSubdivisionBodySpec.bodyResult_eq _ _ _ _ _ (ready Q e edge edges emitted)]
    simp [MachineSubdivisionBodySpec.resultTapes, afterGuard, frame,
      MachineSubdivisionInit.resultTapes]

def bodyInTime {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) (he : e ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩
      (some ⟨some .guard, initialState, frame Q (e + 1) edges (emitted ++ rowBits Q e edge)⟩)
      (bodyBound n q Q) := by
  have run := MachineSubdivisionBody.bodyInTime (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
  rw [bodyResult_eq_frame] at run
  have bound := MachineSubdivisionBodySpec.bodyBudget_le (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
    n Q e edge.source.isLt edge.target.isLt he rfl rfl rfl
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := run.steps_le_m.trans bound }

/-- Every list occurrence is read once, emits exactly its four rows, and advances
the three private numeric names. The loop includes its final zero-counter test. -/
def loopInTime {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) (fit : e + edges.length ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .guard, initialState, frame Q e edges emitted⟩
      (some ⟨some .finishStart, initialState,
        frame Q (e + edges.length) ([] : List (Constraint n q))
          (emitted ++ outputRows Q e edges)⟩)
      (edges.length * (bodyBound n q Q + 1) + 1) := by
  induction edges generalizing e emitted with
  | nil =>
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := by simp }
    change (machine q).step ⟨some .guard, initialState, frame Q e [] emitted⟩ = _
    simpa only [List.length_nil, Nat.add_zero, outputRows, List.append_nil]
      using guard_nil n q Q e emitted
  | cons edge edges ih =>
    have he : e ≤ Q := by simp only [List.length_cons] at fit; omega
    have remainingFit : (e + 1) + edges.length ≤ Q := by
      simp only [List.length_cons] at fit
      omega
    have guard : StateTransition.EvalsToInTime (machine q).step
        ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩
        (some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩) 1 := {
      steps := 1
      evals_in_steps := by
        change (machine q).step
          ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ = _
        exact guard_cons Q e edge edges emitted
      steps_le_m := Nat.le_refl _ }
    have body := bodyInTime Q e edge edges emitted he
    have tail := ih (e + 1) (emitted ++ rowBits Q e edge) remainingFit
    have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first tail
    have index_eq : (e + 1) + edges.length = e + (edge :: edges).length := by simp; omega
    have words_eq : (emitted ++ rowBits Q e edge) ++ outputRows Q (e + 1) edges =
        emitted ++ outputRows Q e (edge :: edges) := by
      simp only [outputRows, List.append_assoc]
    rw [index_eq, words_eq] at whole
    exact {
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega }

end UniqueGamesTheorem.Explicit.MachineSubdivisionLoop

/-! The complete finite subdivision machine, including its polynomial runtime
in the actual serialized input length and exact full-table output. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionRuntime

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame
open MachineSubdivisionCorrespondence

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSubdivisionFinish.timePolynomial q (prefixPolynomial q)

theorem input_eq {q : Nat} (H : Instance q) :
    gameBits H = encodeWords [H.vertices, q, H.constraints.length] ++ bodyBits H.constraints := by
  simp only [gameBits, gameWords, bodyBits, encodeWords_append]

theorem input_size {q : Nat} (H : Instance q) :
    H.vertices ≤ (gameBits H).length ∧ H.constraints.length ≤ (gameBits H).length := by
  rw [input_eq]
  simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

def finalTapes {q : Nat} (H : Instance q) : Tape → List Bool :=
  frame H.constraints.length H.constraints.length ([] : List (Constraint H.vertices q))
    (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints)

theorem final_outputEmpty {q : Nat} (H : Instance q) : finalTapes H .output = [] := rfl

theorem final_accumulator {q : Nat} (H : Instance q) (involutive : Involutive H) :
    finalTapes H .accumulator = (gameBits (SubdivisionTarget.subdivide H)).reverse := by
  change (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
    outputRows H.constraints.length 0 H.constraints).reverse = _
  rw [output_eq_gameBits H involutive]

/-- The prefix contains every actual header read, fresh-name initialization,
header emission, complete four-row body, and occurrence-counter test. -/
def prefixInTime {q : Nat} (H : Instance q) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (gameBits H))
      (some ⟨some .finishStart, initialState, finalTapes H⟩)
      ((prefixPolynomial q).eval (gameBits H).length) := by
  have initial := MachineSubdivisionEmission.prepareInTime q H.vertices H.constraints.length
    (bodyBits H.constraints)
  rw [← input_eq H, ← frame_prepared H.constraints] at initial
  have loop := MachineSubdivisionLoop.loopInTime H.constraints.length 0 H.constraints
    (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length) (by simp)
  simp only [Nat.zero_add] at loop
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initial loop
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := ?_ }
  have hn := (input_size H).1
  have hQ := (input_size H).2
  have bodyBound : MachineSubdivisionLoop.bodyBound H.vertices q H.constraints.length + 1 ≤
      100 * (4 * (gameBits H).length + q * (q + 1) + 1) + 1 := by
    unfold MachineSubdivisionLoop.bodyBound
    omega
  have loopBound := Nat.mul_le_mul hQ bodyBound
  have prepBound : H.vertices + q + H.constraints.length + 6 +
      9 * MachineSubdivisionInit.stageCost H.vertices H.constraints.length +
      (3 * (H.vertices + 7 * H.constraints.length + 2) + 10) ≤
      62 * (gameBits H).length + q + 49 := by
    unfold MachineSubdivisionInit.stageCost
    omega
  have bound := whole.steps_le_m
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  omega

/-- Literal initialization to literal clean halting configuration, with exact
semantic subdivision output. No execution or runtime premise is assumed. -/
def fullRunInTime {q : Nat} (H : Instance q) (involutive : Involutive H) :
    TM2OutputsInTime (machine q) (gameBits H)
      (some (gameBits (SubdivisionTarget.subdivide H)))
      ((timePolynomial q).eval (gameBits H).length) := by
  have run := MachineSubdivisionFinish.completePrefix q (gameBits H) (prefixPolynomial q)
    (finalTapes H) (prefixInTime H) (final_outputEmpty H)
  simpa only [final_accumulator H involutive, List.reverse_reverse, timePolynomial] using run

/-- The input subtype records the mathematical involution property, while the
same finite transition program is used for every instance of the fixed alphabet. -/
def computableInPolyTime (q : Nat) :
    TM2ComputableInPolyTime
      (fun H : {H : Instance q // Involutive H} => gameBits H.val)
      gameBits (fun H => SubdivisionTarget.subdivide H.val) where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun H := by
    change TM2OutputsInTime (machine q) ((gameBits H.val).map id)
      (some ((gameBits (SubdivisionTarget.subdivide H.val)).map id))
      ((timePolynomial q).eval (gameBits H.val).length)
    erw [List.map_id, List.map_id]
    exact fullRunInTime H.val H.property

theorem workAlphabetFinite (q : Nat) (tape : (computableInPolyTime q).tm.K) :
    Finite ((computableInPolyTime q).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.Explicit.MachineSubdivisionRuntime

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionCompose

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionCorrespondence

variable {α : Type} {q : Nat} {encode : α → List Bool} {f : α → Instance q}

def certifiedOutput (involutive : ∀ a, Involutive (f a)) (a : α) :
    {H : Instance q // Involutive H} := ⟨f a, involutive a⟩

/-- Attach the already-proved property without executing anything or changing
the input or output codec. -/
def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime encode (fun H : {H : Instance q // Involutive H} => gameBits H.val)
      (certifiedOutput involutive) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

def computableInPolyTime (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime encode gameBits (fun a => SubdivisionTarget.subdivide (f a)) :=
  MachineSequential.composeBits (f := certifiedOutput involutive)
    (g := fun H : {H : Instance q // Involutive H} => SubdivisionTarget.subdivide H.val)
    (certify upstream involutive)
    (MachineSubdivisionRuntime.computableInPolyTime q)

theorem finiteAlphabet (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a))
    (finite : MachineFiniteAlphabet.FiniteAlphabet upstream.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime upstream involutive).tm := by
  exact MachineFiniteAlphabet.composeBits (certify upstream involutive)
    (MachineSubdivisionRuntime.computableInPolyTime q) finite
    (MachineSubdivisionRuntime.workAlphabetFinite q)

/-- Binary-translation producers discharge the only table-law condition. -/
def translationComputableInPolyTime {s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s)
    (upstream : TM2ComputableInPolyTime encode gameBits f)
    (translations : ∀ a, Integration.TranslationTarget.IsTranslationInstance coordinates (f a)) :
    TM2ComputableInPolyTime encode gameBits (fun a => SubdivisionTarget.subdivide (f a)) :=
  computableInPolyTime upstream (fun a => translations_involutive coordinates (f a) (translations a))

end UniqueGamesTheorem.Explicit.MachineSubdivisionCompose

/-! A real finite program for uniform whole-instance copying. It reads three
headers, physically multiplies the occurrence count by the fixed constant,
copies the header-free body the same fixed number of times, and clears all
working tapes. No input-dependent data are placed in finite control. -/

namespace UniqueGamesTheorem.Explicit.MachineUniformProgram

open Turing UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad

def program (C : Nat) : Label C → TM2.Stmt (fun _ : Tape => Bool) (Label C) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .scale 0 => MachineUnaryAffineAt.seed .newOccurrences 0 (.scale 1)
  | .scale 1 => MachineUnaryAffineAt.scan .occurrences .affineScratch
      .newOccurrences C (.scale 1) (.scale 2)
  | .scale 2 => MachineTransfer.loopAt .affineScratch .occurrences id false
      (.scale 2) (some (emitEntry C))
  | .emit label => MachineFieldTemplate.instruction (tokens C) emitField
      .copyScratch .accumulator Label.emit (some .finishStart) label
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (C : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label C
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program C

theorem covers (k : Tape) (ha : k ≠ .accumulator) (ho : k ≠ .output) :
    k ∈ clearKeys := by
  cases k <;> simp_all [clearKeys]

end UniqueGamesTheorem.Explicit.MachineUniformProgram

/-! Exact execution of the three input-header reads of uniform copying. -/

namespace UniqueGamesTheorem.Explicit.MachineUniformHeaders

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineUniformProgram

def afterVertices (n : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n else []

def afterAlphabet (n q : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q else []

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q
    else if k = .occurrences then encodeWord Q else []

theorem initList_eq (C : Nat) (bits : List Bool) :
    initList (machine C) bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1

theorem first_result (n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .vertices
      (inputTapes (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes (encodeWord n ++ rest) .vertices) =
      afterVertices n rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices]

theorem second_result (n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .alphabet
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabet) =
      afterAlphabet n q rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet]

theorem third_result (n q Q : Nat) (body : List Bool) :
    SourceMachine.fieldTapes Tape.input .occurrences
      (afterAlphabet n q (encodeWord Q ++ body)) body
      (encodeWord Q ++ afterAlphabet n q (encodeWord Q ++ body) .occurrences) =
      resultTapes n q Q body := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterAlphabet, resultTapes]

/-- The input headers are consumed literally; all unread constraint bits retain
their original order and no tape contains an implicit runtime number. -/
def headersInTime (C q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label C) (.headerRead 0) (some (.headerStart 1))
    (program C) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabet (by decide)
    (.headerStart 1 : Label C) (.headerRead 1) (some (.headerStart 2))
    (program C) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label C) (.headerRead 2) (some (.scale 0))
    (program C) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  simpa only [encodeWords, List.nil_append, List.append_assoc, machine, FinTM2.step,
    FinTM2.Cfg, initialState]
    using! ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program C))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

end UniqueGamesTheorem.Explicit.MachineUniformHeaders

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUniformRun
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-instance uniform copying: exact physical header arithmetic, repeated
body emission, actual cleanup, and a polynomial bound in the input codec length. -/

namespace UniqueGamesTheorem.Explicit.MachineUniformRun

open Turing UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Foundations Target
open UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad
open MachineUniformProgram

def afterScale (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineUniformHeaders.resultTapes n q Q body)
    .newOccurrences (encodeWord (C * Q))

def afterEmit (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterScale C n q Q body)
    .accumulator (outputBits C n q Q body)

def scaleInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩
      (some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩)
      (2 * (Q + 1) + 1) where
  steps := 2 * (Q + 1) + 1
  evals_in_steps := by
    change (MachineComposition.advance (machine C).step)^[2 * (Q + 1) + 1]
      (some ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩) =
      some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
    have h := MachineUnaryAffineAt.seededAffineTrace Tape.occurrences .affineScratch
      .newOccurrences (by decide) (by decide) (by decide) C 0
      (.scale 0 : Label C) (.scale 1) (.scale 2) (some (emitEntry C))
      (program C) rfl rfl rfl (MachineUniformHeaders.resultTapes n q Q body)
      Q [] (by simp [MachineUniformHeaders.resultTapes])
      (by simp [MachineUniformHeaders.resultTapes]) ((), ()) none
    simpa only [machine, FinTM2.step, FinTM2.Cfg,
      initialState, afterScale,
      show MachineUniformHeaders.resultTapes n q Q body .newOccurrences = [] from rfl,
      Nat.add_zero, List.append_nil] using! h
  steps_le_m := Nat.le_refl _

theorem template_output (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) = outputBits C n q Q body := by
  simp only [tokens, MachineFieldTemplate.templateOutput, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, MachineFieldTemplate.tokenOutput]
  rw [show (List.replicate C (MachineFieldTemplate.Token.copy (3 : Fin 4))).flatMap
      (MachineFieldTemplate.tokenOutput (fun i => afterScale C n q Q body (emitField i))) =
        MachineUniformCopyOrder.copyMajor C (afterScale C n q Q body (emitField 3)) from
      repeated_template C _]
  simp [afterScale, MachineUniformHeaders.resultTapes, emitField, outputBits,
    encodeWords, List.append_assoc]

theorem template_copiedLength (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) =
        n + q + C * Q + 3 + C * body.length := by
  simp [MachineFieldTemplate.copiedLength, tokens, afterScale,
    MachineUniformHeaders.resultTapes, emitField, Nat.add_assoc]
  omega

def emitInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      (3 * (n + q + C * Q + 3 + C * body.length) + 3 * (C + 3) + 1) := by
  have h := MachineFieldTemplate.phaseInTime (tokens C) emitField
    Tape.copyScratch .accumulator
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide) (by decide)
    (Label.emit (C := C)) (some .finishStart) (program C) (fun _ => rfl)
    (afterScale C n q Q body) (by simp [afterScale, MachineUniformHeaders.resultTapes])
    initialState
  simpa only [machine, FinTM2.step, FinTM2.Cfg, emitEntry,
    MachineFieldTemplate.reset, initialState,
    template_output, template_copiedLength, afterEmit,
    show (tokens C).length = C + 3 by simp [tokens]] using! h

def prefixInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      ((prefixPolynomial C).eval (encodeWords [n, q, Q] ++ body).length) := by
  let first := MachineUniformHeaders.headersInTime C q n Q body
  let second := scaleInTime C n q Q body
  let third := emitInTime C n q Q body
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo third
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, input_length]
  have hcopy : n + q + C * Q + 3 + C * body.length ≤
      (C + 1) * (n + q + Q + 3 + body.length) := by nlinarith
  nlinarith

noncomputable def timePolynomial (C : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine C) clearKeys.length (prefixPolynomial C + 1)

theorem haltList_eq (C : Nat) (bits : List Bool) :
    haltList (machine C) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  (cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes, Function.update]); rfl

def finishStartInTime (C : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (C := C)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program C .finishStart) initialState base) = _
    rfl
  steps_le_m := Nat.le_refl _

/-- The complete actual run, including the physical cleanup and output reversal. -/
noncomputable def outputInTime (C n q Q : Nat) (body : List Bool) :
    TM2OutputsInTime (machine C) (encodeWords [n, q, Q] ++ body)
      (some (outputBits C n q Q body))
      ((timePolynomial C).eval (encodeWords [n, q, Q] ++ body).length) := by
  let initialRun := prefixInTime C n q Q body
  let bridge := finishStartInTime C (afterEmit C n q Q body)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initialRun bridge
  let prefixRun : StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (C := C)), initialState,
        afterEmit C n q Q body⟩)
      ((prefixPolynomial C + 1).eval (encodeWords [n, q, Q] ++ body).length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm]
      using joined.steps_le_m }
  have hout : afterEmit C n q Q body .output = [] := by
    simp [afterEmit, MachineFieldTemplate.outputTapes, afterScale,
      MachineUniformHeaders.resultTapes]
  let finish := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (C := C)) none (program C) (fun _ => rfl)
    (afterEmit C n q Q body) hout ((), ()) none
  let whole := SourceRuntimeSpace.prefixAndFinishInTime (machine C)
    (encodeWords [n, q, Q] ++ body) (prefixPolynomial C + 1) prefixRun
    clearKeys Tape.accumulator Tape.output accumulator_not_mem_clearKeys
    output_not_mem_clearKeys covers (afterEmit C n q Q body) hout (fun _ => rfl) finish
  have hword : (afterEmit C n q Q body .accumulator).reverse = outputBits C n q Q body := by
    simp [afterEmit, MachineFieldTemplate.outputTapes, afterScale,
      MachineUniformHeaders.resultTapes]
  change StateTransition.EvalsToInTime (machine C).step _
    (some (haltList (machine C) (outputBits C n q Q body))) _
  rw [haltList_eq, ← hword]
  exact whole

/-- A fixed actual program works for every game and every alphabet size. -/
noncomputable def computation {q : Nat} (C : Nat) (hC : 0 < C) :
    TM2ComputableInPolyTime gameBits gameBits (UniformTarget.construct (q := q) C hC) where
  tm := machine C
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial C
  outputsFun g := by
    change TM2OutputsInTime (machine C) ((gameBits g).map id)
      (some ((gameBits (UniformTarget.construct C hC g)).map id)) _
    have input_eq : @List.map ((machine C).Γ (machine C).k₀)
        ((machine C).Γ (machine C).k₀) id (gameBits g) = gameBits g := List.map_id _
    have output_eq : @List.map ((machine C).Γ (machine C).k₁)
        ((machine C).Γ (machine C).k₁) id (gameBits (UniformTarget.construct C hC g)) =
        gameBits (UniformTarget.construct C hC g) := List.map_id _
    simp only [input_eq, output_eq]
    rw [UniformTarget.gameBits_construct]
    have input : gameBits g = encodeWords [g.vertices, q, g.constraints.length] ++
        encodeWords (g.constraints.flatMap constraintWords) := by
      simp [gameBits, gameWords, encodeWords, List.append_assoc]
    rw [input]
    exact outputInTime C g.vertices q g.constraints.length
      (encodeWords (g.constraints.flatMap constraintWords))

theorem finiteAlphabet {q : Nat} (C : Nat) (hC : 0 < C) :
    MachineFiniteAlphabet.FiniteAlphabet (computation (q := q) C hC).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

end UniqueGamesTheorem.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextClear
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

open Turing Complexity MachineComposition

abbrev Tape := SourceContextLoad.Tape

end UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryOrderLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature


abbrev BodyExtra (Extra : Type) := SourceLoopInit.HeaderTape ⊕ BodyWork Extra

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel

open Turing Complexity SourceRuntimeModel


abbrev Extra (u D : Nat) := SourceHeaderCounts.Coefficients u D ⊕ Unit

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel



end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_CollisionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Every finite projection game has an exact conditional-kernel representation.
The right question uses its original marginal. Conditional left-question laws
are normalized original rows; zero rows use the original left marginal as a
fallback. Their zero outer weight makes the reconstruction identity valid on
all rows without positivity or support hypotheses.
-/

namespace UniqueGamesTheorem.Repetition

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

@[simp] theorem toGame_kernelOfGame
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    (kernelOfGame G hG).toGame = G := by
  have hq : (kernelOfGame G hG).toGame.questions = G.questions :=
    FiniteDistribution.eq_of_weight_eq (kernelOfGame_question_weight G hG)
  calc
    _ = { questions := G.questions, accepts := G.accepts } := by
      change Game.mk (kernelOfGame G hG).toGame.questions G.accepts =
        Game.mk G.questions G.accepts
      rw [hq]
    _ = G := by cases G; rfl

@[simp] theorem kernelOfGame_success
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    (kernelOfGame G hG).toGame.success strategy = G.success strategy := by
  rw [toGame_kernelOfGame]

@[simp] theorem kernelOfGame_value [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    (kernelOfGame G hG).toGame.value = G.value := by
  rw [toGame_kernelOfGame]

end
end UniqueGamesTheorem.Repetition

end

section

/-! Comparison of the actual classical game value with the squared collision
norm. Both directions are proved for the normalized conditional kernel, including
partial projection constraints and zero-weight questions. -/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

theorem apply_assignment_nonneg (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) (b : A₂) :
    0 ≤ K.apply (assignment labels) y b := by
  rw [apply_assignment]
  exact (K.inner y).probability_nonnegative (fun x => K.accepts x y (labels x) b)

theorem success_eq_outer_apply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) :
    K.toGame.success s =
      K.outer.expectation (fun y => K.apply (assignment s.1) y (s.2 y)) := by
  classical
  simp only [Game.success, Game.wins, toGame, FiniteDistribution.probability,
    FiniteDistribution.expectation, apply_assignment, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : K.accepts x y (s.1 x) (s.2 y) = true <;> simp [h]

theorem success_sq_le_assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) :
    K.toGame.success s ^ 2 ≤ K.assignmentEnergy s.1 := by
  rw [success_eq_outer_apply]
  calc
    _ ≤ K.outer.expectation
        (fun y => K.apply (assignment s.1) y (s.2 y) ^ 2) :=
      sq_expectation_le_expectation_sq K.outer _
    _ ≤ K.assignmentEnergy s.1 := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (K.outer.nonnegative y)
      exact Finset.single_le_sum (fun b _ => sq_nonneg _) (Finset.mem_univ (s.2 y))

theorem value_sq_le_collisionValue [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    K.toGame.value ^ 2 ≤ K.collisionValue := by
  obtain ⟨s, hs⟩ := K.toGame.exists_optimal_strategy
  rw [← hs]
  exact (K.success_sq_le_assignmentEnergy s).trans (K.assignmentEnergy_le_collisionValue s.1)

theorem assignmentEnergy_le_value [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    K.assignmentEnergy labels ≤ K.toGame.value := by
  obtain ⟨answers, hanswers⟩ := K.exists_best_response labels
  calc
    _ ≤ K.toGame.success (labels, answers) := by
      rw [success_eq_outer_apply]
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (K.outer.nonnegative y)
      calc
        _ ≤ ∑ b, K.apply (assignment labels) y b *
            K.apply (assignment labels) y (answers y) := by
          apply Finset.sum_le_sum
          intro b _
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left (hanswers y b)
            (K.apply_assignment_nonneg labels y b)
        _ = (∑ b, K.apply (assignment labels) y b) *
            K.apply (assignment labels) y (answers y) := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * K.apply (assignment labels) y (answers y) :=
          mul_le_mul_of_nonneg_right (K.sum_apply_assignment_le_one labels y)
            (K.apply_assignment_nonneg labels y (answers y))
        _ = _ := one_mul _
    _ ≤ K.toGame.value := K.toGame.success_le_value _

theorem collisionValue_le_value [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    K.collisionValue ≤ K.toGame.value :=
  (K.collisionValue_le_iff _).mpr K.assignmentEnergy_le_value

theorem collisionValue_le_one [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : K.collisionValue ≤ 1 :=
  K.collisionValue_le_value.trans K.toGame.value_le_one

end ProjectionKernel
end
end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_RoundingSampling
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Correlated rounding of finite partial assignments of equal density. A common
finite list of seeds is scanned locally at every vertex. An edge succeeds when
the first seed accepted by either endpoint is a jointly accepted good seed.
The finite truncation error is at most `(1 - density)^n`. Maximizing over the finite
set of deterministic labelings removes that error. No infinite random seed or
assumed rounding principle is used.
-/

namespace UniqueGamesTheorem.Repetition

open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Foundations.CorrelatedSampling
open UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators

noncomputable section

variable {V S A : Type*} [Fintype V] [Fintype S] [Fintype A]

omit [Fintype V] [Fintype A] in
theorem partial_mass_bounds (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (density : ℝ)
    (hdensity : ∀ v, μ.probability (accept v) = density) (x y : V) :
    0 ≤ partialPairMass μ accept label R x y ∧
    partialPairMass μ accept label R x y ≤ density ∧
    density ≤ μ.probability (fun s => accept x s || accept y s) ∧
    μ.probability (fun s => accept x s || accept y s) +
      partialPairMass μ accept label R x y ≤ 2 * density := by
  refine ⟨μ.probability_nonnegative _, ?_, ?_, ?_⟩
  · rw [← hdensity x]
    apply μ.probability_mono
    intro s hs
    have hp : (accept x s = true ∧ accept y s = true) ∧
        R x y (label x s) (label y s) = true := by simpa using hs
    exact hp.1.1
  · rw [← hdensity x]
    exact μ.probability_mono (fun s hs => by simp [hs])
  · calc
      _ ≤ μ.probability (accept x) + μ.probability (accept y) := by
        unfold partialPairMass FiniteDistribution.probability
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro s _
        cases hx : accept x s <;> cases hy : accept y s <;>
          cases hr : R x y (label x s) (label y s) <;>
          simp [hx, hy, hr]
        linarith [μ.nonnegative s]
      _ = 2 * density := by rw [hdensity x, hdensity y]; ring

omit [Fintype V] [Fintype A] in
/-- Pointwise success bound for the actual shared finite first-accept sampler.
The relation may depend on the ordered pair and need not be symmetric. -/
theorem partialSample_pair_lower (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (fallback : A) (density : ℝ)
    (hdensity₀ : 0 < density) (hdensity : ∀ v, μ.probability (accept v) = density)
    (x y : V) (n : Nat) :
    2 * (partialPairMass μ accept label R x y / density) - 1 - (1 - density) ^ n ≤
      traceAverage μ.weight n (fun proposals =>
        if R x y (partialSample accept label fallback proposals x)
          (partialSample accept label fallback proposals y) then 1 else 0) := by
  classical
  let union : S → Bool := fun s => accept x s || accept y s
  let good : S → Bool := fun s =>
    accept x s && accept y s && R x y (label x s) (label y s)
  obtain ⟨hg, _, hlu, hug⟩ := partial_mass_bounds μ accept label R density hdensity x y
  have hu : 0 < eventMass μ.weight union := lt_of_lt_of_le hdensity₀ hlu
  have hm : eventMass μ.weight (fun s => union s && good s) =
      partialPairMass μ accept label R x y := by
    unfold eventMass partialPairMass FiniteDistribution.probability
    apply Finset.sum_congr rfl
    intro s _
    cases hx : accept x s <;> cases hy : accept y s <;> simp [union, good, hx, hy]
  have hfirst := goodFirstMass_lower_bound μ.weight union good
    μ.nonnegative μ.normalized hu n
  rw [hm] at hfirst
  have hactual := traceAverage_mono μ.weight μ.nonnegative n _ _
    (first_good_relation_le accept label R fallback x y)
  rw [goodFirstIndicator_law μ.weight _ _ μ.normalized n] at hactual
  have hcompl := eventMass_complement μ.weight union μ.normalized
  have hre : eventMass μ.weight (fun s => !(union s)) ≤ 1 - density := by
    change density ≤ eventMass μ.weight union at hlu
    linarith
  have hp := pow_le_pow_left₀
    (eventMass_nonneg μ.weight (fun s => !(union s)) μ.nonnegative) hre n
  have hr := partial_ratio_bound hdensity₀ hg hlu hug
  change 2 * (partialPairMass μ accept label R x y / density) - 1 ≤
    partialPairMass μ accept label R x y / eventMass μ.weight union at hr
  change goodFirstMass μ.weight union good n ≤ _ at hactual
  linarith

/-- Finite partial-assignment correlated rounding. Every vertex has acceptance
probability `density`. The normalized accepted good-pair mass `T` gives an actual
deterministic labeling with success at least `2*T - 1`. -/
theorem exists_labeling_ge_partial {E : Type*} [Fintype E] [Nonempty V] [Nonempty A]
    (μ : FiniteDistribution S) (ν : FiniteDistribution E)
    (accept : V → S → Bool) (label : V → S → A)
    (left right : E → V) (R : E → A → A → Bool) (density : ℝ) (hdensity₀ : 0 < density)
    (hdensity : ∀ v, μ.probability (accept v) = density) :
    ∃ f : V → A,
      2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1 ≤
        partialLabelScore ν left right R f := by
  classical
  let fallback : A := Classical.choice inferInstance
  obtain ⟨best, _, hbest⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (V → A))) Finset.univ_nonempty (partialLabelScore ν left right R)
  have hmax (f : V → A) :
      partialLabelScore ν left right R f ≤ partialLabelScore ν left right R best := by
    rw [← hbest]
    exact Finset.le_sup' (partialLabelScore ν left right R) (Finset.mem_univ f)
  have hbounded (n : Nat) :
      2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1 -
        (1 - density) ^ n ≤ partialLabelScore ν left right R best := by
    let seeds := traceSeedLaw μ n
    let sample := fun seed => partialSample accept label fallback (traceList n seed)
    have hpoint (e : E) := partialSample_pair_lower μ accept label (fun _ _ => R e)
      fallback density hdensity₀ hdensity (left e) (right e) n
    change ∀ e : E, 2 * (partialEdgeMass μ accept label left right R e / density) - 1 -
      (1 - density) ^ n ≤ traceAverage μ.weight n (fun proposals =>
        if R e (partialSample accept label fallback proposals (left e))
          (partialSample accept label fallback proposals (right e)) then 1 else 0) at hpoint
    have hlower := expectation_mono' ν hpoint
    rw [expectation_partial_lower] at hlower
    have hswitch :
        ν.expectation (fun e => traceAverage μ.weight n (fun proposals =>
          if R e (partialSample accept label fallback proposals (left e))
            (partialSample accept label fallback proposals (right e)) then 1 else 0)) =
        seeds.expectation (fun seed => partialLabelScore ν left right R (sample seed)) := by
      simp_rw [← traceSeedLaw_expectation μ n]
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro seed
      simp [partialLabelScore, FiniteDistribution.probability,
        FiniteDistribution.expectation, sample, mul_ite]
    rw [hswitch] at hlower
    have hupper := expectation_mono' seeds (fun seed => hmax (sample seed))
    rw [expectation_const'] at hupper
    exact hlower.trans hupper
  refine ⟨best, ?_⟩
  have hdensity₁ : density ≤ 1 := by
    rw [← hdensity (Classical.choice (inferInstance : Nonempty V))]
    exact μ.probability_le_one _
  by_contra hn
  have hgap : 0 <
      (2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1) -
        partialLabelScore ν left right R best := sub_pos.mpr (lt_of_not_ge hn)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - density)
    (by linarith : 1 - density < 1)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hgap)).exists
  linarith [hbounded n]

end
end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_RoundingThresholdLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! High-value rounding of finite nonnegative vectors. The finite threshold
partition and bounded shared rejection sampler produce an ordinary deterministic
labeling. The auxiliary edge sample may retain hidden constraint information;
the labeling receives only its local vertex. -/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V E A Ω : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype Ω]
  [Nonempty V] [Nonempty A] [Nonempty Ω]

/-- Unit squared row mass converts a large collision energy into a genuinely
local deterministic labeling. All randomness used by the proof is independent
of the sampled constraint, and the final answer has no random seed. -/
theorem exists_labeling_high_value (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v = 1) :
    ∃ labels : V → A,
      1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
        partialLabelScore ν left right R labels := by
  obtain ⟨labels, hlabels⟩ := exists_labeling_ge_partial
    (thresholdDistribution f) ν (thresholdAccept f) (thresholdLabel f a)
    left right R (thresholdRate Ω) thresholdRate_positive
    (threshold_acceptance_mass f hrow)
  rw [threshold_average_good_mass ν left right R a f hrow,
    mul_div_cancel_left₀ _ (ne_of_gt (thresholdRate_positive (Ω := Ω)))] at hlabels
  have hoverlap := pairOverlap_ge_energy ν left right R a f hf hrow
  refine ⟨labels, ?_⟩
  linarith

omit [Nonempty Ω] in
/-- Rows of mass at most one are completed by private vertex coordinates.
Their nonnegative contribution only improves the collision energy. -/
theorem exists_labeling_high_value_of_rows_le_one (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v ≤ 1) :
    ∃ labels : V → A,
      1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
        partialLabelScore ν left right R labels := by
  classical
  let fallback : A := Classical.choice inferInstance
  obtain ⟨labels, hlabels⟩ := exists_labeling_high_value ν left right R
    (paddedLabel a fallback) (paddedAmplitude f)
    (paddedAmplitude_nonnegative f hf) (paddedAmplitude_row f hrow)
  have henergy := pairEnergy_le_padded ν left right R a f hf fallback
  have hsqrt := Real.sqrt_le_sqrt (show
      2 * (1 - pairEnergy ν left right R (paddedLabel a fallback) (paddedAmplitude f)) ≤
        2 * (1 - pairEnergy ν left right R a f) by linarith)
  exact ⟨labels, (by linarith :
    1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
      1 - 2 * Real.sqrt
        (2 * (1 - pairEnergy ν left right R (paddedLabel a fallback)
          (paddedAmplitude f)))).trans hlabels⟩

omit [Nonempty Ω] in
/-- A genuine gap for every deterministic labeling bounds the vector energy
by an alphabet-independent quadratic gap. -/
theorem pairEnergy_le_of_labeling_gap (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v ≤ 1)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ labels : V → A, partialLabelScore ν left right R labels ≤ 1 - g) :
    pairEnergy ν left right R a f ≤ 1 - g ^ 2 / 8 := by
  obtain ⟨labels, hlabels⟩ := exists_labeling_high_value_of_rows_le_one
    ν left right R a f hf hrow
  have hbound := hlabels.trans (hgap labels)
  have he : pairEnergy ν left right R a f ≤ 1 := by
    by_contra h
    have hneg : 2 * (1 - pairEnergy ν left right R a f) ≤ 0 := by linarith
    rw [Real.sqrt_eq_zero_of_nonpos hneg] at hbound
    linarith
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (1 - pairEnergy ν left right R a f) by linarith)
  have hgs : g ≤ 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) := by
    linarith
  have hsq := mul_self_le_mul_self hg.le hgs
  nlinarith

end
end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_RoundingKernel
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The alphabet-independent high-value bound for the actual projection
operator. Positive vectors are determinized, padded, and rounded using proved
finite constructions. No rounding or repetition hypothesis is exposed. -/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

/-- Unit mass form of the Dinur--Steurer positive-vector approximation bound.
The loss is independent of both alphabets and of the auxiliary dimension. -/
theorem vectorEnergy_le_gap_rate [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ 1)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - g) :
    K.vectorEnergy f ≤ 1 - g ^ 2 / 8 := by
  classical
  let : Nonempty Q₂ := distribution_nonempty K.outer
  let : Nonempty Q₁ := distribution_nonempty
    (K.inner (Classical.choice (inferInstance : Nonempty Q₂)))
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · let : IsEmpty Ω := hΩ
    have hzero : K.vectorEnergy f = 0 := by simp [vectorEnergy]
    rw [hzero]
    have hsq : g * g ≤ (1 : ℝ) * 1 := mul_le_mul hg1 hg1 hg0 (by norm_num)
    nlinarith
  · let : Nonempty Ω := hΩ
    obtain ⟨labels, hdet⟩ := K.exists_vectorEnergy_le_singleLabelVector f hf
    have hnonneg := vectorAmplitude_nonnegative f hf
    have hrow : ∀ x, rowSquareMass (vectorAmplitude f) x ≤ 1 := by
      intro x
      rw [rowSquareMass_vectorAmplitude]
      exact hmass x
    rw [K.vectorEnergy_singleLabelVector] at hdet
    by_cases hg : g = 0
    · subst g
      simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
      let fallback : A₁ := Classical.choice inferInstance
      have hpad := pairEnergy_le_padded K.symmetricDistribution symmetricLeft
        symmetricRight K.symmetricAccept labels (vectorAmplitude f) hnonneg fallback
      have hone := pairEnergy_le_one_of_unit_rows K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept
        (paddedLabel labels fallback) (paddedAmplitude (vectorAmplitude f))
        (paddedAmplitude_row (vectorAmplitude f) hrow)
      exact hdet.trans (hpad.trans hone)
    · have hgpos : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hg)
      have hscore (a : Q₁ → A₁) :
          partialLabelScore K.symmetricDistribution symmetricLeft symmetricRight
            K.symmetricAccept a ≤ 1 - g := by
        unfold partialLabelScore
        rw [K.symmetric_probability_eq_assignmentEnergy]
        exact (K.assignmentEnergy_le_collisionValue a).trans
          (K.collisionValue_le_value.trans hvalue)
      exact hdet.trans (pairEnergy_le_of_labeling_gap K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept labels (vectorAmplitude f)
        hnonneg hrow hgpos hscore)

end
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_TensorAlgebraLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Independent repetitions of the actual conditional projection kernel. The
resulting game has precisely the original game's product question law. A
successor tuple is a reindexed independent product, so collision bounds on the
product apply to unrestricted strategies on whole tuples.
-/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

@[simp] theorem toGame_repetition (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    (K.repetition n).toGame = K.toGame.repetition n := by
  classical
  have hq : (K.repetition n).toGame.questions = (K.toGame.repetition n).questions := by
    apply FiniteDistribution.eq_of_weight_eq
    intro q
    change ((∏ i, K.outer.weight (q.2 i)) *
        (∏ i, (K.inner (q.2 i)).weight (q.1 i))) =
      ∏ i, K.outer.weight (q.2 i) * (K.inner (q.2 i)).weight (q.1 i)
    exact Finset.prod_mul_distrib.symm
  change Game.mk (K.repetition n).toGame.questions
      (fun (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) =>
        decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true)) =
    Game.mk (K.toGame.repetition n).questions
      (fun (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) =>
        decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true))
  rw [hq]

theorem eq_of_data_eq {K H : ProjectionKernel Q₁ Q₂ A₁ A₂}
    (houter : K.outer = H.outer) (hinner : K.inner = H.inner)
    (haccepts : K.accepts = H.accepts) : K = H := by
  cases K
  cases H
  cases houter
  cases hinner
  cases haccepts
  rfl

/-- Separate the first coordinate without restricting answer dependence on
any coordinate of the complete local question tuple. -/
theorem repetition_succ (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    K.repetition (n + 1) =
      (K.product (K.repetition n)).reindex
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₂))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₂)) := by
  classical
  apply eq_of_data_eq
  · apply FiniteDistribution.eq_of_weight_eq
    intro y
    change (∏ i : Fin (n + 1), K.outer.weight (y i)) =
      K.outer.weight (y 0) * ∏ i : Fin n, K.outer.weight (y i.succ)
    exact Fin.prod_univ_succ _
  · funext y
    apply FiniteDistribution.eq_of_weight_eq
    intro x
    change (∏ i : Fin (n + 1), (K.inner (y i)).weight (x i)) =
      (K.inner (y 0)).weight (x 0) *
        ∏ i : Fin n, (K.inner (y i.succ)).weight (x i.succ)
    exact Fin.prod_univ_succ _
  · funext x y a b
    apply Bool.eq_iff_iff.mpr
    change (decide (∀ i : Fin (n + 1), K.accepts (x i) (y i) (a i) (b i) = true) = true) ↔
      (K.accepts (x 0) (y 0) (a 0) (b 0) &&
        decide (∀ i : Fin n, K.accepts (x i.succ) (y i.succ) (a i.succ) (b i.succ) = true)) = true
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩
    · rintro ⟨hzero, hsucc⟩ i
      exact Fin.cases hzero hsucc i

theorem collisionValue_repetition_succ [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    (K.repetition (n + 1)).collisionValue =
      (K.product (K.repetition n)).collisionValue := by
  rw [repetition_succ, collisionValue_reindex]

theorem collisionValue_repetition_zero_le_one [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    (K.repetition 0).collisionValue ≤ 1 :=
  (K.repetition 0).collisionValue_le_one

end
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

section

/-!
The tensor-domination reduction before the Dinur--Steurer rounding theorem.
Every deterministic strategy for the product gives a nonnegative vector table
for the first kernel. Its energy is exactly the product collision energy, and
each input-question mass is bounded by the second kernel's collision value.
-/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

/-- Apply the second game to a fixed first question and first answer. The
square-root factor changes its weighted output space into counting measure. -/
def tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁))
    (ω : R₂ × B₂) (x : Q₁) (a : A₁) : ℝ :=
  Real.sqrt (H.outer.weight ω.1) *
    H.apply (fun u d => assignment labels (x,u) (a,d)) ω.1 ω.2

omit [Fintype Q₁] [Fintype A₁] in
theorem tensorSlice_nonnegative (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) (a : A₁) :
    0 ≤ H.tensorSlice labels ω x a := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply H.apply_nonnegative
  intro u d
  unfold assignment
  split
  · exact zero_le_one
  · exact le_rfl

omit [Fintype Q₁] in
theorem tensorSlice_label_mass (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) :
    (∑ a, H.tensorSlice labels ω x a) =
      Real.sqrt (H.outer.weight ω.1) *
        H.apply (assignment (fun r => (labels (x,r)).2)) ω.1 ω.2 := by
  unfold tensorSlice
  rw [← Finset.mul_sum, ← apply_sum]
  simp_rw [sum_assignment_product]

omit [Fintype Q₁] in
/-- The fiber mass is an actual collision energy of the second game, not a
free normalization assumption. -/
theorem vectorMass_tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x =
      H.assignmentEnergy (fun r => (labels (x,r)).2) := by
  classical
  unfold vectorMass assignmentEnergy energy
  simp_rw [tensorSlice_label_mass, mul_pow]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Real.sq_sqrt (H.outer.nonnegative y), Finset.mul_sum]

omit [Fintype Q₁] in
theorem vectorMass_tensorSlice_le [Nonempty B₁]
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x ≤ H.collisionValue := by
  rw [vectorMass_tensorSlice]
  exact H.assignmentEnergy_le_collisionValue _

/-- Exact Hilbert-norm factorization, with every marginal weight retained. -/
theorem vectorEnergy_tensorSlice (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) :
    K.vectorEnergy (H.tensorSlice labels) = (K.product H).assignmentEnergy labels := by
  classical
  let p := fun y z b c =>
    K.apply (fun x a => H.apply (fun u d => assignment labels (x,u) (a,d)) z c) y b ^ 2
  have hlhs : K.vectorEnergy (H.tensorSlice labels) =
      ∑ z, ∑ c, ∑ y, ∑ b, K.outer.weight y * H.outer.weight z * p y z b c := by
    simp only [vectorEnergy, energy, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change K.outer.weight y *
      (K.apply (fun x a => Real.sqrt (H.outer.weight z) *
        H.apply (fun u d => assignment labels (x,u) (a,d)) z c) y b) ^ 2 = _
    rw [apply_smul, mul_pow, Real.sq_sqrt (H.outer.nonnegative z)]
    exact (mul_assoc _ _ _).symm
  have hrhs : (K.product H).assignmentEnergy labels =
      ∑ y, ∑ z, ∑ b, ∑ c, K.outer.weight y * H.outer.weight z * p y z b c := by
    simp only [assignmentEnergy, energy, product, FiniteDistribution.product,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    exact congrArg (fun r : ℝ => r ^ 2)
      (apply_product K H (assignment labels) y z b c)
  rw [hlhs, hrhs]
  calc
    (∑ z, ∑ c, ∑ y, ∑ b, K.outer.weight y * H.outer.weight z * p y z b c) =
        ∑ z, ∑ y, ∑ b, ∑ c, K.outer.weight y * H.outer.weight z * p y z b c := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

end ProjectionKernel
end
end UniqueGamesTheorem.Repetition

end

section

/-! Homogeneous normalization for finite nonnegative vector assignments. -/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel
open scoped BigOperators
noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

theorem energy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) :
    K.energy (fun x a => r * f x a) = r ^ 2 * K.energy f := by
  unfold energy
  simp_rw [apply_smul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro b _
  exact mul_left_comm _ _ _

theorem vectorEnergy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (r : ℝ) :
    K.vectorEnergy (fun ω x a => r * f ω x a) = r ^ 2 * K.vectorEnergy f := by
  unfold vectorEnergy
  simp_rw [energy_smul]
  exact (Finset.mul_sum _ _ _).symm

theorem vectorEnergy_eq_zero_of_mass_nonpositive
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (hf : ∀ ω x a, 0 ≤ f ω x a)
    (hmass : ∀ x, vectorMass f x ≤ 0) : K.vectorEnergy f = 0 := by
  have hfzero : f = fun _ _ _ => 0 := by
    funext ω x a
    exact entry_eq_zero_of_vectorMass_nonpositive f hf hmass ω x a
  rw [hfzero]
  simp [vectorEnergy, energy, apply]

/-- A unit-mass estimate extends to any nonnegative mass bound, including
zero. The hypothesis is precisely the unit-mass analytic estimate being
normalized; the normalization itself assumes no repetition bound. -/
theorem vectorEnergy_le_of_unit_bound
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (ρ C : ℝ)
    (unit_bound : ∀ f : Ω → Q₁ → A₁ → ℝ,
      (∀ ω x a, 0 ≤ f ω x a) → (∀ x, vectorMass f x ≤ 1) → K.vectorEnergy f ≤ ρ)
    (hC : 0 ≤ C) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ C) :
    K.vectorEnergy f ≤ ρ * C := by
  rcases eq_or_lt_of_le hC with hzero | hpositive
  · have hCzero : C = 0 := hzero.symm
    subst C
    rw [K.vectorEnergy_eq_zero_of_mass_nonpositive f hf hmass, mul_zero]
  · have hsqrt : 0 ≤ (Real.sqrt C)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg C)
    have hscale : ((Real.sqrt C)⁻¹) ^ 2 = C⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hC]
    have hnorm : ∀ x, vectorMass (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a) x ≤ 1 := by
      intro x
      rw [vectorMass_smul, hscale]
      have h := mul_le_mul_of_nonneg_left (hmass x) (inv_nonneg.mpr hC)
      simpa [ne_of_gt hpositive] using h
    have hbound := unit_bound (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a)
      (fun ω x a => mul_nonneg hsqrt (hf ω x a)) hnorm
    rw [vectorEnergy_smul, hscale] at hbound
    have h := mul_le_mul_of_nonneg_left hbound hC
    simpa [← mul_assoc, ne_of_gt hpositive, mul_comm C ρ] using h

end
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

section

/-!
Alphabet-independent repetition of ordinary finite projection games.

The game is the actual finite question distribution and its local acceptance
predicate. The proof bounds nonnegative vector assignments by finite
thresholding and correlated sampling, factors each unrestricted product
strategy through that bound, and iterates the resulting collision contraction.
No repetition bound, decoder certificate, or alphabet-size budget is a premise.

The deterministic-predicate game interface permits arbitrary real question
weights. Distinct hidden constraints on the same question pair are not encoded
by this interface. Both v2 uses have a unique predicate for each question pair:
the distinct-position equation--variable game and the final simple graph.
-/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
noncomputable section

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
  [Nonempty A₁] [Nonempty A₂] [Nonempty B₁] [Nonempty B₂]

omit [Nonempty B₂] in
theorem collisionValue_product_le_gap_rate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) :
    (K.product H).collisionValue ≤ (1 - gap ^ 2 / 8) * H.collisionValue := by
  apply ((K.product H).collisionValue_le_iff _).2
  intro labels
  rw [← vectorEnergy_tensorSlice]
  apply K.vectorEnergy_le_of_unit_bound (1 - gap ^ 2 / 8) H.collisionValue
    (fun f hf hmass => K.vectorEnergy_le_gap_rate f hf hmass hgap₀ hgap₁ hvalue)
    H.collisionValue_nonneg (H.tensorSlice labels)
    (H.tensorSlice_nonnegative labels) (H.vectorMass_tensorSlice_le labels)

theorem repetition_value_le_dsRate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) (n : ℕ) :
    (K.toGame.repetition n).value ≤ dsRate gap ^ n := by
  have hstep : ∀ m, (K.repetition (m + 1)).collisionValue ≤
      (1 - gap ^ 2 / 8) * (K.repetition m).collisionValue := by
    intro m
    rw [K.collisionValue_repetition_succ]
    exact K.collisionValue_product_le_gap_rate (K.repetition m) hgap₀ hgap₁ hvalue
  have h := rate_of_squared_collision_recurrence hgap₀ hgap₁
    (fun m => (K.repetition m).collisionValue)
    (fun m => (K.repetition m).toGame.value)
    K.collisionValue_repetition_zero_le_one hstep
    (fun m => (K.repetition m).value_sq_le_collisionValue) n
  simpa only [toGame_repetition] using h

end ProjectionKernel

end
end UniqueGamesTheorem.Repetition

end

end OAI
end


