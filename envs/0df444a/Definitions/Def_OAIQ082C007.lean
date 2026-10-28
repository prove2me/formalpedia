-- Prove2me | Definitions.Def_OAIQ082C007
-- name    : OAIQ082C007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:27:35.7551+00:00
-- url     : https://prove2.me/theorems/eea4b71f-bb1a-4e25-be12-5435123233c9
-- title:
--   Definitions bundle OAIQ082C007 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 545 declarations of OpenAI's Lean: 214 definitions, 10 inductive types or structures, 10 instances and 311 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.wireValues`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution.stackCapacity`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.payloadLabels`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.prefixLabels`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.Circuit.restrictAssignment`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch.Frame.network`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.ContextListLinked`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.contextListOutput`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.contextListStart`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.contextListSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.contextOutput`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.contextTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.contextWords`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.gateContexts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.gateSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.outputContexts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.finalTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.initialTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer.asInput`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders.parsedTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders.resultTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop.bodyCost`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop.decodedFields`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop.loopCost`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop.parsedFields`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop.recordsInput`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop.recordsOutput`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop.tapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.Record.fieldValue`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.Record.outputBits`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.Record.outputWords`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.Record.slot`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.affineEmit`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.emission`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.headerTape`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.literalEmit`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime.Input`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime.afterLoopTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime.beforeFinishTapes` and 184 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_BinaryOrderMachine`, `BinPacking_Arithmetic_BinaryPowerMachine`, `BinPacking_Arithmetic_BinaryTallyMachine`, `BinPacking_Arithmetic_GraphTallyMachine`, `BinPacking_Arithmetic_NatExpressionBranch`, `BinPacking_Computation_MachineCanonicalOutput`, `BinPacking_Computation_MachineHorner`, `BinPacking_Computation_PoweringGlobalEnumeration`, `BinPacking_Computation_PoweringMachineRowBody`, `BinPacking_CookLevin_BoundedExecution`, `BinPacking_CookLevin_CellsTokensAlignment`, `BinPacking_CookLevin_CircuitEncodingBridge`, `BinPacking_CookLevin_CircuitFinish`, `BinPacking_CookLevin_CircuitProducer`, `BinPacking_CookLevin_ClashMachine`, `BinPacking_CookLevin_ConfigIndex`, `BinPacking_CookLevin_ForestStage`, `BinPacking_CookLevin_InitializationMachineAt`, `BinPacking_CookLevin_MachineCircuit`, `BinPacking_CookLevin_OutputOrder`, `BinPacking_CookLevin_PaddingCellsMachine`, `BinPacking_CookLevin_PayloadPresenceMachine`, `BinPacking_CookLevin_PolynomialMachine`, `BinPacking_CookLevin_PostfixBounds`, `BinPacking_CookLevin_ProducerFrontStage`, `BinPacking_CookLevin_TransitionArena`, `BinPacking_CookLevin_TransitionIterationTime`, `BinPacking_CookLevin_ValidityComposition`, `BinPacking_CookLevin_ValidityMachine`, `BinPacking_CookLevin_VerifierCircuit`, `BinPacking_CookLevin_VerifierFront`, `BinPacking_Expanders_ExpanderTableEnumeration`, `BinPacking_Expanders_SpectralCut`, `BinPacking_Expanders_ZigzagSpectral`, `BinPacking_Information_GameDecoder`, `BinPacking_PCP_AlphabetRetraction`, `BinPacking_PCP_BinaryFormula`, `BinPacking_PCP_CloudRounding`, `BinPacking_PCP_FinalBooleanVerifier`, `BinPacking_PCP_FinalConstants`, `BinPacking_PCP_FiniteGraph`, `BinPacking_PCP_PCPIteration`, `BinPacking_PCP_Queries`, `BinPacking_PCP_RawInitialMachineBudget`, `BinPacking_Packing_PhaseIteration`, `BinPacking_Reductions_MachineTransducer`, `BinPacking_Search_ApproximationImpliesP`, `BinPacking_Search_ExtensionCapacityBounds`, `BinPacking_Trees_TreeAvoidance`, `BinPacking_Trees_TreeColorCounts`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C000`, `OAIQ082C001`, `OAIQ082C002` and `OAIQ082C003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C012`, `OAIQ082C013`, `OAIQ082C014` and `OAIQ082C015`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C000
import Definitions.Def_OAIQ082C001
import Definitions.Def_OAIQ082C002
import Definitions.Def_OAIQ082C003

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_BinaryFormula
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP

open Target

def honestAnswer {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : ClauseAnswer :=
  ⟨assignment clause[0].variableIndex, assignment clause[1].variableIndex,
   assignment clause[2].variableIndex⟩

def matchingSlots (a b : ClauseAnswer) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

def acceptedSlots {n : Nat} (clause : Clause n) (alice bob : ClauseAnswer) : Nat :=
  if localSatisfies clause alice then matchingSlots alice bob else 0

def clauseFailure {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Nat :=
  if clause.eval assignment then 0 else 1

abbrev AliceStrategy (formula : Formula) := Fin formula.clauses.length → ClauseAnswer
abbrev BobStrategy (formula : Formula) := Fin formula.variables → Bool

def acceptedCount (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) : List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => acceptedSlots (clauseAt formula i) (alice i)
      (honestAnswer (clauseAt formula i) bob) + acceptedCount formula alice bob rest

def failureCount (formula : Formula) (bob : BobStrategy formula) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => clauseFailure (clauseAt formula i) bob + failureCount formula bob rest

end BinPackingGames.Foundations.PCP

namespace BinPackingGames.Foundations.PCP.NameCompaction

open BinPackingGames.Foundations.Target

def evaluationList (F : Formula) (A : Fin F.variables → Bool) : List Bool :=
  F.clauses.map (fun c => c.eval A)

def failedCount (F : Formula) (A : Fin F.variables → Bool) : Nat :=
  (evaluationList F A).count false

end BinPackingGames.Foundations.PCP.NameCompaction

namespace BinPackingGames.Foundations.PCP.VerifierToCNF

open Target

def eventValue {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) : Bool := V.accepts e (fun i => A (V.query e i))

def rejectedEventCount {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool) : Nat :=
  ((List.finRange V.events).map (eventValue V A)).count false

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun c => c.eval A)).count false

end BinPackingGames.Foundations.PCP.VerifierToCNF

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_CloudRounding
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

end BinPackingGames.Foundations.PCP.PoweringWalks

namespace BinPackingGames.Foundations.PCP

namespace ConstraintGraph

variable {V E A : Type*}

def Satisfiable (G : ConstraintGraph V E A) : Prop :=
  ∃ labeling : V → A, ∀ e, G.edgeSatisfied labeling e = true

end ConstraintGraph

end BinPackingGames.Foundations.PCP

namespace BinPackingGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

instance finitePortWords [Finite D] (t : Nat) : Finite (PortWords D t) := by
  let := Fintype.ofFinite D
  exact Finite.of_fintype _

end BinPackingGames.Foundations.PCP.PoweringLabels

namespace BinPackingGames.Foundations.PCP.CloudRounding

open scoped BigOperators

section CloudCounts

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

def minorityEquiv (ell : X → A) (m : A) :
    (Σ a : Nonmajor m, ↥(colorSet ell a.val)) ≃ ↥(minoritySet ell m) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val = t.1.val := (Finset.mem_filter.mp t.2.property).2
    have hn : ell t.2.val ≠ m := fun h => t.1.property (hc.symm.trans h)
    simpa [minoritySet] using hn⟩
  invFun x :=
    ⟨⟨ell x.val, by simpa [minoritySet] using x.property⟩,
      ⟨x.val, by simp [colorSet]⟩⟩
  left_inv t := by
    rcases t with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    have hxa : ell x = a := by simpa [colorSet] using hx
    cases hxa
    rfl
  right_inv x := by apply Subtype.ext; rfl

def minorityCutEmbedding (ell : X → A) (next : X × D → X) (m : A) :
    (Σ a : Nonmajor m, ↥(directedCut next (colorSet ell a.val))) ↪
      ↥(disagreementSet ell next) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val.1 = t.1.val ∧ ell (next t.2.val) ≠ t.1.val := by
      simpa [directedCut, colorSet] using t.2.property
    have hn : ell t.2.val.1 ≠ ell (next t.2.val) :=
      fun h => hc.2 (h.symm.trans hc.1)
    simpa [disagreementSet] using hn⟩
  inj' p q h := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    rcases q with ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
    have hxy : x = y := congrArg Subtype.val h
    cases hxy
    have hxa : ell x.1 = a := by
      have hc : ell x.1 = a ∧ ell (next x) ≠ a := by
        simpa [directedCut, colorSet] using hx
      exact hc.1
    have hxb : ell x.1 = b := by
      have hc : ell x.1 = b ∧ ell (next x) ≠ b := by
        simpa [directedCut, colorSet] using hy
      exact hc.1
    have hab : a = b := hxa.symm.trans hxb
    cases hab
    rfl

end CloudCounts

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

def mismatchSet (G : ConstraintGraph V E A) (ell : E → A) (rounded : V → A) :
    Finset E :=
  Finset.univ.filter (fun e => ell e ≠ rounded (G.tail e))

def copiedRejectionCount (G : ConstraintGraph V E A) (ell : E → A) : Nat :=
  (Finset.univ.filter (fun e => G.accepts e (ell e) (ell (G.reverse e)) = false)).card

def innerDisagreementSet (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) : Finset (E × D) :=
  Finset.univ.filter (fun ed => ell ed.1 ≠ ell (innerRotation G H ed).1)

noncomputable def roundLabels [Nonempty A]
    (G : ConstraintGraph V E A) (ell : E → A) : V → A :=
  fun v => majority (fun e : Cloud G v => ell e.val)

def mismatchFiberEquiv (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (Σ v, ↥(minoritySet (fun e : Cloud G v => ell e.val) (rounded v))) ≃
      ↥(mismatchSet G ell rounded) where
  toFun := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    exact ⟨e, by simpa [mismatchSet, minoritySet] using hbad⟩
  invFun e :=
    ⟨G.tail e.val, ⟨⟨e.val, rfl⟩, by
      simpa [mismatchSet, minoritySet] using e.property⟩⟩
  left_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro e; apply Subtype.ext; rfl

def disagreementFiberEquiv (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (Σ v, ↥(disagreementSet (fun e : Cloud G v => ell e.val)
      (fun ed => ((H v).rot ed).1))) ≃ ↥(innerDisagreementSet G H ell) where
  toFun := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    refine ⟨(e, d), ?_⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  invFun := by
    rintro ⟨⟨e, d⟩, hbad⟩
    refine ⟨G.tail e, ⟨(⟨e, rfl⟩, d), ?_⟩⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  left_inv := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro ed; apply Subtype.ext; rfl

end GraphRounding

end BinPackingGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_AlphabetRetraction
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

def response (T : Verifier E X q) (assignment : X → Bool) (event : E) : Label q :=
  fun i => assignment (T.query event i)

def honestLabeling (T : Verifier E X q) (assignment : X → Bool) : Vertex E X → Label q
  | .inl event => response T assignment event
  | .inr address => encodeRight (assignment address)

def decodedAssignment (positive : 0 < q) (labeling : Vertex E X → Label q) : X → Bool :=
  fun address => decodeRight positive (labeling (.inr address))

def rejectedEvents [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Finset E :=
  Finset.univ.filter (fun event => T.accepts event (response T assignment event) = false)

def verifierRejectionCount [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Nat :=
  (rejectedEvents T assignment).card

end BinPackingGames.Foundations.PCP.QueryIncidence

namespace BinPackingGames.Foundations.PCP.InitialGraph

open Target

instance vertexNonempty (F : Formula) : Nonempty (Vertex F) := ⟨dummyVertex F⟩
def variableLabel (value : Bool) : Label := (value, false, false)

def honestLabeling (F : Formula) (A : Fin F.variables → Bool) : Vertex F → Label
  | .inl (.inl v) => variableLabel (A v)
  | .inl (.inr i) => fromClauseAnswer (honestAnswer (clauseAt F i) A)
  | .inr _ => variableLabel false

end BinPackingGames.Foundations.PCP.InitialGraph

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_FiniteGraph
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

def rejectionCounts (G : ConstraintGraph V E A) : Finset Nat := by
  classical
  exact Finset.univ.image G.rejectionCount

theorem rejectionCounts_nonempty (G : ConstraintGraph V E A) :
    G.rejectionCounts.Nonempty := by
  classical
  exact Finset.univ_nonempty.image G.rejectionCount

def minimumRejections (G : ConstraintGraph V E A) : Nat :=
  G.rejectionCounts.min' G.rejectionCounts_nonempty

def gap (G : ConstraintGraph V E A) : ℝ :=
  (G.minimumRejections : ℝ) / Fintype.card E

end Minimum

end BinPackingGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.GenericGraphTables

open BinPackingGames.Foundations.Complexity

variable {q : Nat}

instance instDecidableValid {n m : Nat} (rows : Rows q n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

end BinPackingGames.Foundations.PCP.GenericGraphTables

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryOrderMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryOrderMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinPackingCompleteness.BinaryEncoding (bitsValue bitsValue_bits)

theorem scanOrder_value (left right : List Bool) (prior : Ordering) :
    scanOrder left right prior = orderNat (bitsValue left) (bitsValue right) prior := by
  induction left generalizing right prior with
  | nil =>
    induction right generalizing prior with
    | nil => simp [scanOrder, bitsValue, orderNat]
    | cons head tail ih =>
      rw [scanOrder, ih]
      simpa only [bitsValue, Nat.bit_false, Nat.mul_zero] using
        orderNat_bit 0 (bitsValue tail) false head prior
  | cons head tail ih =>
    cases right with
    | nil =>
      rw [scanOrder, ih]
      simpa only [bitsValue, Nat.bit_false, Nat.mul_zero] using
        orderNat_bit (bitsValue tail) 0 head false prior
    | cons rightHead rightTail =>
      rw [scanOrder, ih]
      exact orderNat_bit (bitsValue tail) (bitsValue rightTail) head rightHead prior

@[simp] theorem scanOrder_bits (a b : Nat) (prior : Ordering) :
    scanOrder a.bits b.bits prior = orderNat a b prior := by
  rw [scanOrder_value, bitsValue_bits, bitsValue_bits]

@[simp] theorem orderNat_eq_lt (a b : Nat) : orderNat a b .eq = .lt ↔ a < b := by
  unfold orderNat
  split_ifs <;> simp_all

@[simp] theorem orderNat_eq_gt (a b : Nat) : orderNat a b .eq = .gt ↔ b < a := by
  unfold orderNat
  split_ifs <;> simp_all
  omega

@[simp] theorem orderNat_eq_eq (a b : Nat) : orderNat a b .eq = .eq ↔ a = b := by
  unfold orderNat
  split_ifs <;> simp_all <;> omega

section Program

variable {K Λ σ : Type} [DecidableEq K]

theorem update_left (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k; simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

theorem update_right (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (ambient : σ) (prior : Ordering)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨exits prior, clean ambient, tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  cases prior <;>
    simp [loop, TM2.stepAux, distinct, update_left, update_right, clean]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ)
    (prior : Ordering) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some again, (((ambient, updateOrder prior false head), none), none),
        tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ)
    (prior : Ordering) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some again, (((ambient, updateOrder prior head false), none), none),
        tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (prior : Ordering) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some again, (((ambient, updateOrder prior leftHead rightHead), none), none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem trace_left_empty (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (prior : Ordering)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨exits (scanOrder [] rightWord prior), clean ambient,
        tapesAt left right base [] []⟩ := by
  induction rightWord generalizing prior leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, scanOrder] using
      step_empty left right distinct again exits program atLoop base ambient prior
        leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct again exits program atLoop]
    simpa only [scanOrder] using ih (updateOrder prior false head) none none

theorem compareTrace_prior (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (prior : Ordering) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some again, (((ambient, prior), leftRegister), rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨exits (scanOrder leftWord rightWord prior), clean ambient,
        tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord prior leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty left right distinct again exits program atLoop base rightWord
        ambient prior leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some again, (((ambient, prior), leftRegister), rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct again exits program atLoop]
      simpa only [List.length_nil, Nat.max_zero, scanOrder] using
        ih [] (updateOrder prior head false) none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some again, (((ambient, prior), leftRegister), rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct again exits program atLoop]
      simpa only [scanOrder] using
        ih rightTail (updateOrder prior head rightHead) none none

theorem compareTrace (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some again, clean ambient, tapesAt left right base leftWord rightWord⟩) =
      some ⟨exits (orderNat (bitsValue leftWord) (bitsValue rightWord) .eq),
        clean ambient, tapesAt left right base [] []⟩ := by
  simpa only [clean, scanOrder_value] using
    compareTrace_prior left right distinct again exits program atLoop base leftWord rightWord
      ambient .eq none none

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (again : Λ) (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program again = loop left right again exits)
    (base : K → List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some again, clean ambient, base⟩) =
      some ⟨exits (orderNat (bitsValue (base left)) (bitsValue (base right)) .eq),
        clean ambient, tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct again exits program atLoop base (base left) (base right) ambient

end Program

end BinPackingGap.BinaryOrderMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryTallyMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryArithmetic

abbrev bitValue := BinPackingCompleteness.BinaryEncoding.bitsValue

@[simp] theorem bitValue_nil : bitValue [] = 0 := rfl

@[simp] theorem bitValue_cons (b : Bool) (bs : List Bool) :
    bitValue (b :: bs) = Nat.bit b (bitValue bs) := rfl

@[simp] theorem bitValue_bits (n : Nat) : bitValue n.bits = n :=
  BinPackingCompleteness.BinaryEncoding.bitsValue_bits n

theorem bitValue_eq_zero_iff {bs : List Bool} (h : Canonical bs) :
    bitValue bs = 0 ↔ bs = [] := by
  revert h
  induction bs with
  | nil => intro h; simp
  | cons b bs ih =>
      intro h
      constructor
      · intro hz
        have htail : bitValue bs = 0 := by
          cases b <;> simp [Nat.bit] at hz
          omega
        have hnil := (ih h.1).mp htail
        have hb := h.2 hnil
        simp [hnil, hb, Nat.bit] at hz
      · intro hn
        cases hn

theorem canonical_bits (n : Nat) : Canonical n.bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [Canonical]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      refine ⟨ih, ?_⟩
      intro hnil
      apply hn
      have h := congrArg bitValue hnil
      simpa using h

theorem bits_bitValue {bs : List Bool} (h : Canonical bs) :
    (bitValue bs).bits = bs := by
  revert h
  induction bs with
  | nil => intro h; simp
  | cons b bs ih =>
      intro h
      have hn : bitValue bs = 0 → b = true :=
        fun hz => h.2 ((bitValue_eq_zero_iff h.1).mp hz)
      rw [bitValue_cons, Nat.bits_append_bit _ _ hn, ih h.1]

theorem bitValue_addCarry (xs ys : List Bool) (c : Bool) :
    bitValue (addCarry xs ys c) =
      bitValue xs + bitValue ys + (if c then 1 else 0) := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [addCarry, Nat.bit]
      | cons b bs ih =>
          cases b <;> cases c <;>
            simp [addCarry, sumBit, carryBit, Nat.bit, ih]
          omega
  | cons a as ih =>
      cases ys with
      | nil =>
          cases a <;> cases c <;>
            simp [addCarry, sumBit, carryBit, Nat.bit, ih]
          omega
      | cons b bs =>
          cases a <;> cases b <;> cases c <;>
            simp [addCarry, sumBit, carryBit, Nat.bit, ih] <;> omega

@[simp] theorem addCarry_eq_nil (xs ys : List Bool) (c : Bool) :
    addCarry xs ys c = [] ↔ xs = [] ∧ ys = [] ∧ c = false := by
  cases xs <;> cases ys <;> cases c <;> simp [addCarry]

theorem canonical_addCarry {xs ys : List Bool} (hx : Canonical xs)
    (hy : Canonical ys) (c : Bool) : Canonical (addCarry xs ys c) := by
  revert hx hy
  induction xs generalizing ys c with
  | nil =>
      intro hx hy
      revert hy
      induction ys generalizing c with
      | nil => intro hy; cases c <;> simp [addCarry, Canonical]
      | cons b bs ih =>
          intro hy
          simp only [addCarry, Canonical]
          refine ⟨ih (c := carryBit false b c) hy.1, ?_⟩
          intro hn
          obtain ⟨_, hbs, hc⟩ := (addCarry_eq_nil _ _ _).mp hn
          have hb := hy.2 hbs
          cases b <;> cases c <;> simp_all [sumBit, carryBit]
  | cons a as ih =>
      intro hx hy
      cases ys with
      | nil =>
          simp only [addCarry, Canonical]
          refine ⟨ih (ys := []) (c := carryBit a false c) hx.1 hy, ?_⟩
          intro hn
          obtain ⟨has, _, hc⟩ := (addCarry_eq_nil _ _ _).mp hn
          have ha := hx.2 has
          cases a <;> cases c <;> simp_all [sumBit, carryBit]
      | cons b bs =>
          simp only [addCarry, Canonical]
          refine ⟨ih (ys := bs) (c := carryBit a b c) hx.1 hy.1, ?_⟩
          intro hn
          obtain ⟨has, hbs, hc⟩ := (addCarry_eq_nil _ _ _).mp hn
          have ha := hx.2 has
          have hb := hy.2 hbs
          cases a <;> cases b <;> cases c <;> simp_all [carryBit]

theorem addCarry_bits (a b : Nat) :
    addCarry a.bits b.bits false = (a + b).bits := by
  have h := bits_bitValue (canonical_addCarry (canonical_bits a) (canonical_bits b) false)
  simpa [bitValue_addCarry] using h.symm

theorem addCarry_length (xs ys : List Bool) (c : Bool) :
    (addCarry xs ys c).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [addCarry]
      | cons b bs ih =>
          have ht := ih (carryBit false b c)
          simp only [addCarry, List.length_cons, List.length_nil] at ht ⊢
          omega
  | cons a as ih =>
      cases ys with
      | nil =>
          have ht := ih [] (carryBit a false c)
          simp only [addCarry, List.length_cons, List.length_nil] at ht ⊢
          omega
      | cons b bs =>
          have ht := ih bs (carryBit a b c)
          simp only [addCarry, List.length_cons] at ht ⊢
          omega

theorem size_add_le (a b : Nat) :
    (a + b).size ≤ max a.size b.size + 1 := by
  have h := addCarry_length a.bits b.bits false
  simpa [addCarry_bits, Nat.size_eq_bits_len] using h

theorem size_pow_le (a t : Nat) : (a ^ t).size ≤ t * a.size + 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.pow_succ]
      calc
        (a ^ t * a).size ≤ (a ^ t).size + a.size := size_mul_le _ _
        _ ≤ (t * a.size + 1) + a.size := Nat.add_le_add_right ih _
        _ = (t + 1) * a.size + 1 := by
          simp only [Nat.add_mul, Nat.one_mul]
          omega

@[simp] theorem bitValue_shift (xs : List Bool) :
    bitValue (shift xs) = 2 * bitValue xs := by
  cases xs <;> simp [shift, Nat.bit]

theorem canonical_shift {xs : List Bool} (hx : Canonical xs) :
    Canonical (shift xs) := by
  cases xs with
  | nil => simp [shift, Canonical]
  | cons b bs => simpa [shift, Canonical] using hx

theorem shift_length_le (xs : List Bool) : (shift xs).length ≤ xs.length + 1 := by
  cases xs <;> simp [shift]

def mulAcc (xs : List Bool) : List Bool → List Bool → List Bool
  | [], acc => acc
  | b :: ys, acc =>
      mulAcc (shift xs) ys (if b then addCarry xs acc false else acc)

theorem bitValue_mulAcc (xs ys acc : List Bool) :
    bitValue (mulAcc xs ys acc) = bitValue xs * bitValue ys + bitValue acc := by
  induction ys generalizing xs acc with
  | nil => simp [mulAcc]
  | cons b ys ih =>
      cases b <;> simp [mulAcc, ih, bitValue_addCarry, Nat.bit] <;> ring

theorem canonical_mulAcc {xs ys acc : List Bool} (hx : Canonical xs)
    (ha : Canonical acc) : Canonical (mulAcc xs ys acc) := by
  revert hx ha
  induction ys generalizing xs acc with
  | nil => intro hx ha; exact ha
  | cons b ys ih =>
      intro hx ha
      simp only [mulAcc]
      apply ih (canonical_shift hx)
      cases b
      · exact ha
      · exact canonical_addCarry hx ha false

theorem mulAcc_bits (a b : Nat) : mulAcc a.bits b.bits [] = (a * b).bits := by
  have h := bits_bitValue (canonical_mulAcc (ys := b.bits) (canonical_bits a)
    (show Canonical [] from trivial))
  simpa [bitValue_mulAcc] using h.symm

@[simp] theorem bitValue_consBit (b : Bool) (bs : List Bool) :
    bitValue (consBit b bs) = Nat.bit b (bitValue bs) := by
  cases b <;> cases bs <;> rfl

theorem canonical_consBit (b : Bool) {bs : List Bool} (h : Canonical bs) :
    Canonical (consBit b bs) := by
  cases bs with
  | nil => cases b <;> simp [consBit, Canonical]
  | cons a as => cases b <;> exact ⟨h, by simp⟩

def trim : List Bool → List Bool
  | [] => []
  | b :: bs => consBit b (trim bs)

@[simp] theorem bitValue_trim (bs : List Bool) : bitValue (trim bs) = bitValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [trim, ih]

theorem canonical_trim (bs : List Bool) : Canonical (trim bs) := by
  induction bs with
  | nil => trivial
  | cons b bs ih => exact canonical_consBit b ih

theorem trimHigh_append (xs ys : List Bool) :
    trimHigh (xs ++ ys) =
      if trimHigh xs = [] then trimHigh ys else trimHigh xs ++ ys := by
  induction xs with
  | nil => simp [trimHigh]
  | cons b xs ih =>
      cases b with
      | false =>
          change trimHigh (xs ++ ys) =
            if trimHigh xs = [] then trimHigh ys else trimHigh xs ++ ys
          exact ih
      | true => simp [trimHigh]

theorem trimHigh_reverse (bs : List Bool) :
    trimHigh bs.reverse = (trim bs).reverse := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.reverse_cons, trimHigh_append, ih]
      cases ht : trim bs with
      | nil => cases b <;> simp [trim, ht, consBit, trimHigh]
      | cons d ds => cases b <;> simp [trim, ht, consBit, List.reverse_cons]

def subBorrow : List Bool → List Bool → Bool → Option (List Bool)
  | [], [], c => if c then none else some []
  | a :: as, [], c =>
      (subBorrow as [] (borrowBit a false c)).map (fun bs => diffBit a false c :: bs)
  | [], b :: bs, c =>
      (subBorrow [] bs (borrowBit false b c)).map (fun ds => diffBit false b c :: ds)
  | a :: as, b :: bs, c =>
      (subBorrow as bs (borrowBit a b c)).map (fun ds => diffBit a b c :: ds)
termination_by xs ys _ => xs.length + ys.length
decreasing_by
  all_goals simp_wf
  all_goals omega

def rawSubtract : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], c => ([], c)
  | a :: as, [], c =>
      let r := rawSubtract as [] (borrowBit a false c)
      (diffBit a false c :: r.1, r.2)
  | [], b :: bs, c =>
      let r := rawSubtract [] bs (borrowBit false b c)
      (diffBit false b c :: r.1, r.2)
  | a :: as, b :: bs, c =>
      let r := rawSubtract as bs (borrowBit a b c)
      (diffBit a b c :: r.1, r.2)
termination_by xs ys _ => xs.length + ys.length
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem subBorrow_eq_rawSubtract (xs ys : List Bool) (c : Bool) :
    subBorrow xs ys c =
      if (rawSubtract xs ys c).2 then none else some (rawSubtract xs ys c).1 := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [subBorrow, rawSubtract]
      | cons b bs ih =>
          simp only [subBorrow, rawSubtract]
          rw [ih]
          cases rawSubtract [] bs (borrowBit false b c) with
          | mk ds borrow => cases borrow <;> rfl
  | cons a as ih =>
      cases ys with
      | nil =>
          simp only [subBorrow, rawSubtract]
          rw [ih]
          cases rawSubtract as [] (borrowBit a false c) with
          | mk ds borrow => cases borrow <;> rfl
      | cons b bs =>
          simp only [subBorrow, rawSubtract]
          rw [ih]
          cases rawSubtract as bs (borrowBit a b c) with
          | mk ds borrow => cases borrow <;> rfl

theorem rawSubtract_length (xs ys : List Bool) (c : Bool) :
    (rawSubtract xs ys c).1.length = max xs.length ys.length := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => simp [rawSubtract]
      | cons b bs ih =>
          have ht := ih (borrowBit false b c)
          simp only [rawSubtract, List.length_cons, List.length_nil] at ht ⊢
          omega
  | cons a as ih =>
      cases ys with
      | nil =>
          have ht := ih [] (borrowBit a false c)
          simp only [rawSubtract, List.length_cons, List.length_nil] at ht ⊢
          omega
      | cons b bs =>
          have ht := ih bs (borrowBit a b c)
          simp only [rawSubtract, List.length_cons] at ht ⊢
          omega

def BorrowSpec (m n : Nat) (c : Bool) : Option (List Bool) → Prop
  | none => m < n + (if c then 1 else 0)
  | some zs => bitValue zs + n + (if c then 1 else 0) = m

theorem borrowSpec_step (a b c : Bool) (m n : Nat) (r : Option (List Bool))
    (h : BorrowSpec m n (borrowBit a b c) r) :
    BorrowSpec (Nat.bit a m) (Nat.bit b n) c
      (r.map (fun ds => diffBit a b c :: ds)) := by
  cases r with
  | none =>
      change m < n + (if borrowBit a b c then 1 else 0) at h
      change Nat.bit a m < Nat.bit b n + (if c then 1 else 0)
      cases a <;> cases b <;> cases c <;>
        simp [borrowBit, Nat.bit] at h ⊢ <;> omega
  | some zs =>
      change bitValue zs + n + (if borrowBit a b c then 1 else 0) = m at h
      change bitValue (diffBit a b c :: zs) + Nat.bit b n +
        (if c then 1 else 0) = Nat.bit a m
      cases a <;> cases b <;> cases c <;>
        simp [diffBit, borrowBit, Nat.bit] at h ⊢ <;> omega

theorem subBorrow_spec (xs ys : List Bool) (c : Bool) :
    BorrowSpec (bitValue xs) (bitValue ys) c (subBorrow xs ys c) := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [subBorrow, BorrowSpec]
      | cons b bs ih =>
          simpa [subBorrow, Nat.bit] using
            borrowSpec_step false b c 0 (bitValue bs)
              (subBorrow [] bs (borrowBit false b c))
              (ih (borrowBit false b c))
  | cons a as ih =>
      cases ys with
      | nil =>
          simpa [subBorrow, Nat.bit] using
            borrowSpec_step a false c (bitValue as) 0
              (subBorrow as [] (borrowBit a false c))
              (ih [] (borrowBit a false c))
      | cons b bs =>
          simpa [subBorrow] using
            borrowSpec_step a b c (bitValue as) (bitValue bs)
              (subBorrow as bs (borrowBit a b c))
              (ih bs (borrowBit a b c))

def monus (xs ys : List Bool) : List Bool := trim ((subBorrow xs ys false).getD [])

theorem bitValue_monus (xs ys : List Bool) :
    bitValue (monus xs ys) = bitValue xs - bitValue ys := by
  have h := subBorrow_spec xs ys false
  cases hr : subBorrow xs ys false with
  | none =>
      have hlt : bitValue xs < bitValue ys := by simpa [hr, BorrowSpec] using h
      simp [monus, hr]
      omega
  | some zs =>
      have he : bitValue zs + bitValue ys = bitValue xs := by
        simpa [hr, BorrowSpec] using h
      have hv : bitValue zs = bitValue xs - bitValue ys := by omega
      simpa [monus, hr] using hv

theorem canonical_monus (xs ys : List Bool) : Canonical (monus xs ys) :=
  canonical_trim _

theorem monus_bits (a b : Nat) : monus a.bits b.bits = (a - b).bits := by
  have h := bits_bitValue (canonical_monus a.bits b.bits)
  simpa [bitValue_monus] using h.symm

end BinPackingGap.BinaryArithmetic

namespace BinPackingGap.UnaryToBinaryMachine

open Turing BinPackingGames.Foundations.Complexity
open MachineComposition BinaryArithmetic
open BinPackingGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

variable (source output scratch : K)
variable (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)

include hSO hSC in
@[simp] theorem tapes_source (base : K → List Bool) (input binary work : List Bool) :
    tapes source output scratch base input binary work source = input := by
  simp [tapes, hSO, hSC]

end BinPackingGap.UnaryToBinaryMachine

namespace BinPackingGap.BinaryAddMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinaryArithmetic

variable {A : Type}

variable {K Λ A : Type} [DecidableEq K]

variable (left right output : K)
variable (hLR : left ≠ right) (hLO : left ≠ output) (hRO : right ≠ output)

include hLR hLO in
@[simp] theorem tapes_left (base : K → List Bool) (xs ys out : List Bool) :
    tapes left right output base xs ys out left = xs := by
  simp [tapes, hLR, hLO]

include hRO in
@[simp] theorem tapes_right (base : K → List Bool) (xs ys out : List Bool) :
    tapes left right output base xs ys out right = ys := by
  simp [tapes, hRO]

@[simp] theorem tapes_output (base : K → List Bool) (xs ys out : List Bool) :
    tapes left right output base xs ys out output = out := by simp [tapes]

include hLR hLO hRO in
theorem update_left (base : K → List Bool) (xs ys out next : List Bool) :
    Function.update (tapes left right output base xs ys out) left next =
      tapes left right output base next ys out := by
  funext k
  by_cases hl : k = left
  · subst k; simp [tapes, hLR, hLO]
  · by_cases hr : k = right
    · subst k; simp [tapes, Ne.symm hLR, hRO]
    · by_cases ho : k = output
      · subst k; simp [tapes, Ne.symm hLO]
      · simp [tapes, hl, hr, ho]

include hRO in
theorem update_right (base : K → List Bool) (xs ys out next : List Bool) :
    Function.update (tapes left right output base xs ys out) right next =
      tapes left right output base xs next out := by
  funext k
  by_cases hr : k = right
  · subst k; simp [tapes, hRO]
  · by_cases ho : k = output
    · subst k; simp [tapes, Ne.symm hRO]
    · simp [tapes, hr, ho]

theorem update_output (base : K → List Bool) (xs ys out next : List Bool) :
    Function.update (tapes left right output base xs ys out) output next =
      tapes left right output base xs ys next := by
  simp [tapes]

variable (again : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atAdd : program again = addLoop left right output again exit)
variable (base : K → List Bool) (ambient : A)

include hLR hLO hRO atAdd

theorem step_done (out : List Bool) (carry : Bool) (lreg rreg : Option Bool) :
    TM2.step program
      ⟨some again, state ambient carry lreg rreg, tapes left right output base [] [] out⟩ =
      some ⟨exit, clean ambient, tapes left right output base [] []
        (if carry then true :: out else out)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atAdd]
  cases carry <;> cases exit <;>
    simp [addLoop, finish, exitAt, clean, state, TM2.stepAux,
      hLR, hLO, hRO, tapes_left, tapes_right, update_left, update_right, update_output]

theorem step_more (xs ys out : List Bool) (carry : Bool) (lreg rreg : Option Bool)
    (more : xs ≠ [] ∨ ys ≠ []) :
    TM2.step program
      ⟨some again, state ambient carry lreg rreg, tapes left right output base xs ys out⟩ =
      some ⟨some again, state ambient
        (carryBit (xs.headD false) (ys.headD false) carry) none none,
        tapes left right output base xs.tail ys.tail
          (sumBit (xs.headD false) (ys.headD false) carry :: out)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atAdd]
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at more
      | cons y ys =>
          simp [addLoop, state, TM2.stepAux, hLR, hLO, hRO,
            tapes_left, tapes_right, update_left, update_right, update_output]
  | cons x xs =>
      cases ys <;>
        simp [addLoop, state, TM2.stepAux, hLR, hLO, hRO,
          tapes_left, tapes_right, update_left, update_right, update_output]

theorem addTrace (xs ys out : List Bool) (carry : Bool) (lreg rreg : Option Bool) :
    (advance (TM2.step program))^[max xs.length ys.length + 1]
      (some ⟨some again, state ambient carry lreg rreg,
        tapes left right output base xs ys out⟩) =
      some ⟨exit, clean ambient,
        tapes left right output base [] [] ((addCarry xs ys carry).reverse ++ out)⟩ := by
  induction xs generalizing ys out carry lreg rreg with
  | nil =>
      induction ys generalizing out carry lreg rreg with
      | nil =>
          have run := step_done left right output hLR hLO hRO again exit program atAdd
            base ambient out carry lreg rreg
          cases carry <;> simpa [addCarry, List.length_nil, advance_some] using run
      | cons y ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exit program atAdd base ambient
            [] (y :: ys) out carry lreg rreg (Or.inr (List.cons_ne_nil _ _))]
          simpa [addCarry, List.reverse_cons, List.append_assoc] using
            ih (sumBit false y carry :: out) (carryBit false y carry) none none
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.max_zero]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exit program atAdd base ambient
            (x :: xs) [] out carry lreg rreg (Or.inl (List.cons_ne_nil _ _))]
          simpa [addCarry, List.reverse_cons, List.append_assoc] using
            ih [] (sumBit x false carry :: out) (carryBit x false carry) none none
      | cons y ys =>
          rw [show max (x :: xs).length (y :: ys).length + 1 =
            (max xs.length ys.length + 1) + 1 by simp]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exit program atAdd base ambient
            (x :: xs) (y :: ys) out carry lreg rreg (Or.inl (List.cons_ne_nil _ _))]
          simpa [addCarry, List.reverse_cons, List.append_assoc] using
            ih ys (sumBit x y carry :: out) (carryBit x y carry) none none

def addInTime (xs ys out : List Bool) (carry : Bool) (lreg rreg : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, state ambient carry lreg rreg, tapes left right output base xs ys out⟩
      (some ⟨exit, clean ambient,
        tapes left right output base [] [] ((addCarry xs ys carry).reverse ++ out)⟩)
      (max xs.length ys.length + 1) where
  steps := max xs.length ys.length + 1
  evals_in_steps := addTrace left right output hLR hLO hRO again exit program atAdd base ambient
    xs ys out carry lreg rreg
  steps_le_m := Nat.le_refl _

def addNatInTime (a b : Nat) (out : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, clean ambient, tapes left right output base a.bits b.bits out⟩
      (some ⟨exit, clean ambient,
        tapes left right output base [] [] ((a + b).bits.reverse ++ out)⟩)
      (max a.size b.size + 1) := by
  simpa [clean, addCarry_bits, Nat.size_eq_bits_len] using
    addInTime left right output hLR hLO hRO again exit program atAdd base ambient
      a.bits b.bits out false none none

end BinPackingGap.BinaryAddMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryPowerMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryMulMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) := BinaryAddMachine.State A

def clean (ambient : A) : State A := (((ambient, false), none), none)

@[simp] theorem framedTapes_slot (slots : Fin 9 ↪ K) (base : K → List Bool)
    (words : Fin 9 → List Bool) (i : Fin 9) :
    framedTapes slots base words (slots i) = words i := by
  unfold framedTapes
  rw [dite_eq_left ⟨i, rfl⟩]
  congr 1
  exact slots.injective (Classical.choose_spec (show ∃ j, slots j = slots i from ⟨i, rfl⟩))

theorem framedTapes_other (slots : Fin 9 ↪ K) (base : K → List Bool)
    (words : Fin 9 → List Bool) (k : K) (hk : ¬ ∃ i, slots i = k) :
    framedTapes slots base words k = base k := by
  simp [framedTapes, hk]

theorem framedTapes_update (slots : Fin 9 ↪ K) (base : K → List Bool)
    (words : Fin 9 → List Bool) (i : Fin 9) (word : List Bool) :
    Function.update (framedTapes slots base words) (slots i) word =
      framedTapes slots base (Function.update words i word) := by
  funext k
  by_cases hk : ∃ j, slots j = k
  · obtain ⟨j, rfl⟩ := hk
    by_cases hji : j = i
    · subst j; simp
    · simp [Function.update_of_ne, hji, slots.injective.ne hji]
  · have hki : k ≠ slots i := fun h => hk ⟨i, h.symm⟩
    simp [Function.update_of_ne hki, framedTapes_other slots base _ k hk]

noncomputable def tapes (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch : List Bool) :
    K → List Bool :=
  framedTapes slots base ![left, right, output, shifted, remaining, accumulator,
    addend, reversed, scratch]

def loopSteps (xs : List Bool) : List Bool → List Bool → Nat
  | [], acc => xs.length + 2 * acc.length + 4
  | false :: ys, acc => loopSteps (BinaryArithmetic.shift xs) ys acc + 2
  | true :: ys, acc =>
      loopSteps (BinaryArithmetic.shift xs) ys (BinaryArithmetic.addCarry xs acc false) +
        (2 * xs.length + max xs.length acc.length +
          (BinaryArithmetic.addCarry xs acc false).length + 6)

def steps (xs ys : List Bool) : Nat :=
  loopSteps xs ys [] + (2 * (ys.length + 1) + 2 * (xs.length + 1))

@[simp] theorem tapes_slot (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch : List Bool) (i : Fin 9) :
    tapes slots base left right output shifted remaining accumulator addend reversed scratch (slots i) =
      ![left, right, output, shifted, remaining, accumulator, addend, reversed, scratch] i :=
  framedTapes_slot slots base _ i

@[simp] theorem tapes_update0 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 0) replacement =
      tapes slots base replacement right output shifted remaining accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] theorem tapes_update1 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 1) replacement =
      tapes slots base left replacement output shifted remaining accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] theorem tapes_update2 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 2) replacement =
      tapes slots base left right replacement shifted remaining accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] theorem tapes_update3 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 3) replacement =
      tapes slots base left right output replacement remaining accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] theorem tapes_update4 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 4) replacement =
      tapes slots base left right output shifted replacement accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] theorem tapes_update5 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 5) replacement =
      tapes slots base left right output shifted remaining replacement addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] theorem tapes_update6 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 6) replacement =
      tapes slots base left right output shifted remaining accumulator replacement reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] theorem tapes_update7 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 7) replacement =
      tapes slots base left right output shifted remaining accumulator addend replacement scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] theorem tapes_update8 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 8) replacement =
      tapes slots base left right output shifted remaining accumulator addend reversed replacement := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

theorem loopSteps_le (xs ys acc : List Bool) :
    loopSteps xs ys acc ≤
      (ys.length + 1) * (4 * (max xs.length acc.length + ys.length) + 8) := by
  induction ys generalizing xs acc with
  | nil =>
      have hx := Nat.le_max_left xs.length acc.length
      have ha := Nat.le_max_right xs.length acc.length
      simp only [loopSteps, List.length_nil, Nat.zero_add, Nat.add_zero, Nat.one_mul]
      omega
  | cons bit ys ih =>
      have hx := Nat.le_max_left xs.length acc.length
      have ha := Nat.le_max_right xs.length acc.length
      have hs := BinaryArithmetic.shift_length_le xs
      cases bit with
      | false =>
          have hp : max (BinaryArithmetic.shift xs).length acc.length + ys.length ≤
              max xs.length acc.length + (ys.length + 1) := by omega
          have h := (ih (BinaryArithmetic.shift xs) acc).trans
            (Nat.mul_le_mul_left (ys.length + 1)
              (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hp) 8))
          simp only [loopSteps, List.length_cons]
          nlinarith
      | true =>
          have hadd := BinaryArithmetic.addCarry_length xs acc false
          have hp : max (BinaryArithmetic.shift xs).length
                (BinaryArithmetic.addCarry xs acc false).length + ys.length ≤
              max xs.length acc.length + (ys.length + 1) := by omega
          have h := (ih (BinaryArithmetic.shift xs) (BinaryArithmetic.addCarry xs acc false)).trans
            (Nat.mul_le_mul_left (ys.length + 1)
              (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hp) 8))
          simp only [loopSteps, List.length_cons]
          nlinarith

theorem steps_le_timePolynomial (xs ys : List Bool) :
    steps xs ys ≤ timePolynomial.eval (xs.length + ys.length) := by
  have hloop := loopSteps_le xs ys []
  simp only [List.length_nil, Nat.max_zero] at hloop
  have hproduct := Nat.mul_le_mul_right (4 * (xs.length + ys.length) + 8)
    (show ys.length + 1 ≤ (xs.length + ys.length) + 1 by omega)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  unfold steps
  nlinarith

end BinPackingGap.BinaryMulMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Information_GameDecoder
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Hastad.SourceContexts

open Target PCP

instance clauseAnswerInhabited : Inhabited ClauseAnswer := ⟨⟨false, false, false⟩⟩

instance slotFintype : Fintype Slot where
  elems := {.first, .second, .third}
  complete s := by cases s <;> simp

instance slotInhabited : Inhabited Slot := ⟨.first⟩

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

end BinPackingGames.Foundations.Hastad.SourceContexts

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Expanders_SpectralCut
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

def correlation {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  mean (fun x => f x * g x)

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def edgeDensity {V D : Type*} [Fintype V] [Fintype D] (bad : V × D → Bool) : ℝ :=
  mean (edgeProfile bad)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

end BinPackingGames.Foundations.PCP.SpectralReturn

namespace BinPackingGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def cloudOperator [Fintype E] (H : PortGraph D E) (f : V × D → ℝ) (x : V × D) : ℝ :=
  SpectralReturn.mean (fun e => f (x.1, (H.rot (x.2, e)).1))

def graphPermutation (G : PortGraph V D) (f : V × D → ℝ) (x : V × D) : ℝ :=
  f (G.rot x)

end BinPackingGames.Foundations.PCP.ZigzagGraphs

namespace BinPackingGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

def cut (G : PortGraph V D) (S : Finset V) : Finset (V × D) :=
  Finset.univ.filter (fun e => e.1 ∈ S ∧ (G.rot e).1 ∉ S)

end BinPackingGames.Foundations.PCP.SpectralCut

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Expanders_ZigzagSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

end

end BinPackingGames.Foundations.PCP.ZigzagSpectral

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Queries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open BinPackingGames.Foundations.Hastad

@[simp] theorem disagreement_self (a : Bool) : disagreement a a = 0 := by
  simp [disagreement]

def relativeDistance {X : Type*} [Fintype X] (f g : X → Bool) : ℝ :=
  𝔼 x, disagreement (f x) (g x)

@[simp] theorem relativeDistance_self {X : Type*} [Fintype X] (f : X → Bool) :
    relativeDistance f f = 0 := by
  simp [relativeDistance]

end BinPackingGames.Foundations.PCP.CodeComposition

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Expanders_ExpanderTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

instance basePortNonempty : Nonempty BasePort :=
  ⟨fun _ => ⟨0, by norm_num [initialQuarterDegree]⟩⟩

instance vertexNonempty (n : Nat) : Nonempty (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih =>
    let : Nonempty (Vertex n) := ih
    change Nonempty (Vertex n × CloudPort)
    infer_instance

end BinPackingGames.Foundations.PCP.ExpanderFamily

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_FinalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.FinalConstants

def windowSize : Nat := 2 * windowHalf + 1

noncomputable def gain : ℝ := (windowSize : ℝ) / denominator
noncomputable def cap : ℝ := 1 / (walkLength : ℝ)

end BinPackingGames.Foundations.PCP.FinalConstants

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_MachineTransducer
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Reduction.MachineTransducer

open Turing
open BinPackingGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord )

variable {Q : Type} [Fintype Q]

def program (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Option (Q × Bool) →
      TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool)
  | none => loop initial
  | some (state, symbol) =>
      .load (fun register => (transition state symbol, register.2))
        (pushWord true (emit state symbol) (.goto fun _ => none))

def machine (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Option (Q × Bool)
  main := none
  σ := Q × Option Bool
  initialState := (initial, none)
  m := program initial transition emit

def running (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (state : Q) (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).Cfg :=
  ⟨some none, (state, register), tapeStacks input accumulator⟩

def emitting (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (oldState : Q) (symbol : Bool) (input accumulator : List Bool)
    (state : Q × Option Bool) : (machine initial transition emit).Cfg :=
  ⟨some (some (oldState, symbol)), state, tapeStacks input accumulator⟩

def halted (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (accumulator : List Bool) : (machine initial transition emit).Cfg :=
  ⟨none, (initial, none), tapeStacks [] accumulator⟩

theorem step_empty (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (accumulator : List Bool)
    (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state [] accumulator register) =
      some (halted initial transition emit accumulator) := by
  change some (TM2.stepAux (loop initial) (state, register) (tapeStacks [] accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, halted]
  exact congrArg (fun tapes => some (⟨none, (initial, none), tapes⟩ :
    (machine initial transition emit).Cfg)) (update_input [] accumulator [])

theorem step_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state (symbol :: input) accumulator register) =
      some (emitting initial transition emit state symbol input accumulator (state, some symbol)) := by
  change some (TM2.stepAux (loop initial) (state, register)
    (tapeStacks (symbol :: input) accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, emitting]
  rw [update_input]
  rfl

theorem step_emit (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (oldState : Q) (symbol : Bool)
    (input accumulator : List Bool) (state : Q × Option Bool) :
    (machine initial transition emit).step
        (emitting initial transition emit oldState symbol input accumulator state) =
      some (running initial transition emit (transition oldState symbol) input
        ((emit oldState symbol).reverse ++ accumulator) state.2) := by
  change some (TM2.stepAux (pushWord true (emit oldState symbol) (.goto fun _ => none))
    (transition oldState symbol, state.2) (tapeStacks input accumulator)) = _
  rw [stepAux_pushWord]
  simp only [TM2.stepAux]
  change some (⟨some none, (transition oldState symbol, state.2),
    Function.update (tapeStacks input accumulator) true
      ((emit oldState symbol).reverse ++ accumulator)⟩ :
    (machine initial transition emit).Cfg) = _
  exact congrArg (fun tapes => some (⟨some none, (transition oldState symbol, state.2), tapes⟩ :
    (machine initial transition emit).Cfg))
    (update_output input accumulator ((emit oldState symbol).reverse ++ accumulator))

def next (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (configuration : Option (machine initial transition emit).Cfg) :
    Option (machine initial transition emit).Cfg :=
  configuration.bind (machine initial transition emit).step

theorem two_steps_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (next initial transition emit)^[2]
        (some (running initial transition emit state (symbol :: input) accumulator register)) =
      some (running initial transition emit (transition state symbol) input
        ((emit state symbol).reverse ++ accumulator) (some symbol)) := by
  change (machine initial transition emit).step
    (running initial transition emit state (symbol :: input) accumulator register) >>=
      (machine initial transition emit).step = _
  rw [step_cons]
  exact step_emit initial transition emit state symbol input accumulator (state, some symbol)

theorem transduce_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (input accumulator : List Bool)
    (register : Option Bool) :
    (next initial transition emit)^[2 * input.length + 1]
        (some (running initial transition emit state input accumulator register)) =
      some (halted initial transition emit ((output transition emit state input).reverse ++ accumulator)) := by
  induction input generalizing state accumulator register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, output, List.reverse_nil, List.nil_append]
      using step_empty initial transition emit state accumulator register
  | cons symbol input ih =>
    rw [List.length_cons]
    rw [show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega]
    rw [Function.iterate_add_apply, two_steps_cons, ih]
    simp only [output, List.reverse_append, List.append_assoc]

theorem initList_eq (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    initList (machine initial transition emit) input =
      running initial transition emit initial input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (accumulator : List Bool) :
    haltList (machine initial transition emit) accumulator =
      halted initial transition emit accumulator := by
  unfold haltList halted
  congr 1

theorem transduce_init_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    (next initial transition emit)^[2 * input.length + 1]
        (some (initList (machine initial transition emit) input)) =
      some (haltList (machine initial transition emit) (output transition emit initial input).reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using transduce_steps initial transition emit initial input [] none

end BinPackingGames.Reduction.MachineTransducer

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

theorem output_encodeWord (a : ℕ) :
    Reduction.MachineTransducer.output transition payload () (encodeWord a) =
      List.replicate a true := by
  induction a with
  | zero => simp [encodeWord, Reduction.MachineTransducer.output, payload]
  | succ a ih =>
    simpa only [encodeWord, List.replicate_succ, List.cons_append,
      Reduction.MachineTransducer.output, payload, Bool.cond_true, transition,
      ite_true, if_true, List.singleton_append, List.nil_append] using congrArg (List.cons true) ih

theorem prepend_payload (a p : ℕ) (suffix : List Bool) :
    List.replicate a true ++ (encodeWord p ++ suffix) = encodeWord (a + p) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

def loopBase (slots : Fin 5 ↪ K) (base : K → List Bool) (a b r : ℕ) : K → List Bool :=
  resultTapes slots base (a * (b - r))

theorem totalSteps_eq (a b : ℕ) :
    MachineCountedLoop.totalSteps (fun _ => bodySteps a) b = b * (bodySteps a + 1) + 1 := by
  simp [MachineCountedLoop.totalSteps, Nat.mul_add, Nat.add_assoc]

end BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

namespace BinPackingGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

def value (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => radix * value radix digits n + digits n

def prefixSteps (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSteps radix digits n + stepCost radix (value radix digits n) (digits n)

def stageTapes (slots : Layout width ↪ K) (base : K → List Bool) (n acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl (accumulator (parity n)))) (encodeWord acc)

structure Clean (slots : Layout width ↪ K) (base : K → List Bool) : Prop where
  accA : base (slots (.inl 1)) = []
  accB : base (slots (.inl 2)) = []
  counter : base (slots (.inl 4)) = []
  scratch : base (slots (.inl 5)) = []

omit [DecidableEq K] in
theorem Clean.acc {slots : Layout width ↪ K} {base : K → List Bool}
    (clean : Clean slots base) (flip : Bool) : base (slots (.inl (accumulator flip))) = [] := by
  cases flip
  · exact clean.accA
  · exact clean.accB

def steps (radix : Nat) (digits : Nat → Nat) (width : Nat) : Nat :=
  prefixSteps radix digits width + 2 * value radix digits width + 5

omit [DecidableEq K] in
theorem value_eq_foldl (radix : Nat) (digits : Nat → Nat) (n : Nat) :
    value radix digits n =
      ((List.range n).map digits).foldl (fun acc digit => radix * acc + digit) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [value, List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_singleton, List.foldl_cons, List.foldl_nil, ← ih]

open scoped BigOperators

end BinPackingGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_GraphTallyMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryEncoding

@[simp] theorem natBits_length (n : Nat) : (natBits n).length = 2 * n.size + 1 :=
  BinPackingCompleteness.BinaryEncoding.nameBits_length n

@[simp] theorem parseNat_natBits (n : Nat) (suffix : List Bool) :
    parseNat (natBits n ++ suffix) = some (n, suffix) :=
  BinPackingCompleteness.BinaryEncoding.parseName_encoded n suffix

@[simp] theorem parseRawInstance_rawInstanceBits (r : RawInstance) (suffix : List Bool) :
    parseRawInstance (rawInstanceBits r ++ suffix) = some (r, suffix) :=
  parseList_listBits _ _
    (parsePair_pairBits _ _ _ _ parseNat_natBits parseNat_natBits) r suffix

@[simp] theorem parseAssignments_assignmentBits (a : List Nat) (suffix : List Bool) :
    parseAssignments (assignmentBits a ++ suffix) = some (a, suffix) :=
  parseList_listBits _ _ parseNat_natBits a suffix

@[simp] theorem parseExtension_extensionBits (bins : Nat) (r : RawInstance)
    (fixed : List (Option Nat)) (suffix : List Bool) :
    parseExtension (extensionBits bins r fixed ++ suffix) = some ((bins, r, fixed), suffix) := by
  have hf := parseList_listBits (optionBits natBits) (parseOption parseNat)
    (parseOption_optionBits _ _ parseNat_natBits) fixed suffix
  simp [parseExtension, parsePair, extensionBits, List.append_assoc, hf]

@[simp] theorem decodeRawInstance_rawInstanceBits (r : RawInstance) :
    decodeRawInstance (rawInstanceBits r) = some r :=
  decode_encode _ _ parseRawInstance_rawInstanceBits r

@[simp] theorem decodeAssignments_assignmentBits (a : List Nat) :
    decodeAssignments (assignmentBits a) = some a :=
  decode_encode _ _ parseAssignments_assignmentBits a

@[simp] theorem decodeExtension_extensionBits (bins : Nat) (r : RawInstance)
    (fixed : List (Option Nat)) :
    decodeExtension (extensionBits bins r fixed) = some (bins, r, fixed) := by
  have h := parseExtension_extensionBits bins r fixed []
  simp only [List.append_nil] at h
  simp [decodeExtension, decode, h]

@[simp] theorem rawInstanceBits_length (r : RawInstance) :
    (rawInstanceBits r).length =
      1 + (r.map fun q => 2 * q.1.size + 2 * q.2.size + 3).sum := by
  simp only [rawInstanceBits, listBits_length, pairBits_length, natBits_length]
  congr 2
  apply List.map_congr_left
  intro q _
  omega

@[simp] theorem assignmentBits_length (a : List Nat) :
    (assignmentBits a).length = 1 + (a.map fun j => 2 * j.size + 2).sum := by
  simp only [assignmentBits, listBits_length, natBits_length]
  congr 2
  apply List.map_congr_left
  intro j _
  omega

theorem parseFrame_sound {input bits suffix : List Bool}
    (h : BinPackingCompleteness.BinaryEncoding.parseFrame input = some (bits, suffix)) :
    input = BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix := by
  induction input using List.twoStepInduction generalizing bits suffix with
  | nil => simp [BinPackingCompleteness.BinaryEncoding.parseFrame] at h
  | singleton flag =>
      cases flag with
      | false =>
          simp only [BinPackingCompleteness.BinaryEncoding.parseFrame, Option.some.injEq,
            Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | true => simp [BinPackingCompleteness.BinaryEncoding.parseFrame] at h
  | cons_cons flag bit rest ih _ =>
      cases flag with
      | false =>
          simp only [BinPackingCompleteness.BinaryEncoding.parseFrame, Option.some.injEq,
            Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | true =>
          cases hp : BinPackingCompleteness.BinaryEncoding.parseFrame rest with
          | none => simp [BinPackingCompleteness.BinaryEncoding.parseFrame, hp] at h
          | some result =>
              rcases result with ⟨digits, tail⟩
              simp only [BinPackingCompleteness.BinaryEncoding.parseFrame, hp] at h
              rcases h with ⟨rfl, rfl⟩
              simp [BinPackingCompleteness.BinaryEncoding.frame, ih hp]

theorem parseNat_sound : ParserSound natBits parseNat := by
  intro input n suffix h
  cases hp : BinPackingCompleteness.BinaryEncoding.parseFrame input with
  | none => simp [parseNat, BinPackingCompleteness.BinaryEncoding.parseName, hp] at h
  | some result =>
      rcases result with ⟨digits, tail⟩
      by_cases hc : digits = (BinPackingCompleteness.BinaryEncoding.bitsValue digits).bits
      · have parsed : parseNat input =
            some (BinPackingCompleteness.BinaryEncoding.bitsValue digits, tail) := by
          rw [parseNat, BinPackingCompleteness.BinaryEncoding.parseName, hp]
          change (if digits = (BinPackingCompleteness.BinaryEncoding.bitsValue digits).bits
            then some (BinPackingCompleteness.BinaryEncoding.bitsValue digits, tail) else none) = _
          exact ite_eq_left hc
        have values := Option.some.inj (parsed.symm.trans h)
        simp only [Prod.mk.injEq] at values
        rcases values with ⟨rfl, rfl⟩
        simpa only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits, ← hc] using
          parseFrame_sound hp
      · simp [parseNat, BinPackingCompleteness.BinaryEncoding.parseName, hp, hc] at h

theorem parsePair_sound {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (pa : Parser α) (pb : Parser β) (ha : ParserSound ea pa) (hb : ParserSound eb pb) :
    ParserSound (pairBits ea eb) (parsePair pa pb) := by
  intro input p suffix h
  cases hpa : pa input with
  | none => simp [parsePair, hpa] at h
  | some first =>
      rcases first with ⟨a, rest⟩
      cases hpb : pb rest with
      | none => simp [parsePair, hpa, hpb] at h
      | some second =>
          rcases second with ⟨b, tail⟩
          have parsed : parsePair pa pb input = some ((a, b), tail) := by
            simp [parsePair, hpa, hpb]
          have values := Option.some.inj (parsed.symm.trans h)
          simp only [Prod.mk.injEq] at values
          rcases values with ⟨rfl, rfl⟩
          rw [ha hpa, hb hpb]
          simp [pairBits, List.append_assoc]

theorem parseOption_sound {α : Type} (encode : α → List Bool) (parse : Parser α)
    (hp : ParserSound encode parse) : ParserSound (optionBits encode) (parseOption parse) := by
  intro input a suffix h
  cases input with
  | nil => simp [parseOption] at h
  | cons flag rest =>
      cases flag with
      | false =>
          simp only [parseOption, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | true =>
          cases hparse : parse rest with
          | none => simp [parseOption, hparse] at h
          | some result =>
              rcases result with ⟨x, tail⟩
              simp only [parseOption, hparse] at h
              rcases h with ⟨rfl, rfl⟩
              simp [optionBits, hp hparse]

theorem parseListAux_sound {α : Type} (encode : α → List Bool) (parse : Parser α)
    (hp : ParserSound encode parse) (fuel : Nat) :
    ParserSound (listBits encode) (parseListAux parse fuel) := by
  induction fuel with
  | zero => intro input xs suffix h; simp [parseListAux] at h
  | succ fuel ih =>
      intro input xs suffix h
      cases input with
      | nil => simp [parseListAux] at h
      | cons flag rest =>
          cases flag with
          | false =>
              simp only [parseListAux, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              rfl
          | true =>
              cases hhead : parse rest with
              | none => simp [parseListAux, hhead] at h
              | some first =>
                  rcases first with ⟨a, remaining⟩
                  cases htail : parseListAux parse fuel remaining with
                  | none => simp [parseListAux, hhead, htail] at h
                  | some second =>
                      rcases second with ⟨as, tail⟩
                      have parsed : parseListAux parse (fuel + 1) (true :: rest) =
                          some (a :: as, tail) := by
                        simp [parseListAux, hhead, htail]
                      have values := Option.some.inj (parsed.symm.trans h)
                      simp only [Prod.mk.injEq] at values
                      rcases values with ⟨rfl, rfl⟩
                      simp [listBits, hp hhead, ih htail, List.append_assoc]

theorem parseList_sound {α : Type} (encode : α → List Bool) (parse : Parser α)
    (hp : ParserSound encode parse) : ParserSound (listBits encode) (parseList parse) := by
  intro input xs suffix h
  exact parseListAux_sound encode parse hp input.length h

theorem parseRawInstance_sound : ParserSound rawInstanceBits parseRawInstance :=
  parseList_sound _ _ (parsePair_sound _ _ _ _ parseNat_sound parseNat_sound)

theorem parseAssignments_sound : ParserSound assignmentBits parseAssignments :=
  parseList_sound _ _ parseNat_sound

theorem decodeRawInstance_sound {input : List Bool} {r : RawInstance}
    (h : decodeRawInstance input = some r) : input = rawInstanceBits r :=
  decode_sound _ _ parseRawInstance_sound h

theorem decodeAssignments_sound {input : List Bool} {a : List Nat}
    (h : decodeAssignments input = some a) : input = assignmentBits a :=
  decode_sound _ _ parseAssignments_sound h

theorem decodeExtension_sound {input : List Bool} {bins : Nat} {r : RawInstance}
    {fixed : List (Option Nat)} (h : decodeExtension input = some (bins, r, fixed)) :
    input = extensionBits bins r fixed := by
  have hs : ParserSound
      (pairBits natBits (pairBits rawInstanceBits (listBits (optionBits natBits))))
      parseExtension := parsePair_sound natBits
    (pairBits rawInstanceBits (listBits (optionBits natBits))) _ _ parseNat_sound
    (parsePair_sound _ _ _ _ parseRawInstance_sound
      (parseList_sound _ _ (parseOption_sound _ _ parseNat_sound)))
  have hi := decode_sound _ _ hs h
  simpa [pairBits, extensionBits, List.append_assoc] using hi

end BinPackingGap.BinaryEncoding

namespace BinPackingGap

namespace GraphFields

open BinaryEncoding

def bits (fields : GraphFields) : List Bool :=
  natBits fields.k ++ listBits natBits fields.vertices ++
    listBits (pairBits natBits natBits) fields.endpoints

@[simp] theorem bits_length (fields : GraphFields) :
    fields.bits.length = (natBits fields.k).length +
      (listBits natBits fields.vertices).length +
      (listBits (pairBits natBits natBits) fields.endpoints).length := by
  simp [bits, Nat.add_assoc]

end GraphFields

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCanonicalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem finalTapes_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∈ chosen) :
    finalTapes chosen base k = [] := by rw [finalTapes_apply, ite_eq_left h]

end BinPackingGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryAddPreserving

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)

variable {K Λ A : Type} [DecidableEq K]

theorem steps_le (a b : Nat) : steps a b ≤ 4 * (a.size + b.size) + 7 := by
  have sumLength := BinaryArithmetic.size_add_le a b
  unfold steps
  omega

end BinPackingGap.BinaryAddPreserving

namespace BinPackingGap.BinaryMonusMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinaryArithmetic BinaryAddMachine

variable {K Λ A : Type} [DecidableEq K]

def subtractLoop (left right output : K) (again : Λ) (exits : Bool → Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop left (fun s head => ((s.1.1, head), s.2))
    (.pop right (fun s head => (s.1, head))
      (.branch (fun s => s.1.2.isNone && s.2.isNone)
        (.branch (fun s => s.1.1.2) (finish (exits true)) (finish (exits false)))
        (.push output (fun s => diffBit (s.1.2.getD false) (s.2.getD false) s.1.1.2)
          (.load (fun s => state s.1.1.1
            (borrowBit (s.1.2.getD false) (s.2.getD false) s.1.1.2) none none)
            (.goto fun _ => again)))))

section Subtract

variable (left right output : K)
variable (hLR : left ≠ right) (hLO : left ≠ output) (hRO : right ≠ output)
variable (again : Λ) (exits : Bool → Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atSub : program again = subtractLoop left right output again exits)
variable (base : K → List Bool) (ambient : A)

include hLR hLO hRO atSub

theorem step_done (out : List Bool) (borrow : Bool) (lreg rreg : Option Bool) :
    TM2.step program
      ⟨some again, state ambient borrow lreg rreg, tapes left right output base [] [] out⟩ =
      some ⟨exits borrow, clean ambient, tapes left right output base [] [] out⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atSub]
  cases borrow <;> cases hx : exits true <;> cases hy : exits false <;>
    simp [subtractLoop, finish, exitAt, clean, state, TM2.stepAux,
      hLR, hLO, hRO, tapes_left, tapes_right, update_left, update_right, hx, hy]

theorem step_more (xs ys out : List Bool) (borrow : Bool) (lreg rreg : Option Bool)
    (more : xs ≠ [] ∨ ys ≠ []) :
    TM2.step program
      ⟨some again, state ambient borrow lreg rreg, tapes left right output base xs ys out⟩ =
      some ⟨some again, state ambient
        (borrowBit (xs.headD false) (ys.headD false) borrow) none none,
        tapes left right output base xs.tail ys.tail
          (diffBit (xs.headD false) (ys.headD false) borrow :: out)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atSub]
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at more
      | cons y ys =>
          simp [subtractLoop, state, TM2.stepAux, hLR, hLO, hRO,
            tapes_left, tapes_right, update_left, update_right, update_output]
  | cons x xs =>
      cases ys <;>
        simp [subtractLoop, state, TM2.stepAux, hLR, hLO, hRO,
          tapes_left, tapes_right, update_left, update_right, update_output]

theorem subtractTrace (xs ys out : List Bool) (borrow : Bool) (lreg rreg : Option Bool) :
    (advance (TM2.step program))^[max xs.length ys.length + 1]
      (some ⟨some again, state ambient borrow lreg rreg,
        tapes left right output base xs ys out⟩) =
      some ⟨exits (rawSubtract xs ys borrow).2, clean ambient,
        tapes left right output base [] [] ((rawSubtract xs ys borrow).1.reverse ++ out)⟩ := by
  induction xs generalizing ys out borrow lreg rreg with
  | nil =>
      induction ys generalizing out borrow lreg rreg with
      | nil =>
          simpa [rawSubtract, List.length_nil, advance_some] using
            step_done left right output hLR hLO hRO again exits program atSub base ambient
              out borrow lreg rreg
      | cons y ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exits program atSub base ambient
            [] (y :: ys) out borrow lreg rreg (Or.inr (List.cons_ne_nil _ _))]
          simpa [rawSubtract, List.reverse_cons, List.append_assoc] using
            ih (diffBit false y borrow :: out) (borrowBit false y borrow) none none
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.max_zero]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exits program atSub base ambient
            (x :: xs) [] out borrow lreg rreg (Or.inl (List.cons_ne_nil _ _))]
          simpa [rawSubtract, List.reverse_cons, List.append_assoc] using
            ih [] (diffBit x false borrow :: out) (borrowBit x false borrow) none none
      | cons y ys =>
          rw [show max (x :: xs).length (y :: ys).length + 1 =
            (max xs.length ys.length + 1) + 1 by simp]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exits program atSub base ambient
            (x :: xs) (y :: ys) out borrow lreg rreg (Or.inl (List.cons_ne_nil _ _))]
          simpa [rawSubtract, List.reverse_cons, List.append_assoc] using
            ih ys (diffBit x y borrow :: out) (borrowBit x y borrow) none none

def subtractInTime (xs ys out : List Bool) (borrow : Bool) (lreg rreg : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, state ambient borrow lreg rreg, tapes left right output base xs ys out⟩
      (some ⟨exits (rawSubtract xs ys borrow).2, clean ambient,
        tapes left right output base [] [] ((rawSubtract xs ys borrow).1.reverse ++ out)⟩)
      (max xs.length ys.length + 1) where
  steps := max xs.length ys.length + 1
  evals_in_steps := subtractTrace left right output hLR hLO hRO again exits program atSub
    base ambient xs ys out borrow lreg rreg
  steps_le_m := Nat.le_refl _

end Subtract

variable {σ : Type}

def trimLoop (source : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun s bit => (s.1, bit))
    (.branch (fun s => s.2.isNone)
      (.load (fun s => (s.1, none)) (BinPackingGames.Reduction.MachineTransfer.exitAt source exit))
      (.branch (fun s => s.2.getD false)
        (.push source (fun _ => true)
          (.load (fun s => (s.1, none))
            (BinPackingGames.Reduction.MachineTransfer.exitAt source exit)))
        (.goto fun _ => again)))

theorem trimTrace (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTrim : program again = trimLoop source again exit)
    (base : K → List Bool) (word : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[trimSteps word]
      (some ⟨some again, (ambient, register), Function.update base source word⟩) =
      some ⟨exit, (ambient, none), Function.update base source (trimHigh word)⟩ := by
  induction word generalizing register with
  | nil =>
      change some (TM2.stepAux (program again) _ _) = _
      rw [atTrim]
      cases exit <;>
        simp [trimLoop, trimHigh, TM2.stepAux, BinPackingGames.Reduction.MachineTransfer.exitAt]
  | cons bit word ih =>
      cases bit with
      | false =>
          rw [trimSteps, Function.iterate_succ_apply]
          change (advance (TM2.step program))^[trimSteps word]
            (some (TM2.stepAux (program again) _ _)) = _
          rw [atTrim]
          simpa [trimLoop, trimHigh, TM2.stepAux] using ih (some false)
      | true =>
          change some (TM2.stepAux (program again) _ _) = _
          rw [atTrim]
          cases exit <;>
            simp [trimLoop, trimHigh, TM2.stepAux, BinPackingGames.Reduction.MachineTransfer.exitAt]

def trimInTime (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTrim : program again = trimLoop source again exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base source (trimHigh (base source))⟩)
      ((base source).length + 1) where
  steps := trimSteps (base source)
  evals_in_steps := by
    change (advance (TM2.step program))^[trimSteps (base source)]
      (some ⟨some again, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base source (trimHigh (base source))⟩
    simpa only [Function.update_eq_self] using
      trimTrace source again exit program atTrim base (base source) ambient register
  steps_le_m := trimSteps_le _

end BinPackingGap.BinaryMonusMachine

namespace BinPackingGap.BinaryMonusPreserving

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)
open BinaryArithmetic

variable {K Λ A : Type} [DecidableEq K]

def appendRuns {X : Type} (step : X → Option X) {a b c : X} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) where
  steps := first.steps + second.steps
  evals_in_steps := by
    have firstTrace := first.evals_in_steps
    have secondTrace := second.evals_in_steps
    change (MachineComposition.advance step)^[first.steps] (some a) = some b at firstTrace
    change (MachineComposition.advance step)^[second.steps] (some b) = some c at secondTrace
    change (MachineComposition.advance step)^[first.steps + second.steps] (some a) = some c
    rw [Nat.add_comm, Function.iterate_add_apply, firstTrace, secondTrace]
  steps_le_m := Nat.add_le_add first.steps_le_m second.steps_le_m

end BinPackingGap.BinaryMonusPreserving

namespace BinPackingGap.BinaryRegisterProgram

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {Reg K Λ A : Type}

def resultOf [DecidableEq Reg] : List (Command Reg) → (Reg → Nat) → Reg → Nat :=
  MachineFiniteSequence.resultOf result

@[simp] theorem resultOf_nil [DecidableEq Reg] (values : Reg → Nat) : resultOf [] values = values := rfl

end BinPackingGap.BinaryRegisterProgram

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringGlobalEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

instance labelDecidableEq (t : Nat) : DecidableEq (Label t) := by
  induction t with
  | zero => exact inferInstanceAs (DecidableEq MachineUnaryAffineAt.Label)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (PoweringMachineRotor.Label ⊕ Label t))

end BinPackingGames.Foundations.Complexity.PoweringMachineWord

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMachineRowBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

instance labelDecidableEq (op : Instruction d) : DecidableEq (Label op) := by
  cases op <;> dsimp only [Label] <;> infer_instance

end BinPackingGames.Foundations.Complexity.PoweringMachineField

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_BoundedExecution
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution

noncomputable def stackCapacity (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (T : Nat) : Nat :=
  input.length + T * Runtime.programPushBound tm

section Statement
variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem stackBound_of_budget (S : Nat) (stmt : Turing.TM2.Stmt Γ Λ σ)
    (tapes : ∀ k, List (Γ k))
    (h : ∀ k, (tapes k).length + Runtime.statementPushBound stmt ≤ S) : StackBound S tapes := by
  intro k
  have hk := h k
  omega

theorem statementSafe_of_budget (S : Nat) (stmt : Turing.TM2.Stmt Γ Λ σ)
    (state : σ) (tapes : ∀ k, List (Γ k))
    (h : ∀ k, (tapes k).length + Runtime.statementPushBound stmt ≤ S) :
    StatementSafe S stmt state tapes := by
  induction stmt generalizing state tapes with
  | push j f q ih =>
    refine ⟨stackBound_of_budget S _ tapes h, ?_, ?_⟩
    · have hj := h j
      simp only [Runtime.statementPushBound] at hj
      omega
    · apply ih
      intro k
      have hk := h k
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      simp only [Runtime.statementPushBound] at hk
      omega
  | peek j f q ih =>
    exact ⟨stackBound_of_budget S _ tapes h, ih _ _ h⟩
  | pop j f q ih =>
    refine ⟨stackBound_of_budget S _ tapes h, ?_⟩
    apply ih
    intro k
    have hk := h k
    have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
        (tapes k).length := by
      by_cases same : k = j
      · subst k; simp
      · simp [Function.update, same]
    simp only [Runtime.statementPushBound] at hk
    omega
  | load f q ih =>
    exact ⟨stackBound_of_budget S _ tapes h, ih _ _ h⟩
  | branch f yes no ihYes ihNo =>
    refine ⟨stackBound_of_budget S _ tapes h, ?_⟩
    cases decision : f state with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply ihNo
      intro k
      have hk := h k
      have hm := Nat.le_max_right (Runtime.statementPushBound yes) (Runtime.statementPushBound no)
      simp only [Runtime.statementPushBound] at hk
      omega
    | true =>
      simp only [↓reduceIte]
      apply ihYes
      intro k
      have hk := h k
      have hm := Nat.le_max_left (Runtime.statementPushBound yes) (Runtime.statementPushBound no)
      simp only [Runtime.statementPushBound] at hk
      omega
  | goto f => exact stackBound_of_budget S _ tapes h
  | halt => exact stackBound_of_budget S _ tapes h

end Statement

end BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ConfigIndex
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.StackEncoding

variable {Γ : Type*}

def read {S : Nat} (cells : Cells Γ S) (n : Nat) : Option Γ :=
  if h : n < S then cells ⟨n, h⟩ else none

@[simp] theorem read_at {S : Nat} (cells : Cells Γ S) (i : Fin S) :
    read cells i.val = cells i := by
  simp [read, i.isLt]

theorem read_encode {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) (n : Nat) :
    read (encode S xs) n = xs[n]? := by
  by_cases hn : n < S
  · simp [read, encode, hn]
  · have hx : xs.length ≤ n := by omega
    simp [read, hn, List.getElem?_eq_none hx]

theorem encode_injective {S : Nat} {xs ys : List Γ}
    (hx : xs.length ≤ S) (hy : ys.length ≤ S)
    (h : encode S xs = encode S ys) : xs = ys := by
  apply List.ext_getElem?
  intro n
  rw [← read_encode xs hx n, ← read_encode ys hy n, h]

end BinPackingGames.Foundations.Complexity.CookLevin.StackEncoding

namespace BinPackingGames.Foundations.Complexity.CookLevin

open Target

theorem Gate.eval_congr (g : Gate) {bound : Nat} (hg : g.Bounded bound)
    (A B : Nat → Bool) (h : ∀ j, j < bound → A j = B j) :
    g.eval A = g.eval B := by
  cases g with
  | const b => rfl
  | not x => simp only [Gate.eval, h x hg]
  | and x y => simp only [Gate.eval, h x hg.1, h y hg.2]
  | or x y => simp only [Gate.eval, h x hg.1, h y hg.2]

theorem consistent_cons (start : Nat) (g : Gate) (gs : List Gate) (A : Nat → Bool) :
    Consistent start (g :: gs) A ↔ A start = g.eval A ∧ Consistent (start + 1) gs A := by
  unfold Consistent
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0 (by simp)
      change A (start + 0) = g.eval A at h0
      simpa only [Nat.add_zero] using h0
    · intro i hi
      have ht := h (i + 1) (by simpa using hi)
      change A (start + (i + 1)) = gs[i].eval A at ht
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  · rintro ⟨hg, hgs⟩ i hi
    cases i with
    | zero => simpa using hg
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hgs i (by simpa using hi)

theorem consistent_append (start : Nat) (gs hs : List Gate) (A : Nat → Bool) :
    Consistent start (gs ++ hs) A ↔
      Consistent start gs A ∧ Consistent (start + gs.length) hs A := by
  induction gs generalizing start with
  | nil => simp [Consistent]
  | cons g gs ih =>
    simp only [List.cons_append, consistent_cons, ih, List.length_cons]
    simp only [Nat.add_comm, Nat.add_left_comm, and_assoc]

theorem run_append (start : Nat) (gs hs : List Gate) (A : Nat → Bool) :
    run start (gs ++ hs) A = run (start + gs.length) hs (run start gs A) := by
  induction gs generalizing start A with
  | nil => simp [run]
  | cons g gs ih =>
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (start + 1) (Function.update A start (g.eval A))

theorem run_consistent (start : Nat) (gs : List Gate) (A : Nat → Bool)
    (h : Ordered start gs) : Consistent start gs (run start gs A) := by
  induction gs generalizing start A with
  | nil => exact consistent_nil start A
  | cons g gs ih =>
    rcases (ordered_cons start g gs).mp h with ⟨hg, hgs⟩
    apply (consistent_cons start g gs _).mpr
    constructor
    · have hout : run start (g :: gs) A start = g.eval A := by
        rw [run, run_eq_of_lt (start + 1) gs _ start (by omega)]
        exact Function.update_self start _ _
      rw [hout]
      exact Gate.eval_congr g hg A (run start (g :: gs) A)
        (fun j hj => (run_eq_of_lt start (g :: gs) A j hj).symm)
    · exact ih (start + 1) _ hgs

theorem run_unique (start : Nat) (gs : List Gate) (A B : Nat → Bool)
    (ho : Ordered start gs) (hc : Consistent start gs B)
    (ha : ∀ j, j < start → A j = B j) :
    ∀ j, j < start + gs.length → run start gs A j = B j := by
  induction gs generalizing start A with
  | nil =>
    intro j hj
    exact ha j (by simpa using hj)
  | cons g gs ih =>
    rcases (ordered_cons start g gs).mp ho with ⟨hg, hgs⟩
    rcases (consistent_cons start g gs B).mp hc with ⟨hb, hbs⟩
    have hnext : ∀ j, j < start + 1 →
        Function.update A start (g.eval A) j = B j := by
      intro j hj
      by_cases heq : j = start
      · subst j
        rw [Function.update_self]
        exact (Gate.eval_congr g hg A B ha).trans hb.symm
      · rw [Function.update_of_ne heq]
        exact ha j (by omega)
    intro j hj
    exact ih (start + 1) _ hgs hbs hnext j (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj)

theorem Circuit.evalWires_consistent (C : Circuit) (input : Fin C.inputs → Bool) :
    Consistent C.inputs C.gates (C.evalWires input) :=
  run_consistent C.inputs C.gates (inputEnv input) C.ordered

theorem Consistent.congr {start : Nat} {gs : List Gate} {A B : Nat → Bool}
    (hc : Consistent start gs A) (ho : Ordered start gs)
    (hab : ∀ j, j < start + gs.length → A j = B j) :
    Consistent start gs B := by
  intro i hi
  have hbound := Gate.bounded_mono gs[i] (by omega : start + i ≤ start + gs.length)
    (ho i hi)
  calc
    B (start + i) = A (start + i) := (hab _ (by omega)).symm
    _ = gs[i].eval A := hc i hi
    _ = gs[i].eval B := Gate.eval_congr gs[i] hbound A B hab

theorem gateClauses_correct {n : Nat} (output : Fin n) (g : Gate)
    (h : g.Bounded n) (A : Fin n → Bool) :
    (∀ c ∈ gateClauses output g h, c.eval A = true) ↔
      A output = g.eval (inputEnv A) := by
  cases g with
  | const b =>
    simp only [gateClauses, List.forall_mem_cons]
    cases b <;> cases ho : A output <;>
      simp [unitClause, Clause.eval, Literal.eval, Gate.eval, ho]
  | not x =>
    change x < n at h
    simp only [gateClauses, List.forall_mem_cons]
    cases ho : A output <;> cases hx : A ⟨x, h⟩ <;>
      simp [Clause.eval, Literal.eval, Gate.eval, inputEnv, h, ho, hx]
  | and x y =>
    change x < n ∧ y < n at h
    simp only [gateClauses, List.forall_mem_cons]
    cases ho : A output <;> cases hx : A ⟨x, h.1⟩ <;> cases hy : A ⟨y, h.2⟩ <;>
      simp [Clause.eval, Literal.eval, Gate.eval, inputEnv, h.1, h.2,
        ho, hx, hy]
  | or x y =>
    change x < n ∧ y < n at h
    simp only [gateClauses, List.forall_mem_cons]
    cases ho : A output <;> cases hx : A ⟨x, h.1⟩ <;> cases hy : A ⟨y, h.2⟩ <;>
      simp [Clause.eval, Literal.eval, Gate.eval, inputEnv, h.1, h.2,
        ho, hx, hy]

theorem Circuit.toFormula_satisfied_iff (C : Circuit) (A : Fin C.wires → Bool) :
    (∀ c ∈ C.toFormula.clauses, c.eval A = true) ↔
      Consistent C.inputs C.gates (inputEnv A) ∧ A C.output = true := by
  constructor
  · intro h
    constructor
    · intro i hi
      let idx : Fin C.gates.length := ⟨i, hi⟩
      have hblock : ∀ c ∈ C.gateBlock idx, c.eval A = true := by
        intro c hc
        apply h c
        apply List.mem_append.mpr
        left
        exact List.mem_flatMap.mpr ⟨idx, by simp, hc⟩
      have heq := (gateClauses_correct (C.gateOutput idx) (C.gateAt idx)
        (C.gateBounded idx) A).mp hblock
      have hlt : C.inputs + i < C.wires := by simp only [Circuit.wires]; omega
      simpa [inputEnv, hlt, Circuit.gateOutput, Circuit.gateAt, idx] using heq
    · have hu := h (unitClause C.output true)
        (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      simpa [unitClause, Clause.eval, Literal.eval] using hu
  · rintro ⟨hc, ho⟩ c hmem
    rcases List.mem_append.mp hmem with hblock | hunit
    · obtain ⟨i, _, hci⟩ := List.mem_flatMap.mp hblock
      apply (gateClauses_correct (C.gateOutput i) (C.gateAt i)
        (C.gateBounded i) A).mpr ?_ c hci
      have heq := hc i.val i.isLt
      have hlt : C.inputs + i.val < C.wires := (C.gateOutput i).isLt
      simpa [inputEnv, hlt, Circuit.gateOutput, Circuit.gateAt] using heq
    · have heq : c = unitClause C.output true := List.mem_singleton.mp hunit
      subst c
      simpa [unitClause, Clause.eval, Literal.eval] using ho

def Circuit.restrictAssignment (C : Circuit) (A : Fin C.wires → Bool) :
    Fin C.inputs → Bool := fun j =>
  A ⟨j.val, by have hj := j.isLt; simp only [Circuit.wires]; omega⟩

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

open Turing
open StackEncoding BoundedExecution

namespace Expr

variable {ι : Type*}

theorem eval_congr (e : Expr ι) (u v : ι → Bool) (h : ∀ i, u i = v i) :
    e.eval u = e.eval v := by
  have : u = v := funext h
  rw [this]

theorem consistent_singleton (start : Nat) (g : Gate) (A : Nat → Bool)
    (h : Consistent start [g] A) : A start = g.eval A := by
  exact ((consistent_cons start g [] A).mp h).1

theorem eval_of_consistent (e : Expr ι) (wire : ι → Nat) (start : Nat)
    (A : Nat → Bool) (h : Consistent start (e.gates wire start) A) :
    A (e.root start) = e.eval (fun i => A (wire i)) := by
  induction e generalizing start with
  | input i =>
    simpa [gates, root, size, Gate.eval, eval] using
      consistent_singleton start (.or (wire i) (wire i)) A h
  | const b =>
    simpa [gates, root, size, Gate.eval, eval] using
      consistent_singleton start (.const b) A h
  | not e ih =>
    obtain ⟨he, hg⟩ := (consistent_append start _ _ A).mp h
    simp only [gates_length] at hg
    have hg' := consistent_singleton _ _ _ hg
    simpa only [root_not, Gate.eval, eval, ih start he] using hg'
  | and e f ihe ihf =>
    obtain ⟨hef, hg⟩ := (consistent_append start _ _ A).mp h
    obtain ⟨he, hf⟩ := (consistent_append start _ _ A).mp hef
    simp only [gates_length] at hf
    simp only [List.length_append, gates_length] at hg
    have hg' := consistent_singleton _ _ _ hg
    have he' := ihe start he
    have hf' := ihf (start + e.size) hf
    simpa only [root_and, Gate.eval, eval,
      he', hf'] using hg'
  | or e f ihe ihf =>
    obtain ⟨hef, hg⟩ := (consistent_append start _ _ A).mp h
    obtain ⟨he, hf⟩ := (consistent_append start _ _ A).mp hef
    simp only [gates_length] at hf
    simp only [List.length_append, gates_length] at hg
    have hg' := consistent_singleton _ _ _ hg
    have he' := ihe start he
    have hf' := ihf (start + e.size) hf
    simpa only [root_or, Gate.eval, eval,
      he', hf'] using hg'

theorem eval_disjoin_true (input : ι → Bool) (es : List (Expr ι)) :
    (disjoin es).eval input = true ↔ ∃ e ∈ es, e.eval input = true := by
  induction es with
  | nil => simp [disjoin, eval]
  | cons e es ih => simp [disjoin, eval, ih]

theorem size_disjoin_le (es : List (Expr ι)) (C : Nat)
    (h : ∀ e ∈ es, e.size ≤ C) : (disjoin es).size ≤ es.length * (C + 1) + 1 := by
  induction es generalizing C with
  | nil => simp [disjoin, size]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih C (fun f hf => h f (by simp [hf]))
    simp only [disjoin, size, List.length_cons, Nat.succ_mul]
    omega

end Expr

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem eval_table {ι A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (input : ι → Bool) (f : A → B) (x : A → Expr ι) (a : A)
    (hx : ∀ z, (x z).eval input = decide (a = z)) (b : B) :
    (table f x b).eval input = decide (f a = b) := by
  apply bool_ext
  simp only [table, Expr.eval_disjoin_true, List.mem_map]
  constructor
  · rintro ⟨_, ⟨z, _, rfl⟩, hz⟩
    simp only [Expr.eval, hx, Bool.and_eq_true, decide_eq_true_eq] at hz
    rcases hz with ⟨rfl, hz⟩
    exact decide_eq_true hz
  · intro h
    refine ⟨.and (x a) (.const (decide (f a = b))), ?_, ?_⟩
    · exact ⟨a, by simp, rfl⟩
    · simp [Expr.eval, hx, h]

theorem eval_table₂ {ι A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (input : ι → Bool) (f : A → B → C) (x : A → Expr ι) (y : B → Expr ι)
    (a : A) (b : B) (hx : ∀ z, (x z).eval input = decide (a = z))
    (hy : ∀ z, (y z).eval input = decide (b = z)) (c : C) :
    (table₂ f x y c).eval input = decide (f a b = c) := by
  apply eval_table input _ _ (a, b)
  rintro ⟨za, zb⟩
  simp [Expr.eval, hx, hy, Prod.mk.injEq]

theorem size_table_le {ι A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (x : A → Expr ι) (b : B) (C : Nat) (h : ∀ a, (x a).size ≤ C) :
    (table f x b).size ≤ Fintype.card A * (C + 3) + 1 := by
  unfold table
  have hb : ∀ e ∈ Finset.univ.toList.map (fun a => Expr.and (x a)
      (.const (decide (f a = b)))), e.size ≤ C + 2 := by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
    simpa only [Expr.size, Nat.add_assoc] using Nat.add_le_add_right (h a) 2
  simpa [Nat.add_assoc] using Expr.size_disjoin_le _ (C + 2) hb

theorem size_table₂_le {ι A B D : Type*} [Fintype A] [Fintype B] [DecidableEq D]
    (f : A → B → D) (x : A → Expr ι) (y : B → Expr ι) (d : D) (C : Nat)
    (hx : ∀ a, (x a).size ≤ C) (hy : ∀ b, (y b).size ≤ C) :
    (table₂ f x y d).size ≤ (Fintype.card A * Fintype.card B) * (2 * C + 4) + 1 := by
  have h := size_table_le (fun p : A × B => f p.1 p.2)
    (fun p => Expr.and (x p.1) (y p.2)) d (2 * C + 1) (fun p => by
      have := hx p.1
      have := hy p.2
      simp only [Expr.size]
      omega)
  simpa only [table₂, Fintype.card_prod, Nat.add_assoc] using h

end BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitEncodingBridge
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

open Turing
open BinPackingGames.Foundations.Hastad
open BinPackingGames.Reduction

def Record.slot (r : Record) (j : Fin 3) : Nat :=
  match j.val with
  | 0 => r.output
  | 1 => r.first
  | _ => r.second

def Record.fieldValue (r : Record) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => r.tag.val
  | 1 => r.output
  | 2 => r.first
  | _ => r.second

def Record.outputWords (r : Record) : List Nat := templateWords r.tag r.slot
def Record.outputBits (r : Record) : List Bool := encodeWords r.outputWords

def headerTape (slot : Fin 3) : Tape :=
  match slot.val with
  | 0 => .header
  | 1 => .counter
  | _ => .selected

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

def literalEmit (positive : Bool) : Bool → List Bool
  | true => [true]
  | false => [false] ++ encodeWord (if positive then 1 else 0)

def emission : Context → Bool → List Bool
  | .header j => if j.val = 0 then affineEmit 1 0 else affineEmit 3 1
  | .gate tag j => literalEmit (gateTemplate tag j).2
  | .output _ => literalEmit true

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

namespace BinPackingGames.Foundations.Complexity.CookLevin

open CircuitProducerModel

def circuitBits (C : Circuit) : List Bool := encodeWords (circuitWords C)

theorem gateRecord_fields_le (start bound : Nat) (g : Gate)
    (hs : start ≤ bound) (hg : g.Bounded bound) :
    ∀ n ∈ (gateRecord start g).words, n ≤ bound + 4 := by
  cases g with
  | const b => cases b <;> simp [gateRecord, Record.words] <;> omega
  | not a => simp [gateRecord, Record.words, Gate.Bounded] at *; omega
  | and a b => simp [gateRecord, Record.words, Gate.Bounded] at *; omega
  | or a b => simp [gateRecord, Record.words, Gate.Bounded] at *; omega

theorem gateRecords_fields_le (start : Nat) (gs : List Gate) (ho : Ordered start gs) :
    ∀ n ∈ recordsWords (gateRecords start gs), n ≤ start + gs.length + 4 := by
  induction gs generalizing start with
  | nil => simp [gateRecords, recordsWords]
  | cons g gs ih =>
      rcases (ordered_cons start g gs).mp ho with ⟨hg, hgs⟩
      intro n hn
      rw [gateRecords, recordsWords_cons, List.mem_append] at hn
      rcases hn with hn | hn
      · have h := gateRecord_fields_le start start g (Nat.le_refl _) hg n hn
        simp only [List.length_cons]
        omega
      · have h := ih (start + 1) hgs n hn
        simp only [List.length_cons]
        omega

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

open Turing
open BinPackingGames.Reduction
open CircuitProducerModel

theorem contextSource_ne_scratch (context : Context) :
    contextSource context ≠ Tape.scratch := by
  cases context with
  | header slot => simp only [contextSource]; split <;> simp
  | gate tag position => simp [contextSource]
  | output position => simp [contextSource]

theorem contextSource_ne_reversed (context : Context) :
    contextSource context ≠ Tape.reversed := by
  cases context with
  | header slot => simp only [contextSource]; split <;> simp
  | gate tag position => simp [contextSource]
  | output position => simp [contextSource]

def contextOutput (context : Context) (base : Tape → List Bool) : List Bool :=
  MachineTransducer.output (fun control _ => control) emission
    context (base (contextSource context))

def contextTapes (context : Context) (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .reversed ((contextOutput context base).reverse ++ base .reversed)

@[simp] theorem contextTapes_other (context : Context) (base : Tape → List Bool)
    (tape : Tape) (different : tape ≠ .reversed) :
    contextTapes context base tape = base tape := by
  simp [contextTapes, different]

@[simp] theorem contextTapes_source (context other : Context) (base : Tape → List Bool) :
    contextTapes context base (contextSource other) = base (contextSource other) :=
  contextTapes_other context base _ (contextSource_ne_reversed other)

@[simp] theorem contextTapes_scratch (context : Context) (base : Tape → List Bool) :
    contextTapes context base .scratch = base .scratch :=
  contextTapes_other context base _ (by decide)

@[simp] theorem contextOutput_update (context : Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextOutput context (Function.update base .reversed out) = contextOutput context base := by
  simp [contextOutput, contextSource_ne_reversed]

@[simp] theorem contextSteps_update (context : Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextSteps context (Function.update base .reversed out) = contextSteps context base := by
  simp [contextSteps, contextSource_ne_reversed]

theorem output_eq_flatMap (context : Context) (input : List Bool) :
    MachineTransducer.output (fun control _ => control) emission context input =
      input.flatMap (emission context) := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

theorem literalEmit_word (positive : Bool) (value : Nat) :
    (encodeWord value).flatMap (literalEmit positive) =
      encodeWords [value, if positive then 1 else 0] := by
  induction value with
  | zero => simp [encodeWord, encodeWords, literalEmit]
  | succ value ih =>
    simpa [encodeWord, encodeWords, List.replicate_succ, literalEmit] using
      congrArg (List.cons true) ih

theorem affineEmit_word (scale offset value : Nat) :
    (encodeWord value).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * value) := by
  have hrep : (List.replicate value true).flatMap (affineEmit scale offset) =
      List.replicate (scale * value) true := by
    rw [List.flatMap_replicate]
    change (List.replicate value (List.replicate scale true)).flatten = _
    rw [List.flatten_replicate_replicate, Nat.mul_comm value scale]
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, hrep, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * value) offset]

def contextWords (context : Context) (value : Nat) : List Nat :=
  match context with
  | .header j => if j.val = 0 then [value] else [3 * value + 1]
  | .gate tag j => [value, if (gateTemplate tag j).2 then 1 else 0]
  | .output _ => [value, 1]

theorem output_word (context : Context) (value : Nat) :
    MachineTransducer.output (fun control _ => control) emission context (encodeWord value) =
      encodeWords (contextWords context value) := by
  rw [output_eq_flatMap]
  cases context with
  | header j =>
    by_cases hj : j.val = 0 <;>
      simp [emission, contextWords, hj, affineEmit_word, encodeWords, Nat.add_comm]
  | gate tag j => exact literalEmit_word (gateTemplate tag j).2 value
  | output j => simpa [emission, contextWords] using literalEmit_word true value

def contextListOutput (contexts : List Context) (base : Tape → List Bool) : List Bool :=
  contexts.flatMap (fun context => contextOutput context base)

def contextListSteps (contexts : List Context) (base : Tape → List Bool) : Nat :=
  (contexts.map (fun context => contextSteps context base)).sum

def contextListStart (contexts : List Context) (exit : Option Label) : Option Label :=
  match contexts with
  | [] => exit
  | context :: _ => some (.setup context)

def ContextListLinked : List Context → Option Label → Prop
  | [], _ => True
  | context :: rest, exit =>
    contextNext context = contextListStart rest exit ∧ ContextListLinked rest exit

@[simp] theorem contextListOutput_update (contexts : List Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextListOutput contexts (Function.update base .reversed out) = contextListOutput contexts base := by
  simp [contextListOutput]

@[simp] theorem contextListSteps_update (contexts : List Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextListSteps contexts (Function.update base .reversed out) = contextListSteps contexts base := by
  simp [contextListSteps]

def gateContexts (tag : Fin 5) : List Context :=
  (List.finRange 9).map (Context.gate tag)

def outputContexts : List Context := [.output 0, .output 1, .output 2]

theorem gateContexts_linked (tag : Fin 5) :
    ContextListLinked (gateContexts tag) (some (.cleanup 0)) := by
  simp [gateContexts, List.finRange, List.ofFn_succ, ContextListLinked,
    contextListStart, contextNext]

theorem outputContexts_linked :
    ContextListLinked outputContexts (some .finalCounter) := by
  simp [outputContexts, ContextListLinked, contextListStart, contextNext]

theorem contextOutput_gate_word (record : Record) (position : Fin 9)
    (base : Tape → List Bool)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    contextOutput (.gate record.tag position) base = encodeWords
      [record.slot (gateTemplate record.tag position).1,
        if (gateTemplate record.tag position).2 then 1 else 0] := by
  have fields (slot : Fin 3) :
      base (.field ⟨slot.val + 1, by omega⟩) = encodeWord (record.slot slot) := by
    have slotCases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
    rcases slotCases with h | h | h
    · simpa [Record.slot, h] using h1
    · simpa [Record.slot, h] using h2
    · simpa [Record.slot, h] using h3
  unfold contextOutput
  rw [show base (contextSource (.gate record.tag position)) =
      encodeWord (record.slot (gateTemplate record.tag position).1) from fields _]
  exact output_word (.gate record.tag position) _

theorem encodeWords_flatMap {A : Type*} (items : List A) (words : A → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem gateOutput_words (record : Record) (base : Tape → List Bool)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    contextListOutput (gateContexts record.tag) base = record.outputBits := by
  simp only [contextListOutput, gateContexts, List.flatMap_map,
    Record.outputBits, Record.outputWords, templateWords, encodeWords_flatMap]
  congr 1
  funext position
  exact contextOutput_gate_word record position base h1 h2 h3

def gateSteps (record : Record) : Nat :=
  ((List.finRange 9).map fun position =>
    3 * (record.slot (gateTemplate record.tag position).1 + 1) + 3).sum

theorem gateSteps_eq (record : Record) (base : Tape → List Bool)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    contextListSteps (gateContexts record.tag) base = gateSteps record := by
  have fields (slot : Fin 3) :
      base (.field ⟨slot.val + 1, by omega⟩) = encodeWord (record.slot slot) := by
    have slotCases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
    rcases slotCases with h | h | h
    · simpa [Record.slot, h] using h1
    · simpa [Record.slot, h] using h2
    · simpa [Record.slot, h] using h3
  simp only [contextListSteps, gateContexts, List.map_map, gateSteps]
  congr 2
  funext position
  simp only [Function.comp_apply, contextSteps, contextSource, fields, encodeWord_length]

theorem slot_le_sum (record : Record) (slot : Fin 3) :
    record.slot slot ≤ record.output + record.first + record.second := by
  unfold Record.slot
  split <;> omega

theorem sum_map_le_length_mul {A : Type*} (items : List A)
    (value : A → Nat) (bound : Nat) (bounded : ∀ item ∈ items, value item ≤ bound) :
    (items.map value).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have head := bounded item (by simp)
    have tail := ih (fun a ha => bounded a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem gateSteps_le (record : Record) :
    gateSteps record ≤ 27 * (record.output + record.first + record.second) + 54 := by
  have bound := sum_map_le_length_mul (List.finRange 9)
    (fun position => 3 * (record.slot (gateTemplate record.tag position).1 + 1) + 3)
    (3 * (record.output + record.first + record.second) + 6) (by
      intro position _
      have := slot_le_sum record (gateTemplate record.tag position).1
      omega)
  simp only [List.length_finRange] at bound
  unfold gateSteps
  omega

theorem length_flatMap_le_length_mul {A : Type*} (items : List A)
    (word : A → List Bool) (bound : Nat) (bounded : ∀ item ∈ items, (word item).length ≤ bound) :
    (items.flatMap word).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have head := bounded item (by simp)
    have tail := ih (fun a ha => bounded a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

theorem outputBits_length_le (record : Record) :
    record.outputBits.length ≤ 9 * (record.output + record.first + record.second) + 27 := by
  have bound := length_flatMap_le_length_mul (List.finRange 9)
    (fun position => encodeWords
      [record.slot (gateTemplate record.tag position).1,
        if (gateTemplate record.tag position).2 then 1 else 0])
    (record.output + record.first + record.second + 3) (by
      intro position _
      have index := slot_le_sum record (gateTemplate record.tag position).1
      have sign : (if (gateTemplate record.tag position).2 then 1 else 0 : Nat) ≤ 1 := by
        split <;> omega
      simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
      omega)
  simp only [List.length_finRange] at bound
  unfold Record.outputBits Record.outputWords templateWords
  rw [encodeWords_flatMap]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixModel

namespace Token

def takeGate : Token → List Nat → Option (Gate × List Nat)
  | .const value, roots => some (.const value, roots)
  | .input wire, roots => some (.or wire wire, roots)
  | .not, arg :: roots => some (.not arg, roots)
  | .and, right :: left :: roots => some (.and left right, roots)
  | .or, right :: left :: roots => some (.or left right, roots)
  | _, _ => none

end Token

def compileTokens (start : Nat) (roots : List Nat) :
    List Token → Option (Nat × List Nat × List Gate)
  | [] => some (start, roots, [])
  | token :: tokens => do
      let (gate, remaining) ← token.takeGate roots
      let (next, finalRoots, gates) ← compileTokens (start + 1) (start :: remaining) tokens
      pure (next, finalRoots, gate :: gates)

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixModel

namespace BinPackingGames.Foundations.Complexity.CookLevin

open Target CircuitProducerModel

@[simp] theorem unitClause_words {n : Nat} (output : Fin n) :
    clauseWords (unitClause output true) = outputWords output.val := rfl

theorem gateRecords_outputWords (start : Nat) (gs : List Gate) :
    (List.finRange gs.length).flatMap
        (fun i => (gateRecord (start + i.val) gs[i.val]).outputWords) =
      (gateRecords start gs).flatMap Record.outputWords := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    change (List.finRange (gs.length + 1)).flatMap
      (fun i => (gateRecord (start + i.val) (g :: gs)[i.val]).outputWords) = _
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    change (gateRecord start g).outputWords ++
        (List.finRange gs.length).flatMap
          (fun i => (gateRecord (start + (i.val + 1)) gs[i.val]).outputWords) =
      (gateRecord start g).outputWords ++
        (gateRecords (start + 1) gs).flatMap Record.outputWords
    apply congrArg ((gateRecord start g).outputWords ++ ·)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (start + 1)

end BinPackingGames.Foundations.Complexity.CookLevin

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_MachineCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.MachineCircuit

open Turing StatementCircuit BoundedExecution
open scoped BigOperators

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
variable [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]

omit [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ stack, Fintype (Γ stack)] in
theorem configEncoding_injective (S : Nat) (first second : TM2.Cfg Γ Λ σ)
    (hfirst : ∀ k, (first.stk k).length ≤ S)
    (hsecond : ∀ k, (second.stk k).length ≤ S)
    (same : configEncoding S first = configEncoding S second) : first = second := by
  have hl : first.l = second.l := by
    have h := congrFun same (.inl second.l)
    simpa only [configEncoding, decide_true, decide_eq_true_eq] using h
  have hv : first.var = second.var := by
    have h := congrFun same (.inr (.inl second.var))
    simpa only [configEncoding, inputEncoding, decide_true, decide_eq_true_eq] using h
  have ht : first.stk = second.stk := by
    funext k
    apply StackEncoding.encode_injective (hfirst k) (hsecond k)
    funext i
    have h := congrFun same (.inr (.inr ⟨k, i, StackEncoding.encode S (second.stk k) i⟩))
    simpa only [configEncoding, inputEncoding, decide_true, decide_eq_true_eq] using h
  cases first
  cases second
  simp only at hl hv ht
  cases hl
  cases hv
  cases ht
  rfl

end BinPackingGames.Foundations.Complexity.CookLevin.MachineCircuit

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_OutputOrder
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch

open StatementCircuit

namespace Batch

variable {ι : Type*}

theorem eval_roots (wire : ι → Nat) (start : Nat) (es : List (Expr ι))
    (A : Nat → Bool) (hc : Consistent start (gates wire start es) A) :
    (roots start es).map A = es.map (fun e => e.eval (fun i => A (wire i))) := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨he, ht⟩ := (consistent_append start _ _ A).mp hc
    simp only [Expr.gates_length] at ht
    simp only [roots, List.map_cons, e.eval_of_consistent wire start A he,
      ih (start + e.size) ht]

theorem eval_rootAt (wire : ι → Nat) (start : Nat) (es : List (Expr ι))
    (A : Nat → Bool) (hc : Consistent start (gates wire start es) A)
    (i : Fin es.length) :
    A (rootAt start es i) = es[i.val].eval (fun j => A (wire j)) := by
  have h := congrArg (fun xs : List Bool => xs[i.val]?) (eval_roots wire start es A hc)
  have hr : i.val < (roots start es).length := by simp
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hr,
    List.getElem?_eq_getElem i.isLt, Option.map_some, Option.some.injEq, rootAt] using h

theorem cost_le (es : List (Expr ι)) (D : Nat)
    (h : ∀ e ∈ es, e.size ≤ D) : cost es ≤ es.length * D := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun f hf => h f (by simp [hf]))
    simp only [cost_cons, List.length_cons, Nat.succ_mul]
    omega

theorem cost_ofFn {n : Nat} (es : Fin n → Expr ι) :
    cost (List.ofFn es) = ∑ i, (es i).size := by
  simp [cost, List.map_ofFn, List.sum_ofFn]

theorem cost_ofFn_le {n : Nat} (es : Fin n → Expr ι) (D : Nat)
    (h : ∀ i, (es i).size ≤ D) : cost (List.ofFn es) ≤ n * D := by
  have hc := cost_le (List.ofFn es) D (by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact h i)
  simpa only [List.length_ofFn] using hc

end Batch

namespace Fragment

variable {inputs : Nat}

theorem evalWires_consistent (f : Fragment inputs) (input : Fin inputs → Bool) :
    Consistent inputs f.gates (f.evalWires input) :=
  run_consistent inputs f.gates (inputEnv input) f.ordered

theorem evalWires_append (f : Fragment inputs) (gs : List Gate)
    (hg : Ordered (inputs + f.gates.length) gs) (input : Fin inputs → Bool) :
    (f.append gs hg).evalWires input =
      run (inputs + f.gates.length) gs (f.evalWires input) :=
  run_append inputs f.gates gs (inputEnv input)

theorem evalWires_append_old (f : Fragment inputs) (gs : List Gate)
    (hg : Ordered (inputs + f.gates.length) gs) (input : Fin inputs → Bool)
    (j : Nat) (hj : j < inputs + f.gates.length) :
    (f.append gs hg).evalWires input j = f.evalWires input j := by
  rw [evalWires_append]
  exact run_eq_of_lt _ _ _ j hj

end Fragment

namespace Frame

variable {inputs width oldWidth newWidth : Nat}

theorem step_eval (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (input : Fin inputs → Bool) (i : Fin newWidth) :
    (f.step es).eval input i = (es i).eval (f.eval input) := by
  let start := inputs + f.fragment.gates.length
  let wire := fun j : Fin oldWidth => (f.wires j).val
  let gs := Batch.gates wire start (List.ofFn es)
  have hc : Consistent start gs ((f.step es).fragment.evalWires input) :=
    ((consistent_append inputs f.fragment.gates gs _).mp
      ((f.step es).fragment.evalWires_consistent input)).2
  have he := Batch.eval_rootAt wire start (List.ofFn es)
    ((f.step es).fragment.evalWires input) hc
    ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
  change (f.step es).eval input i = _ at he
  rw [he]
  simp only [List.getElem_ofFn]
  apply Expr.eval_congr
  intro j
  exact f.fragment.evalWires_append_old gs
    (Batch.gates_ordered wire start _ (fun j => (f.wires j).isLt))
    input (f.wires j).val (f.wires j).isLt

theorem step_eval_fun (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (input : Fin inputs → Bool) :
    (f.step es).eval input = fun i => (es i).eval (f.eval input) := by
  funext i
  exact step_eval f es input i

def network (es : Fin width → Expr (Fin width)) (state : Fin width → Bool) :
    Fin width → Bool := fun i => (es i).eval state

end Frame

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixAlignment

open StatementCircuit CircuitBatch PostfixModel

variable {ι : Type*}

theorem compileTokens_append
    (start : Nat) (roots : List Nat) (first rest : List Token)
    (middle : Nat) (middleRoots : List Nat) (firstGates : List Gate)
    (finish : Nat) (finalRoots : List Nat) (lastGates : List Gate)
    (hfirst : compileTokens start roots first = some (middle, middleRoots, firstGates))
    (hrest : compileTokens middle middleRoots rest = some (finish, finalRoots, lastGates)) :
    compileTokens start roots (first ++ rest) =
      some (finish, finalRoots, firstGates ++ lastGates) := by
  induction first generalizing start roots middle middleRoots firstGates with
  | nil =>
    simp only [compileTokens, Option.some.injEq, Prod.mk.injEq] at hfirst
    rcases hfirst with ⟨rfl, rfl, rfl⟩
    simpa only [List.nil_append] using hrest
  | cons token tokens ih =>
    cases hg : token.takeGate roots with
    | none => simp [compileTokens, hg] at hfirst
    | some pair =>
      rcases pair with ⟨gate, remaining⟩
      cases ht : compileTokens (start + 1) (start :: remaining) tokens with
      | none => simp [compileTokens, hg, ht] at hfirst
      | some triple =>
        rcases triple with ⟨next, afterRoots, tailGates⟩
        simp [compileTokens, hg, ht] at hfirst
        rcases hfirst with ⟨rfl, rfl, rfl⟩
        have hi := ih (start + 1) (start :: remaining) next afterRoots tailGates ht hrest
        simp [List.cons_append, compileTokens, hg, hi]

theorem compile_exprTokens (wire : ι → Nat) (e : Expr ι)
    (start : Nat) (roots : List Nat) :
    compileTokens start roots (exprTokens wire e) =
      some (start + e.size, e.root start :: roots, e.gates wire start) := by
  induction e generalizing start roots with
  | input i => simp [exprTokens, compileTokens, Token.takeGate, Expr.root, Expr.size, Expr.gates]
  | const b => simp [exprTokens, compileTokens, Token.takeGate, Expr.root, Expr.size, Expr.gates]
  | not e ih =>
    have hop : compileTokens (start + e.size) (e.root start :: roots) [.not] =
        some (start + e.size + 1, (start + e.size) :: roots, [.not (e.root start)]) := rfl
    have he := compileTokens_append start roots (exprTokens wire e) [.not]
      _ _ _ _ _ _ (ih start roots) hop
    simpa only [exprTokens, Expr.gates, Expr.size, Expr.root_not, Nat.add_assoc] using he
  | and e f ihe ihf =>
    have hop : compileTokens (start + e.size + f.size)
        (f.root (start + e.size) :: e.root start :: roots) [.and] =
        some (start + e.size + f.size + 1, (start + e.size + f.size) :: roots,
          [.and (e.root start) (f.root (start + e.size))]) := rfl
    have hf := compileTokens_append (start + e.size) (e.root start :: roots)
      (exprTokens wire f) [.and] _ _ _ _ _ _ (ihf _ _) hop
    have he := compileTokens_append start roots (exprTokens wire e)
      (exprTokens wire f ++ [.and]) _ _ _ _ _ _ (ihe _ _) hf
    simpa only [exprTokens, Expr.gates, Expr.size, Expr.root_and, Nat.add_assoc,
      List.append_assoc] using he
  | or e f ihe ihf =>
    have hop : compileTokens (start + e.size + f.size)
        (f.root (start + e.size) :: e.root start :: roots) [.or] =
        some (start + e.size + f.size + 1, (start + e.size + f.size) :: roots,
          [.or (e.root start) (f.root (start + e.size))]) := rfl
    have hf := compileTokens_append (start + e.size) (e.root start :: roots)
      (exprTokens wire f) [.or] _ _ _ _ _ _ (ihf _ _) hop
    have he := compileTokens_append start roots (exprTokens wire e)
      (exprTokens wire f ++ [.or]) _ _ _ _ _ _ (ihe _ _) hf
    simpa only [exprTokens, Expr.gates, Expr.size, Expr.root_or, Nat.add_assoc,
      List.append_assoc] using he

theorem compile_forestTokens (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) :
    compileTokens start roots (forestTokens wire es) =
      some (start + Batch.cost es, (Batch.roots start es).reverse ++ roots,
        Batch.gates wire start es) := by
  induction es generalizing start roots with
  | nil => simp [forestTokens, compileTokens, Batch.cost, Batch.roots, Batch.gates]
  | cons e es ih =>
    have h := compileTokens_append start roots (exprTokens wire e) (forestTokens wire es)
      _ _ _ _ _ _ (compile_exprTokens wire e start roots)
      (ih (start + e.size) (e.root start :: roots))
    simpa only [forestTokens_cons, Batch.cost_cons, Batch.roots, Batch.gates,
      List.reverse_cons, List.append_assoc, List.singleton_append, Nat.add_assoc] using h

theorem exprTokens_member (wire : ι → Nat) (e : Expr ι) (t : Token)
    (h : t ∈ exprTokens wire e) :
    (∃ b, t = .const b) ∨ t = .not ∨ t = .and ∨ t = .or ∨
      ∃ i, t = .input (wire i) := by
  induction e with
  | input i =>
    have ht : t = .input (wire i) := by simpa only [exprTokens, List.mem_singleton] using h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, ht⟩)))
  | const b =>
    have ht : t = .const b := by simpa only [exprTokens, List.mem_singleton] using h
    exact Or.inl ⟨b, ht⟩
  | not e ih =>
    simp only [exprTokens, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact ih h
    · exact Or.inr (Or.inl rfl)
  | and e f ihe ihf =>
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at h
    rcases h with h | h | rfl
    · exact ihe h
    · exact ihf h
    · exact Or.inr (Or.inr (Or.inl rfl))
  | or e f ihe ihf =>
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at h
    rcases h with h | h | rfl
    · exact ihe h
    · exact ihf h
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixAlignment

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

open Turing StatementCircuit

variable {K : Type} (Γ : K → Type) (σ : Type)

variable {Γ σ} [∀ k, DecidableEq (Γ k)]

structure Data where
  state : σ → Term Γ σ
  cells : ∀ k, Position → Option (Γ k) → Term Γ σ

structure Result (Λ : Type) extends Data (Γ := Γ) (σ := σ) where
  label : Option Λ → Term Γ σ

def initial : Data (Γ := Γ) (σ := σ) where
  state := Term.state
  cells := Term.cell

def read (bits : Data (Γ := Γ) (σ := σ)) (k : K) (p : Position) (a : Option (Γ k)) :
    Term Γ σ :=
  .within p (bits.cells k p a) (.const (decide ((none : Option (Γ k)) = a)))

variable {Λ : Type} [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [DecidableEq Λ]

noncomputable def push (bits : Data (Γ := Γ) (σ := σ)) (k : K) (f : σ → Γ k) :
    Data (Γ := Γ) (σ := σ) where
  state := bits.state
  cells := Function.update bits.cells k (fun p a =>
    .atZero p (finiteTable (fun v => some (f v)) bits.state a) (bits.cells k (.pred p) a))

noncomputable def peek (bits : Data (Γ := Γ) (σ := σ)) (k : K)
    (f : σ → Option (Γ k) → σ) : Data (Γ := Γ) (σ := σ) where
  state := finiteTable₂ f bits.state (read bits k .zero)
  cells := bits.cells

noncomputable def pop (bits : Data (Γ := Γ) (σ := σ)) (k : K)
    (f : σ → Option (Γ k) → σ) : Data (Γ := Γ) (σ := σ) where
  state := finiteTable₂ f bits.state (read bits k .zero)
  cells := Function.update bits.cells k (fun p a => read bits k (.succ p) a)

noncomputable def load (bits : Data (Γ := Γ) (σ := σ)) (f : σ → σ) :
    Data (Γ := Γ) (σ := σ) where
  state := finiteTable f bits.state
  cells := bits.cells

def mux (condition : Term Γ σ) (yes no : Result (Γ := Γ) (σ := σ) Λ) :
    Result (Γ := Γ) (σ := σ) Λ where
  state := fun v => .mux condition (yes.state v) (no.state v)
  cells := fun k p a => .mux condition (yes.cells k p a) (no.cells k p a)
  label := fun l => .mux condition (yes.label l) (no.label l)

noncomputable def compile : TM2.Stmt Γ Λ σ → Data (Γ := Γ) (σ := σ) →
    Result (Γ := Γ) (σ := σ) Λ
  | .push k f next, bits => compile next (push bits k f)
  | .peek k f next, bits => compile next (peek bits k f)
  | .pop k f next, bits => compile next (pop bits k f)
  | .load f next, bits => compile next (load bits f)
  | .branch guard yes no, bits =>
      mux (finiteTable guard bits.state true) (compile yes bits) (compile no bits)
  | .goto label, bits =>
      { toData := bits, label := finiteTable (fun v => some (label v)) bits.state }
  | .halt, bits =>
      { toData := bits, label := fun l => .const (decide ((none : Option Λ) = l)) }

def bitKind {S : Nat} : ConfigBit Γ Λ σ S → OutputKind Γ Λ σ
  | .inl l => .inl l
  | .inr (.inl v) => .inr (.inl v)
  | .inr (.inr ⟨k, _, a⟩) => .inr (.inr ⟨k, a⟩)

def bitCursor {S : Nat} : ConfigBit Γ Λ σ S → Nat
  | .inl _ | .inr (.inl _) => 0
  | .inr (.inr ⟨_, i, _⟩) => i.val

def select (bits : Result (Γ := Γ) (σ := σ) Λ) : OutputKind Γ Λ σ → Term Γ σ
  | .inl l => bits.label l
  | .inr (.inl v) => bits.state v
  | .inr (.inr ⟨k, a⟩) => bits.cells k .current a

noncomputable def transition (stmt : TM2.Stmt Γ Λ σ) (kind : OutputKind Γ Λ σ) : Term Γ σ :=
  select (compile stmt initial) kind

def self : OutputKind Γ Λ σ → Global (Γ := Γ) (Λ := Λ) (σ := σ)
  | .inl l => .label l
  | .inr (.inl v) => .data (.state v)
  | .inr (.inr ⟨k, a⟩) => .data (.cell k .current a)

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] in
theorem self_instantiate (S : Nat) (bit : ConfigBit Γ Λ σ S) :
    (self (bitKind bit)).instantiate S (bitCursor bit) = .input bit := by
  rcases bit with l | (v | ⟨k, i, a⟩)
  · rfl
  · rfl
  · simp [self, bitKind, bitCursor, Global.instantiate, Term.instantiate,
      Position.eval, i.isLt, Expr.rename]

variable [Fintype Λ]

noncomputable def sticky (program : Λ → TM2.Stmt Γ Λ σ) (kind : OutputKind Γ Λ σ) :
    Global (Γ := Γ) (Λ := Λ) (σ := σ) :=
  .or (.and (.label none) (self kind))
    (Global.disjoin (Finset.univ.toList.map fun l =>
      .and (.label (some l)) (.data (transition (program l) kind))))

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierCircuit
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin

theorem NPVerifier.input_time_le_horizon (verifier : NPVerifier)
    (input witness : List Bool)
    (bounded : witness.length ≤ verifier.witnessBound.eval input.length) :
    verifier.computation.time.eval (pairBits (input, witness)).length ≤
      verifier.horizon input.length := by
  apply MachineComposition.natPolynomial_eval_mono
  rw [pairBits_length]
  exact Nat.add_le_add_right (Nat.add_le_add_left bounded _) _

def NPVerifier.runWithinHorizon (verifier : NPVerifier)
    (input witness : List Bool)
    (bounded : witness.length ≤ verifier.witnessBound.eval input.length) :
    Turing.TM2OutputsInTime verifier.computation.tm
      ((pairBits (input, witness)).map verifier.computation.inputAlphabet.invFun)
      (some ([verifier.verify (input, witness)].map verifier.computation.outputAlphabet.invFun))
      (verifier.horizon input.length) where
  toEvalsTo := (verifier.computation.outputsFun (input, witness)).toEvalsTo
  steps_le_m := Nat.le_trans
    (verifier.computation.outputsFun (input, witness)).steps_le_m
    (verifier.input_time_le_horizon input witness bounded)

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding

open scoped BigOperators

def Valid {q : Nat} (bits : Bits q) : Prop :=
  ∃ length : Fin (q + 1), ∀ i, selector bits i = decide (i = length)

theorem valid_iff_local {q : Nat} (bits : Bits q) :
    Valid bits ↔
      (∃ i, selector bits i = true) ∧
      (∀ i j, selector bits i = true → selector bits j = true → i = j) := by
  constructor
  · rintro ⟨length, h⟩
    refine ⟨⟨length, by simp [h]⟩, ?_⟩
    intro i j hi hj
    have hil : i = length := by simpa [h] using hi
    have hjl : j = length := by simpa [h] using hj
    exact hil.trans hjl.symm
  · rintro ⟨⟨length, hl⟩, hu⟩
    refine ⟨length, fun i => ?_⟩
    by_cases hi : i = length
    · subst i; simp [hl]
    · have hf : selector bits i = false := by
        cases hbi : selector bits i
        · rfl
        · exact False.elim (hi (hu i length hbi hl))
      simp [hi, hf]

theorem decode_length_le {q : Nat} (bits : Bits q) : (decode bits).length ≤ q := by
  simp [decode]

theorem encode_valid (q : Nat) (witness : List Bool) (h : witness.length ≤ q) :
    Valid (encode q witness h) :=
  ⟨⟨witness.length, by omega⟩, selector_encode q witness h⟩

theorem exists_valid_iff (q : Nat) (P : List Bool → Prop) :
    (∃ bits : Bits q, Valid bits ∧ P (decode bits)) ↔
      ∃ witness : List Bool, witness.length ≤ q ∧ P witness := by
  constructor
  · rintro ⟨bits, _, hp⟩
    exact ⟨decode bits, decode_length_le bits, hp⟩
  · rintro ⟨witness, h, hp⟩
    exact ⟨encode q witness h, encode_valid q witness h, by simpa using hp⟩

def present {q : Nat} (bits : Bits q) (n : Nat) : Bool :=
  decide (∃ length : Fin (q + 1), selector bits length = true ∧ n < length.val)

theorem present_eq {q : Nat} (bits : Bits q) (length : Fin (q + 1))
    (h : ∀ i, selector bits i = decide (i = length)) (n : Nat) :
    present bits n = decide (n < length.val) := by
  simp [present, h]

def witnessCell {q : Nat} (bits : Bits q) (n : Nat) : Option Bool :=
  if h : n < q then
    if present bits n then some (payload bits ⟨n, h⟩) else none
  else none

theorem witnessCell_eq_getElem? {q : Nat} (bits : Bits q) (hv : Valid bits) (n : Nat) :
    witnessCell bits n = (decode bits)[n]? := by
  obtain ⟨length, h⟩ := hv
  simp only [witnessCell, decode, selectedLength_eq bits length h,
    present_eq bits length h, List.getElem?_take, List.getElem?_ofFn]
  by_cases hnq : n < q <;> by_cases hnl : n < length.val <;> simp [hnq, hnl]

theorem pairBits_decode_length_le {q : Nat} (input : List Bool) (bits : Bits q) :
    (pairBits (input, decode bits)).length ≤ 2 * input.length + q + 1 := by
  rw [pairBits_length]
  change 2 * input.length + (decode bits).length + 1 ≤ 2 * input.length + q + 1
  have h := decode_length_le bits
  omega

variable (verifier : NPVerifier) (input : List Bool)

theorem initial_other_stack (bits : Bits (verifier.witnessBound.eval input.length))
    (k : verifier.computation.tm.K) (hk : k ≠ verifier.computation.tm.k₀) :
    (initial verifier input bits).stk k = [] := by
  simp [initial, Turing.initList, hk]

theorem accepts_iff_valid_assignment :
    verifier.Accepts input ↔
      ∃ bits : Bits (verifier.witnessBound.eval input.length),
        Valid bits ∧ verifier.verify (input, decode bits) = true := by
  exact (exists_valid_iff _ (fun witness => verifier.verify (input, witness) = true)).symm

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

open StatementCircuit WitnessEncoding

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem eval_disjoin_ofFn_true {ι : Type*} {n : Nat}
    (input : ι → Bool) (es : Fin n → Expr ι) :
    (Expr.disjoin (List.ofFn es)).eval input = true ↔ ∃ i, (es i).eval input = true := by
  rw [Expr.eval_disjoin_true]
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨es i, List.mem_ofFn.mpr ⟨i, rfl⟩, h⟩

section Size

theorem size_mux {ι : Type*} (c y n : Expr ι) :
    (Expr.mux c y n).size = 2 * c.size + y.size + n.size + 4 := by
  simp only [Expr.mux, Expr.size]
  omega

end Size

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

open Turing StatementCircuit CircuitBatch
open scoped BigOperators

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.alphabetFinite
local instance labelFinite_r114ba2_1 (V : NPVerifier) : Fintype V.computation.tm.Λ :=
  V.computation.tm.ΛFin
local instance stateFinite_r114ba2_1 (V : NPVerifier) : Fintype V.computation.tm.σ :=
  V.computation.tm.σFin
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.labelDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.stateDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.alphabetDecidable
theorem capacity_pos (V : NPVerifier) (n : Nat) : 1 ≤ capacity V n := by
  unfold capacity
  omega

abbrev FreeBits (V : NPVerifier) (input : List Bool) :=
  WitnessEncoding.Bits (V.witnessBound.eval input.length)

def machineInput (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :=
  (pairBits (input, WitnessEncoding.decode bits)).map V.computation.inputAlphabet.invFun

def actualRun (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) (t : Nat) :
    V.computation.tm.Cfg := BoundedExecution.run V.computation.tm (machineInput V input bits) t

theorem stackCapacity_le (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :
    BoundedExecution.stackCapacity V.computation.tm (machineInput V input bits)
      (V.horizon input.length) ≤ capacity V input.length := by
  have h := WitnessEncoding.pairBits_decode_length_le input bits
  simp only [BoundedExecution.stackCapacity, machineInput, List.length_map, capacity]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ClashMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

section

open PostfixModel

def clashPairTokens (i j : Nat) : List Token :=
  if i = j then [.const false] else [.input i, .input j, .and]

end

open StatementCircuit WitnessCircuit WitnessEncoding PostfixModel PostfixAlignment CircuitBatch

theorem forestTokens_ofFn {ι : Type*} (wire : ι → Nat) (n : Nat) (es : Fin n → Expr ι) :
    forestTokens wire (List.ofFn es) = (List.ofFn fun i => exprTokens wire (es i)).flatten := by
  simp only [forestTokens, List.flatMap_def, List.map_ofFn, Function.comp_def]

def muxTokens (condition yes no : List Token) : List Token :=
  condition ++ yes ++ [.and] ++ condition ++ [.not] ++ no ++ [.and, .or]

theorem exprTokens_mux {ι : Type*} (wire : ι → Nat) (c y n : Expr ι) :
    exprTokens wire (Expr.mux c y n) =
      muxTokens (exprTokens wire c) (exprTokens wire y) (exprTokens wire n) := by
  simp [Expr.mux, exprTokens, muxTokens, List.append_assoc]

section Symbols

variable {A : Type*} [DecidableEq A]

def payloadSymbolTokens (q : Nat) (f : Bool → A) (i : Nat) (a : Option A) : List Token :=
  [.input (q + 1 + i), .const (decide (some (f true) = a)), .and,
    .input (q + 1 + i), .not, .const (decide (some (f false) = a)), .and, .or]

end Symbols

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

namespace Input

def statement (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .tag => pushWord (slots 2) (encodeWord 5)
      (.push (slots 3) (fun _ => true) (.goto fun _ => labels .scan))
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 1) false
      (fun _ b => labels (.emit b)) (labels .restore)
  | .emit b => MachineTransducerCopy.emitter (slots 2) (fun (_ : Bool) _ => false)
      (fun _ b => [b]) (labels .scan) false b
  | .restore => Reduction.MachineTransfer.loopAt (slots 1) (slots 0) id false
      (labels .restore) exit

theorem identity_output (xs : List Bool) (control : Bool) :
    Reduction.MachineTransducer.output (fun (_ : Bool) _ => false)
      (fun _ b => [b]) control xs = xs := by
  induction xs generalizing control with
  | nil => rfl
  | cons b xs ih => simp [Reduction.MachineTransducer.output, ih]

end Input

namespace Pair

def steps (i j : Nat) : Nat := MachineUnaryLessAt.steps i j + 1 +
  if i < j then offSteps i j else
    MachineUnaryLessAt.steps j i + 1 + if j < i then offSteps i j else 1

theorem steps_le (i j : Nat) : steps i j ≤ 12 * (i + j + 2) := by
  unfold steps offSteps Input.steps MachineUnaryLessAt.steps
  have h₁ := Nat.min_le_left i j
  have h₂ := Nat.min_le_left j i
  split <;> (try split) <;> omega

end Pair

namespace Row

def steps : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | count + 1, i, start => 1 + Pair.steps i start + 1 + steps count i (start + 1)

theorem steps_le (count i start B : Nat) (hB : i + start + count ≤ B) :
    steps count i start ≤ count * (12 * (B + 2) + 2) + 1 := by
  induction count generalizing start with
  | zero => simp [steps]
  | succ count ih =>
    have hr := ih (start + 1) (by omega)
    have hp := Pair.steps_le i start
    have hpos : i + start + 2 ≤ B + 2 := by omega
    have hm := Nat.mul_le_mul_left 12 hpos
    rw [steps, Nat.succ_mul]
    omega

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean )

variable {K Λ σ : Type} [DecidableEq K]

namespace SelectorLoop

def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (done : Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .guard => MachineUnaryCounter.guard (slots 0) (labels (.input .tag)) done
  | .input l => ClashMachine.Input.statement (inputMap.trans slots)
      (fun l => labels (.input l)) (some (labels .increment)) l
  | .increment => .push (slots 1) (fun _ => true) (.goto fun _ => labels .guard)

end SelectorLoop

namespace Nonempty

inductive Label where
  | initialize_
  | remaining (l : MachineUnaryAffineAt.Label)
  | closure (l : MachineUnaryAffineAt.Label)
  | selector (l : SelectorLoop.Label)
  | orSeed | orLoop | cleanup | drain
  deriving DecidableEq, Fintype

end Nonempty

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PaddingCellsMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine

open Turing PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

theorem update_input (p : Ports K) (base : K → List Bool)
    (input output count replacement : List Bool) :
    Function.update (tapes p base input output count) (p 0) replacement =
      tapes p base replacement output count := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;> simp [tapes, p.injective.eq_iff]
  · have hn : ∀ j, k ≠ p j := fun j h => hk ⟨j, h.symm⟩
    simp [tapes, hn]

theorem update_output (p : Ports K) (base : K → List Bool)
    (input output count replacement : List Bool) :
    Function.update (tapes p base input output count) (p 1) replacement =
      tapes p base input replacement count := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;> simp [tapes, p.injective.eq_iff]
  · have hn : ∀ j, k ≠ p j := fun j h => hk ⟨j, h.symm⟩
    simp [tapes, hn]

theorem update_count (p : Ports K) (base : K → List Bool)
    (input output count replacement : List Bool) :
    Function.update (tapes p base input output count) (p 2) replacement =
      tapes p base input output replacement := by
  simp [tapes]

open VerifierCircuit WitnessEncoding

end BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_InitializationMachineAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

open Turing PostfixModel
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
open InitializationMachine (Label bodySteps selectorSteps)

variable {K Λ σ : Type} [DecidableEq K]

theorem identity_output (control : Bool) (input : List Bool) :
    Reduction.MachineTransducer.output (fun (_ : Bool) _ => false)
      (fun _ symbol => [symbol]) control input = input := by
  induction input generalizing control with
  | nil => rfl
  | cons b input ih => simp [Reduction.MachineTransducer.output, ih]

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

namespace Full

def bodySteps (q i : Nat) : Nat :=
  1 + copySteps q + Row.steps (q + 1) i 0 + (q + 2) + 1 + copySteps q + (q + 3) + 1

theorem bodySteps_eq (q i : Nat) : bodySteps q i = Row.steps (q + 1) i 0 + 6 * q + 14 := by
  unfold bodySteps copySteps
  omega

def loopSteps : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | count + 1, q, start => 1 + bodySteps q start + loopSteps count q (start + 1)

theorem bodySteps_le (q i : Nat) (hi : i ≤ q) : bodySteps q i ≤ bodyBudget q := by
  have h := Row.steps_le (q + 1) i 0 (2 * q + 1) (by omega)
  rw [bodySteps_eq]
  unfold bodyBudget
  have he : 12 * (2 * q + 1 + 2) + 2 = 12 * (2 * q + 3) + 2 := by omega
  rw [he] at h
  omega

theorem loopSteps_le (count q start : Nat) (hbound : start + count ≤ q + 1) :
    loopSteps count q start ≤ count * (bodyBudget q + 1) + 1 := by
  induction count generalizing start with
  | zero => simp [loopSteps]
  | succ count ih =>
    have hr := ih (start + 1) (by omega)
    have hb := bodySteps_le q start (by omega)
    rw [loopSteps, Nat.succ_mul]
    omega

def steps (q : Nat) : Nat :=
  1 + copySteps q + loopSteps (q + 1) q 0 + copySteps q + (q + 3) + (q + 2) + 1

theorem steps_le_time (q : Nat) : steps q ≤ timePolynomial.eval q := by
  have h := loopSteps_le (q + 1) q 0 (by omega)
  rw [timePolynomial_eval]
  unfold steps copySteps
  omega

end Full

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean )

variable {K Λ σ : Type} [DecidableEq K]

def steps (q : Nat) : Nat := Nonempty.steps q + ClashMachine.Full.steps q + 1

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PayloadPresenceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadPresenceMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean )

variable {K Λ σ : Type} [DecidableEq K]

inductive Label where
  | initialize_
  | copy (context : CopyContext) (l : MachineUnaryAffineAt.Label)
  | presence (l : InitializationMachine.Label)
  | orLoop | cleanup | drain
  deriving DecidableEq, Fintype

def presenceLabels : InitializationMachine.Label ↪ Label :=
  ⟨Label.presence, fun _ _ h => by cases h; rfl⟩

def copyExit (labels : Label ↪ Λ) : CopyContext → Λ
  | .remaining => labels (.copy .threshold .seed)
  | .threshold => labels (.copy .closing .seed)
  | .closing => labels (.presence .guard)

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadPresenceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CellsTokensAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean )
open PayloadPresenceMachine (Ports )

variable {K Λ σ : Type} [DecidableEq K]

namespace Symbol

inductive Label where
  | start
  | first (l : PayloadPresenceMachine.Label)
  | payload (l : Payload.Label)
  | conjunction
  | second (l : PayloadPresenceMachine.Label)
  | suffix
  deriving DecidableEq, Fintype

def firstLabels : PayloadPresenceMachine.Label ↪ Label := ⟨.first, fun _ _ h => by cases h; rfl⟩
def secondLabels : PayloadPresenceMachine.Label ↪ Label := ⟨.second, fun _ _ h => by cases h; rfl⟩

end Symbol

namespace Row

variable {A : Nat}

inductive Label (A : Nat) where
  | visit (j : Fin (A + 1))
  | symbol (j : Fin A) (l : Symbol.Label)
  deriving DecidableEq, Fintype

def symbolLabels (j : Fin A) : Symbol.Label ↪ Label A :=
  ⟨Label.symbol j, fun _ _ h => by cases h; rfl⟩

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean )
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

def rowPorts (p : Ports K) : PayloadPresenceMachine.Ports K := rowMap.trans p

inductive Label (symbols : Nat)
  | guard | next
  | row (entry : PayloadCellsMachine.Row.Label symbols)
  deriving DecidableEq, Fintype

def rowLabels (label : Label A ↪ Λ) : PayloadCellsMachine.Row.Label A ↪ Λ where
  toFun entry := label (.row entry)
  inj' := by intro i j h; exact Label.row.inj (label.injective h)

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitFinish
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

open Turing MachineComposition
open MachineCloudPadding

variable {σ : Type}

theorem prependTrace {K Λ α : Type} [DecidableEq K]
    (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (firstLabel secondLabel : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (α × Option Bool))
    (atFirst : target firstLabel = Reduction.MachineTransfer.loopAt source scratch id false
      firstLabel (some secondLabel))
    (atSecond : target secondLabel = Reduction.MachineTransfer.loopAt scratch destination
      id false secondLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (ambient : α) (register : Option Bool) :
    (advance (TM2.step target))^[2 * ((base source).length + 1)]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Reduction.MachineTransfer.tapesAt source destination base []
          (base source ++ base destination)⟩ := by
  let mid := Reduction.MachineTransfer.tapesAt source scratch base [] (base source).reverse
  have first := Reduction.MachineTransfer.transferAt_fromTapes source scratch sourceScratch
    id false firstLabel (some secondLabel) target atFirst base ambient register
  change (advance (TM2.step target))^[(base source).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  change (advance (TM2.step target))^[(base source).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨some secondLabel, (ambient, none), mid⟩ at first
  have hscratch : mid scratch = (base source).reverse := by
    simp [mid]
  have hdestination : mid destination = base destination := by
    simp [mid, Reduction.MachineTransfer.tapesAt, Ne.symm sourceDestination,
      destinationScratch]
  have second := Reduction.MachineTransfer.transferAt_fromTapes scratch destination
    (Ne.symm destinationScratch) id false secondLabel exit target atSecond mid ambient none
  change (advance (TM2.step target))^[(mid scratch).length + 1]
    (some ⟨some secondLabel, (ambient, none), mid⟩) = _ at second
  rw [hscratch, hdestination] at second
  simp only [List.length_reverse, List.reverse_reverse, List.map_id] at second
  have restored : Reduction.MachineTransfer.tapesAt scratch destination mid []
      (base source ++ base destination) =
      Reduction.MachineTransfer.tapesAt source destination base []
        (base source ++ base destination) := by
    funext k
    by_cases hs : k = source
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, mid, sourceDestination, sourceScratch]
    · by_cases hd : k = destination
      · subst k
        simp [Reduction.MachineTransfer.tapesAt]
      · by_cases ht : k = scratch
        · subst k
          simp [Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch,
            Ne.symm destinationScratch, scratchEmpty]
        · simp [Reduction.MachineTransfer.tapesAt, mid, hs, hd, ht]
  rw [restored] at second
  have both := appendTrace _ first second
  simpa only [show ((base source).length + 1) + ((base source).length + 1) =
    2 * ((base source).length + 1) by omega] using both

def initialTapes (n f root : Nat) (records : List Bool) : Tape → List Bool :=
  memory (encodeWord n) (encodeWord f) (encodeWord root) records.reverse [] [] []

def finalTapes (n f root : Nat) (records : List Bool) : Tape → List Bool :=
  memory [] [] [] [] (encodeWords [n, n - f, root] ++ records) [] []

theorem circuit_finalTapes (C : Circuit) :
    finalTapes C.wires C.inputs C.output.val (recordsBits C.records) =
      memory [] [] [] [] (circuitBits C) [] [] := by
  have hcount : C.wires - C.inputs = C.gates.length := by
    simp [Circuit.wires]
  simp only [finalTapes, hcount, circuitBits, circuitWords, encodeWords_append,
    recordsBits]

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitProducer
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages

open Turing
open BinPackingGames.Reduction
open CircuitProducerModel

def clearFields (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (.field 0) []) (.field 1) []) (.field 2) []) (.field 3) []

@[simp] theorem clearFields_field (base : Tape → List Bool) (j : Fin 4) :
    clearFields base (.field j) = [] := by
  fin_cases j <;> simp [clearFields]

def cleanupSteps (base : Tape → List Bool) : Nat :=
  (base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length + 4

def finishTapes (base : Tape → List Bool) : Tape → List Bool :=
  MachineTransfer.tapesAt .reversed .output
    (Function.update (Function.update base .counter []) .selected []) []
    ((base .reversed).reverse ++ base .output)

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders

open Turing
open BinPackingGames.Foundations.Hastad
open CircuitProducerModel CircuitEmission CircuitProducerStages

def parsedTapes (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool) :
    Tape → List Bool
  | .input => suffix
  | .header => encodeWord n
  | .counter => encodeWord m
  | .selected => encodeWord output
  | tape => base tape

def resultTapes (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool) :
    Tape → List Bool
  | .input => suffix
  | .header => []
  | .counter => encodeWord m
  | .selected => encodeWord output
  | .reversed => (encodeWords [n, 3 * m + 1]).reverse
  | tape => base tape

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop

open Turing
open BinPackingGames.Foundations.Hastad
open CircuitProducerModel CircuitEmission CircuitProducerStages

def recordsInput (rs : List Record) : List Bool := rs.flatMap Record.bits
def recordsOutput (rs : List Record) : List Bool := rs.flatMap Record.outputBits

def tapes (base : Tape → List Bool) (input counter accumulator : List Bool)
    (fields : Fin 4 → List Bool) : Tape → List Bool
  | .input => input
  | .counter => counter
  | .field j => fields j
  | .scratch => []
  | .reversed => accumulator
  | tape => base tape

def parsedFields (r : Record) (j : Fin 4) : List Bool := encodeWord (r.fieldValue j)
def decodedFields (r : Record) (j : Fin 4) : List Bool :=
  if j.val = 0 then [] else parsedFields r j

theorem update_reversed (base : Tape → List Bool) (input counter acc out : List Bool)
    (fields : Fin 4 → List Bool) :
    Function.update (tapes base input counter acc fields) .reversed out =
      tapes base input counter out fields := by
  funext tape
  cases tape <;> simp [tapes]

theorem counterTapes_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes .counter
      (tapes base input counter acc fields) n [] =
      tapes base input (encodeWord n) acc fields := by
  funext tape
  cases tape <;> simp [MachineUnaryCounter.counterTapes, tapes]

theorem decodeTapes_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (r : Record) :
    Function.update (tapes base input counter acc (parsedFields r)) (.field 0) [] =
      tapes base input counter acc (decodedFields r) := by
  funext tape
  cases tape with
  | field j => fin_cases j <;> simp [tapes, decodedFields]
  | _ => simp [tapes]

theorem clearFields_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) :
    clearFields (tapes base input counter acc fields) =
      tapes base input counter acc (fun _ => []) := by
  funext tape
  cases tape with
  | field j => simp [tapes]
  | _ => simp [tapes, clearFields]

theorem cleanupSteps_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (r : Record) :
    cleanupSteps (tapes base input counter acc (decodedFields r)) =
      r.output + r.first + r.second + 7 := by
  simp [cleanupSteps, tapes, decodedFields, parsedFields, Record.fieldValue]
  omega

theorem recordBits_length (r : Record) :
    r.bits.length = r.tag.val + r.output + r.first + r.second + 4 := by
  simp [Record.bits, Record.words, encodeWords]
  omega

def bodyCost (r : Record) : Nat :=
  (r.tag.val + r.output + r.first + r.second + 8) + 1 +
    gateSteps r + (r.output + r.first + r.second + 7)

def loopCost : List Record → Nat
  | [] => 1
  | r :: rs => (1 + bodyCost r) + loopCost rs

theorem bodyCost_le (r : Record) : bodyCost r ≤ 50 * r.bits.length := by
  have h := gateSteps_le r
  rw [recordBits_length]
  unfold bodyCost
  omega

theorem loopCost_le (rs : List Record) :
    loopCost rs ≤ 50 * (recordsInput rs).length + rs.length + 1 := by
  induction rs with
  | nil => simp [loopCost, recordsInput]
  | cons r rs ih =>
      have h := bodyCost_le r
      simp only [loopCost, recordsInput, List.flatMap_cons, List.length_append,
        List.length_cons] at *
      omega

theorem recordOutput_length_le (r : Record) : r.outputBits.length ≤ 9 * r.bits.length := by
  have h := outputBits_length_le r
  rw [recordBits_length]
  omega

theorem recordsOutput_length_le (rs : List Record) :
    (recordsOutput rs).length ≤ 9 * (recordsInput rs).length := by
  induction rs with
  | nil => simp [recordsOutput, recordsInput]
  | cons r rs ih =>
      have h := recordOutput_length_le r
      simp only [recordsOutput, recordsInput, List.flatMap_cons, List.length_append] at *
      omega

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime

open Turing
open CircuitProducerModel CircuitProducerLoop

structure Input where
  wireCount : Nat
  selected : Nat
  records : List Record

def inputBits (input : Input) : List Bool :=
  encodeWords [input.wireCount, input.records.length, input.selected] ++ recordsInput input.records

def outputHeaders (input : Input) : List Bool :=
  encodeWords [input.wireCount, 3 * input.records.length + 1]

def producedBits (input : Input) : List Bool :=
  outputHeaders input ++ recordsOutput input.records ++ encodeWords (outputWords input.selected)

def inputTapes (input : Input) : Tape → List Bool :=
  fun tape => if tape = .input then inputBits input else []

def retainedTapes (input : Input) : Tape → List Bool :=
  fun tape => if tape = .selected then encodeWord input.selected else []

def guardTapes (input : Input) : Tape → List Bool :=
  tapes (retainedTapes input) (recordsInput input.records) (encodeWord input.records.length)
    (outputHeaders input).reverse (fun _ => [])

def afterLoopTapes (input : Input) : Tape → List Bool :=
  tapes (retainedTapes input) [] (encodeWord 0)
    ((recordsOutput input.records).reverse ++ (outputHeaders input).reverse) (fun _ => [])

def beforeFinishTapes (input : Input) : Tape → List Bool :=
  tapes (retainedTapes input) [] (encodeWord 0) (producedBits input).reverse (fun _ => [])

theorem headers_result_eq (input : Input) :
    CircuitProducerHeaders.resultTapes (inputTapes input) input.wireCount
      input.records.length input.selected (recordsInput input.records) = guardTapes input := by
  funext tape
  cases tape <;> simp [CircuitProducerHeaders.resultTapes, inputTapes, guardTapes,
    tapes, retainedTapes, outputHeaders]

theorem output_result_eq (input : Input) :
    Function.update (afterLoopTapes input) .reversed
      ((encodeWords (outputWords input.selected)).reverse ++ afterLoopTapes input .reversed) =
      beforeFinishTapes input := by
  rw [afterLoopTapes, update_reversed]
  simp [beforeFinishTapes, producedBits, tapes, List.reverse_append, List.append_assoc]

theorem inputBits_length (input : Input) :
    (inputBits input).length = input.wireCount + input.records.length + input.selected + 3 +
      (recordsInput input.records).length := by
  simp [inputBits, encodeWords]
  omega

theorem producedBits_length_le (input : Input) :
    (producedBits input).length ≤ input.wireCount + 3 * input.records.length +
      3 * input.selected + 9 * (recordsInput input.records).length + 12 := by
  have h := recordsOutput_length_le input.records
  simp only [producedBits, outputHeaders, List.length_append, outputWords, encodeWords,
    encodeWord_length, List.length_nil]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer

open Turing
open CircuitProducerModel

def asInput (C : Circuit) : CircuitProducerRuntime.Input :=
  ⟨C.wires, C.output.val, C.records⟩

theorem recordsInput_eq (rs : List Record) :
    CircuitProducerLoop.recordsInput rs = encodeWords (rs.flatMap Record.words) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [CircuitProducerLoop.recordsInput, List.flatMap_cons, encodeWords_append] at *
      rw [ih]
      rfl

theorem recordsOutput_eq (rs : List Record) :
    CircuitProducerLoop.recordsOutput rs = encodeWords (rs.flatMap Record.outputWords) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [CircuitProducerLoop.recordsOutput, List.flatMap_cons, encodeWords_append] at *
      rw [ih]
      rfl

theorem inputBits_asInput (C : Circuit) :
    CircuitProducerRuntime.inputBits (asInput C) = circuitBits C := by
  simp only [CircuitProducerRuntime.inputBits, asInput, Circuit.records_length,
    recordsInput_eq, circuitBits, circuitWords, encodeWords_append, recordsWords]

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PostfixBounds
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixMachine

open Turing PostfixModel Hastad

def headerTape (slot : Fin 2) : Tape := if slot.val = 0 then .current else .remaining

def readSource (tag : Fin 6) : Tape := if tag.val = 5 then .input else .roots

def readDestination (tag : Fin 6) (pass : Fin 2) : Tape :=
  if binary tag && decide (pass.val = 0) then .right else .left

def fieldSource (tag : Fin 6) (slot : Fin 3) : Tape :=
  if slot.val = 0 then .current
  else if slot.val = 1 ∨ tag.val = 5 then .left else .right

theorem outputTapes_other (base : Tape → List Bool) (bits : List Bool) (tape : Tape)
    (h : tape ≠ .reversed) : outputTapes base bits tape = base tape := by
  simp [outputTapes, h]

theorem readSource_ne_destination (tag : Fin 6) (pass : Fin 2) :
    readSource tag ≠ readDestination tag pass := by
  unfold readSource readDestination
  split <;> split <;> decide

theorem fieldSource_ne_scratch (tag : Fin 6) (slot : Fin 3) :
    fieldSource tag slot ≠ .scratch := by
  unfold fieldSource
  split <;> first | decide | (split <;> decide)

theorem fieldSource_ne_reversed (tag : Fin 6) (slot : Fin 3) :
    fieldSource tag slot ≠ .reversed := by
  unfold fieldSource
  split <;> first | decide | (split <;> decide)

def FieldReady (tag : Fin 6) (slot : Fin 3) (base : Tape → List Bool) (value : Nat) : Prop :=
  (fieldUnused tag slot = true → value = 0) ∧
    (fieldUnused tag slot = false → base (fieldSource tag slot) = encodeWord value)

theorem FieldReady.output (tag : Fin 6) (slot : Fin 3) (base : Tape → List Bool)
    (value : Nat) (h : FieldReady tag slot base value) (bits : List Bool) :
    FieldReady tag slot (outputTapes base bits) value := by
  refine ⟨h.1, ?_⟩
  intro used
  rw [outputTapes_other base bits _ (fieldSource_ne_reversed tag slot)]
  exact h.2 used

def clearTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update base .left []) .right []

def finishTapes (base : Tape → List Bool) (current : Nat) : Tape → List Bool :=
  clearTapes (Function.update
    (Function.update base .roots (encodeWord current ++ base .roots))
    .current (encodeWord (current + 1)))

def boundaryTapes (base : Tape → List Bool) (current : Nat)
    (roots : List Nat) (input : List Bool) : Tape → List Bool
  | .input => input
  | .current => encodeWord current
  | .roots => encodeWords roots
  | .left | .right | .scratch => []
  | tape => base tape

def preparedTapes (base : Tape → List Bool) (current : Nat)
    (roots : List Nat) (input left right : List Bool) : Tape → List Bool
  | .input => input
  | .current => encodeWord current
  | .roots => encodeWords roots
  | .left => left
  | .right => right
  | .scratch => []
  | tape => base tape

def operandFields : Token → Gate → List Bool × List Bool
  | .const _, _ => ([], [])
  | .input wire, _ => (encodeWord wire, [])
  | .not, .not arg => (encodeWord arg, [])
  | .and, .and left right | .or, .or left right => (encodeWord left, encodeWord right)
  | _, _ => ([], [])

def operandSteps : Token → Gate → Nat
  | .const _, _ => 0
  | .input wire, _ => wire + 2
  | .not, .not arg => arg + 2
  | .and, .and left right | .or, .or left right => left + right + 4
  | _, _ => 0

def argumentBits : Token → List Bool
  | .input wire => encodeWord wire
  | _ => []

theorem boundary_remaining (base : Tape → List Bool) (current : Nat)
    (roots : List Nat) (input : List Bool) (count : Nat) :
    Function.update (boundaryTapes base current roots input) .remaining (encodeWord count) =
      boundaryTapes (Function.update base .remaining (encodeWord count)) current roots input := by
  funext tape
  cases tape <;> simp [boundaryTapes]

def reversedTapes (base : Tape → List Bool) (bits : List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .remaining []) .reversed [])
    .output (bits ++ base .output)

def finalTapes (base : Tape → List Bool) (next : Nat) (roots : List Nat)
    (suffix output : List Bool) : Tape → List Bool
  | .input => suffix
  | .current => encodeWord next
  | .roots => encodeWords roots
  | .output => output ++ base .output
  | _ => []

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixBounds

open StatementCircuit CircuitBatch PostfixModel PostfixMachine PostfixAlignment
open CircuitProducerModel

def TokenBounded (R : Nat) : Token → Prop
  | .input wire => wire ≤ R
  | _ => True

theorem gateRecord_slot_le (current R : Nat) (gate : Gate) (hq : current ≤ R)
    (hg : gate.Bounded (R + 1)) (slot : Fin 3) :
    (gateRecord current gate).slot slot ≤ R := by
  cases gate with
  | const b => cases b <;> fin_cases slot <;> simp [gateRecord, Record.slot] <;> omega
  | not a => fin_cases slot <;> simp [gateRecord, Record.slot] <;> simp [Gate.Bounded] at hg <;> omega
  | and a b => fin_cases slot <;> simp [gateRecord, Record.slot] <;> simp [Gate.Bounded] at hg <;> omega
  | or a b => fin_cases slot <;> simp [gateRecord, Record.slot] <;> simp [Gate.Bounded] at hg <;> omega

theorem operandSteps_le (token : Token) (gate : Gate) (R : Nat)
    (ht : TokenBounded R token) (hg : gate.Bounded (R + 1)) :
    operandSteps token gate ≤ 2 * R + 4 := by
  cases token <;> cases gate <;>
    simp_all [operandSteps, TokenBounded, Gate.Bounded] <;> omega

theorem operandFields_length_le (token : Token) (gate : Gate) (R : Nat)
    (ht : TokenBounded R token) (hg : gate.Bounded (R + 1)) :
    (operandFields token gate).1.length + (operandFields token gate).2.length ≤ 2 * R + 2 := by
  cases token <;> cases gate <;>
    simp_all [operandFields, TokenBounded, Gate.Bounded] <;> omega

theorem takeGate_bounds (token : Token) (roots : List Nat) (gate : Gate) (rest : List Nat)
    (R : Nat) (ht : TokenBounded R token) (hr : RootsBounded R roots)
    (htake : token.takeGate roots = some (gate, rest)) :
    gate.Bounded (R + 1) ∧ RootsBounded R rest := by
  cases token with
  | const b =>
    simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
    rcases htake with ⟨rfl, rfl⟩
    exact ⟨trivial, hr⟩
  | input wire =>
    simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
    rcases htake with ⟨rfl, rfl⟩
    exact ⟨⟨by change wire ≤ R at ht; omega, by change wire ≤ R at ht; omega⟩, hr⟩
  | not =>
    cases roots with
    | nil => simp [Token.takeGate] at htake
    | cons a roots =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      have ha := hr a (by simp)
      exact ⟨by change a < R + 1; omega, fun r h => hr r (by simp [h])⟩
  | and =>
    cases roots with
    | nil => simp [Token.takeGate] at htake
    | cons right roots =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons left roots =>
        simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
        rcases htake with ⟨rfl, rfl⟩
        have hl := hr left (by simp)
        have hr' := hr right (by simp)
        exact ⟨⟨by omega, by omega⟩, fun r h => hr r (by simp [h])⟩
  | or =>
    cases roots with
    | nil => simp [Token.takeGate] at htake
    | cons right roots =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons left roots =>
        simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
        rcases htake with ⟨rfl, rfl⟩
        have hl := hr left (by simp)
        have hr' := hr right (by simp)
        exact ⟨⟨by omega, by omega⟩, fun r h => hr r (by simp [h])⟩

theorem exprTokens_bounded {ι : Type*} (wire : ι → Nat) (e : Expr ι) (R : Nat)
    (hw : ∀ i, wire i ≤ R) : ∀ token ∈ exprTokens wire e, TokenBounded R token := by
  induction e with
  | input i => simp [exprTokens, TokenBounded, hw]
  | const b => simp [exprTokens, TokenBounded]
  | not e ih =>
    intro token ht
    simp only [exprTokens, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ih token ht
    · trivial
  | and e f ihe ihf =>
    intro token ht
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at ht
    rcases ht with ht | ht | rfl
    · exact ihe token ht
    · exact ihf token ht
    · trivial
  | or e f ihe ihf =>
    intro token ht
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at ht
    rcases ht with ht | ht | rfl
    · exact ihe token ht
    · exact ihf token ht
    · trivial

theorem forestTokens_bounded {ι : Type*} (wire : ι → Nat) (es : List (Expr ι)) (R : Nat)
    (hw : ∀ i, wire i ≤ R) : ∀ token ∈ forestTokens wire es, TokenBounded R token := by
  intro token ht
  obtain ⟨e, _, he⟩ := List.mem_flatMap.mp ht
  exact exprTokens_bounded wire e R hw token he

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ForestStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ForestPlacement

open Turing

variable {I J K L Λ σ : Type}

variable [DecidableEq I] [DecidableEq K]

theorem trace (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ)
    (base : Tapes K) (source : L → TM2.Stmt (fun _ : I => Bool) L σ)
    (ambientProgram : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (atLabels : ∀ l, ambientProgram (labels l) = statement ports labels haltTarget (source l))
    (steps : Nat) (start finish : TM2.Cfg (fun _ : I => Bool) L σ)
    (sourceTrace : (MachineComposition.advance (TM2.step source))^[steps] (some start) = some finish) :
    (MachineComposition.advance (TM2.step ambientProgram))^[steps]
      (some (configuration ports labels haltTarget base start)) =
        some (configuration ports labels haltTarget base finish) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step ambientProgram)
    (configuration ports labels haltTarget base)
    (step_simulation ports labels haltTarget base source ambientProgram atLabels)
    steps start finish sourceTrace

noncomputable def execution (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ)
    (base : Tapes K) (source : L → TM2.Stmt (fun _ : I => Bool) L σ)
    (ambientProgram : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (atLabels : ∀ l, ambientProgram (labels l) = statement ports labels haltTarget (source l))
    {start finish : TM2.Cfg (fun _ : I => Bool) L σ} {budget : Nat}
    (sourceRun : StateTransition.EvalsToInTime (TM2.step source) start (some finish) budget) :
    StateTransition.EvalsToInTime (TM2.step ambientProgram)
      (configuration ports labels haltTarget base start)
      (some (configuration ports labels haltTarget base finish)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step ambientProgram)
    (configuration ports labels haltTarget base)
    (step_simulation ports labels haltTarget base source ambientProgram atLabels) sourceRun

end BinPackingGames.Foundations.Complexity.CookLevin.ForestPlacement

namespace BinPackingGames.Foundations.Complexity.CookLevin.RootRefresh

open Turing MachineComposition
open BinPackingGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

def guard (source : K) (start : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => start)
      (.load (fun state => (state.1, none))
        (Reduction.MachineTransfer.exitAt source exit)))

theorem guardStep_nil (source : K) (again start : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program again = guard source start exit)
    (base : K → List Bool) (hinput : base source = [])
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some again, (ambient, register), base⟩ =
      some ⟨exit, (ambient, none), base⟩ := by
  change some (TM2.stepAux (program again) (ambient, register) base) = _
  rw [atGuard]
  cases exit <;> simp [guard, TM2.stepAux, hinput, Reduction.MachineTransfer.exitAt]

theorem guardStep_nonempty (source : K) (again start : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program again = guard source start exit)
    (base : K → List Bool) (hinput : base source ≠ [])
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some again, (ambient, register), base⟩ =
      some ⟨some start, (ambient, (base source).head?), base⟩ := by
  change some (TM2.stepAux (program again) (ambient, register) base) = _
  rw [atGuard]
  cases hs : base source with
  | nil => exact False.elim (hinput hs)
  | cons bit rest => simp [guard, TM2.stepAux, hs]

theorem fieldTapes_overwrite (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output input' output' : List Bool) :
    SourceMachine.fieldTapes source destination
      (SourceMachine.fieldTapes source destination base input output) input' output' =
        SourceMachine.fieldTapes source destination base input' output' := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [SourceMachine.fieldTapes, hne]
  · by_cases hd : k = destination
    · subst k
      simp [SourceMachine.fieldTapes]
    · simp [SourceMachine.fieldTapes, hs, hd]

theorem steps_cons (n : Nat) (values : List Nat) :
    steps (n :: values) = steps values + (n + 3) := by
  simp only [steps, List.sum_cons, List.length_cons]
  omega

theorem steps_le_length (values : List Nat) :
    steps values ≤ 3 * (encodeWords values).length + 1 := by
  rw [encodeWords_length]
  unfold steps
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.RootRefresh

namespace BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

open Turing MachineComposition StatementCircuit CircuitBatch CircuitProducerModel
open PostfixModel PostfixAlignment

def coreFinal (next : Nat) (roots : List Nat) (records : List Bool) :
    PostfixMachine.Tape → List Bool :=
  PostfixMachine.finalTapes (fun _ => []) next roots [] records

theorem forest_length_le_cost {ι : Type*} (es : List (Expr ι)) :
    es.length ≤ Batch.cost es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hp := e.size_pos
    simp only [List.length_cons, Batch.cost_cons]
    omega

def localLowerPorts : PostfixMachine.Tape ↪ Tape :=
  ⟨Tape.lower, by intro a b h; exact Tape.lower.inj h⟩

def lowerFill (base : Tape → List Bool) (inner : PostfixMachine.Tape → List Bool) :
    Tape → List Bool
  | .lower tape => inner tape
  | tape => base tape

theorem fill_lower_eq (base : Tape → List Bool) (inner : PostfixMachine.Tape → List Bool) :
    ForestPlacement.fill localLowerPorts base inner = lowerFill base inner := by
  funext tape
  cases tape with
  | lower tape => exact ForestPlacement.fill_at localLowerPorts base inner tape
  | tokens => exact ForestPlacement.fill_other _ _ _ _ (by intro i; simp [localLowerPorts])
  | records => exact ForestPlacement.fill_other _ _ _ _ (by intro i; simp [localLowerPorts])
  | rootTable => exact ForestPlacement.fill_other _ _ _ _ (by intro i; simp [localLowerPorts])

def extras (oldRecords oldRoots : List Bool) : Tape → List Bool
  | .records => oldRecords
  | .rootTable => oldRoots
  | _ => []

end BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PolynomialMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PolynomialMachine

theorem coefficientPolynomial_eval (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n = cs.foldr (fun digit value => value * n + digit) 0 := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a rest ih => simp [coefficientPolynomial, ih]

theorem coefficientPolynomial_eval_reverse (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n =
      cs.reverse.foldl (fun value digit => value * n + digit) 0 := by
  rw [coefficientPolynomial_eval, List.foldr_eq_foldl_reverse]

theorem highCoefficients_foldl (p : Polynomial Nat) (n : Nat) :
    (highCoefficients p).foldl (fun value digit => value * n + digit) 0 = p.eval n := by
  calc
    _ = (coefficientPolynomial (coefficients p).val).eval n :=
      (coefficientPolynomial_eval_reverse (coefficients p).val n).symm
    _ = p.eval n := congrArg (fun q : Polynomial Nat => q.eval n) (coefficients p).property

theorem range_map_digit (p : Polynomial Nat) :
    (List.range (width p)).map (digit p) = highCoefficients p := by
  apply List.ext_getElem
  · simp [width]
  · intro i hi hj
    simp [digit, width, hj]

section LiteralFields

open Turing
open BinPackingGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def clearFieldsTapes (count : K → Nat) : List K → (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes => clearFieldsTapes count rest
      (Function.update tapes k ((tapes k).drop (count k)))

theorem clearFieldsTapes_apply (count : K → Nat) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    clearFieldsTapes count indices tapes k =
      if k ∈ indices then (tapes k).drop (count k) else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [clearFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [clearFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

end LiteralFields

noncomputable section

theorem prefixValuePolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixValuePolynomial digits i).eval n = MachineHorner.value n digits i := by
  induction i with
  | zero => simp [prefixValuePolynomial, MachineHorner.value]
  | succ i ih => simp [prefixValuePolynomial, MachineHorner.value, ih]

theorem prefixCostPolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixCostPolynomial digits i).eval n = MachineHorner.prefixSteps n digits i := by
  induction i with
  | zero => simp [prefixCostPolynomial, MachineHorner.prefixSteps]
  | succ i ih =>
    simp only [prefixCostPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval, ih,
      MachineHorner.prefixSteps, MachineHorner.stepCost, MachineRadixStep.steps]
    ring

end

end BinPackingGames.Foundations.Complexity.CookLevin.PolynomialMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionArena
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

open StatementCircuit CircuitBatch PostfixModel PostfixAlignment

variable {inputs oldWidth newWidth width : Nat}

def snapshot (f : Frame inputs width) : Snapshot where
  current := inputs + f.fragment.gates.length
  roots := List.ofFn (fun i => (f.wires i).val)
  reversedRecords := (recordsBits (gateRecords inputs f.fragment.gates)).reverse

def next (f : Frame inputs width) : Nat := inputs + f.fragment.gates.length
def rootValues (f : Frame inputs width) : List Nat := List.ofFn (fun i => (f.wires i).val)
def recordBits (f : Frame inputs width) : List Bool :=
  recordsBits (gateRecords inputs f.fragment.gates)

theorem gateRecords_append (start : Nat) (first rest : List Gate) :
    gateRecords start (first ++ rest) =
      gateRecords start first ++ gateRecords (start + first.length) rest := by
  induction first generalizing start with
  | nil => simp [gateRecords]
  | cons g gs ih =>
    simp [gateRecords, ih, Nat.add_comm, Nat.add_left_comm]

theorem snapshot_root_mem_lt (f : Frame inputs width) (r : Nat)
    (hr : r ∈ (snapshot f).roots) : r < (snapshot f).current := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact (f.wires i).isLt

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

@[simp] theorem bitsOfLabels_labelsOfBits (vertices : V ≃ Fin n)
    (assignment : Fin (n * 6) → Bool) : bitsOfLabels vertices (labelsOfBits vertices assignment) = assignment := by
  funext k
  simp only [bitsOfLabels, labelsOfBits, bitIndex, Equiv.apply_symm_apply, Prod.eta]

end BinPackingGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierFront
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

open Turing MachineComposition
open BinPackingGames.Reduction.MachineTransfer

theorem update_zero (input saved counter replacement : List Bool) :
    Function.update (tapes input saved counter) 0 replacement =
      tapes replacement saved counter := by
  funext k
  fin_cases k <;> simp [tapes]

theorem update_one (input saved counter replacement : List Bool) :
    Function.update (tapes input saved counter) 1 replacement =
      tapes input replacement counter := by
  funext k
  fin_cases k <;> simp [tapes]

theorem update_two (input saved counter replacement : List Bool) :
    Function.update (tapes input saved counter) 2 replacement =
      tapes input saved replacement := by
  funext k
  fin_cases k <;> simp [tapes]

end BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront
open Turing MachineComposition
open BinPackingGames.Foundations.Hastad

variable {A : Type}

theorem alphabet_tapes_apply {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : ∀ k, List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ProducerFrontStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

open Turing MachineComposition PostfixModel
open ClashMachine (State clean chain)
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

inductive Label (A : Nat)
  | prefix (entry : CellsPrefixStage.Label A)
  | copyFirst | copySecond | seed
  | payload (entry : PayloadRowsLoop.Label A)
  | padding | cleanup | drain
  deriving DecidableEq, Fintype

def prefixLabels (labels : Label A ↪ Λ) : CellsPrefixStage.Label A ↪ Λ :=
  ⟨fun l => labels (.prefix l), fun _ _ h => Label.prefix.inj (labels.injective h)⟩

def payloadLabels (labels : Label A ↪ Λ) : PayloadRowsLoop.Label A ↪ Λ :=
  ⟨fun l => labels (.payload l), fun _ _ h => Label.payload.inj (labels.injective h)⟩

end BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionIterationTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

open Turing MachineComposition TermMachine TransitionTemplate PostfixModel

section Indexed

end Indexed

open VerifierCircuit

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

open Turing MachineComposition StatementCircuit CircuitBatch
open PostfixModel PostfixAlignment ProducerInvariant VerifierCircuit
open TransitionArena

local instance iterationTimeVerifierLabelFintype_r114ba2_1 (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype_r114ba2_1 (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype_r114ba2_1 (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq_r114ba2_1 (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq_r114ba2_1 (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq_r114ba2_1 (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
def wireValues {inputs count : Nat} (frame : Frame inputs count) : Fin count → Nat :=
  fun i => (frame.wires i).val

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PCPIteration
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.AmplificationRound

abbrev Label := QueryIncidence.Label 6

end BinPackingGames.Foundations.PCP.AmplificationRound

namespace BinPackingGames.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

end BinPackingGames.Foundations.PCP.RoundGap

namespace BinPackingGames.Foundations.PCP.PCPIteration

def finalClauseGap : ℚ := 1 / (40960 * (FinalConstants.walkLength : ℚ))

end BinPackingGames.Foundations.PCP.PCPIteration

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TreeColorCounts
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

section
namespace ForkGadget

open scoped BigOperators

theorem red_witness {N i : ℕ} (hi : 1 ≤ i) :
    ∃ l ∈ leaves N i, colorCount (red i) l = 1 := by
  refine ⟨leafWord N i 0 0,
    leafWord_mem (Nat.two_pow_pos i) (continuationCount_pos i N), ?_⟩
  rw [red_count hi, ite_eq_left (phaseQuota_pos i)]

theorem blue_witness {N i : ℕ} (hi : 1 ≤ i) :
    ∃ l ∈ leaves N i, colorCount (blue i) l = 1 := by
  have hlt : phaseQuota i < 2 ^ i := by
    have hp := phaseQuota_pos i
    have heq := two_mul_phaseQuota hi
    omega
  refine ⟨leafWord N i (phaseQuota i) 0,
    leafWord_mem hlt (continuationCount_pos i N), ?_⟩
  rw [blue_count hi, ite_eq_left ⟨le_rfl, hlt⟩]

theorem avoids {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N)
    (A : Finset (List ℕ)) (hroot : [] ∉ A)
    (hquota : ∀ j, 1 ≤ j → j ≤ N → levelCount A j ≤ phaseQuota j) :
    ∃ l ∈ leaves N i, Disjoint A (UniformTree.prefixes l) := by
  let early := A.filter (fun w => 0 < w.length ∧ w.length ≤ i)
  have hearly : early.card < (Finset.range (2 ^ i)).card := by
    simpa only [early, Nat.zero_add, Finset.card_range] using
      card_rank_initial_lt_pow A List.length 0 i (by
        intro j hj
        have hj' := Finset.mem_Icc.mp hj
        simpa only [levelCount, Nat.zero_add] using hquota j hj'.1 (hj'.2.trans hiN))
  have hspines : (Finset.range (2 ^ i) : Set ℕ).PairwiseDisjoint
      (fun a => (UniformTree.prefixes (spine i a)).erase []) := by
    intro a ha b hb hab
    exact disjoint_positive_spine_prefixes hab
  obtain ⟨a, ha, hclear⟩ := exists_disjoint_of_card_lt
    (Finset.range (2 ^ i)) early
    (fun a => (UniformTree.prefixes (spine i a)).erase []) hspines hearly
  have ha' : a < 2 ^ i := Finset.mem_range.mp ha
  have hspine : Disjoint A (UniformTree.prefixes (spine i a)) := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwpath
    by_cases hw : w = []
    · exact hroot (hw ▸ hwA)
    · have hp := UniformTree.mem_prefixes_iff.mp hwpath
      have hlen : w.length ≤ i := by simpa only [spine_length hi] using hp.length_le
      have he : w ∈ early := Finset.mem_filter.mpr
        ⟨hwA, List.length_pos_iff_ne_nil.mpr hw, hlen⟩
      exact Finset.disjoint_left.mp hclear he (Finset.mem_erase.mpr ⟨hw, hwpath⟩)
  by_cases hiN' : i < N
  · let late := A.filter (fun w => i < w.length ∧ w.length ≤ N)
    have hlate : late.card < (Finset.range (continuationCount i N)).card := by
      simpa only [late, Nat.zero_add, Finset.card_range] using
        card_rank_tail_lt_continuations A List.length 0 i N (by
          intro j hj
          have hj' := Finset.mem_Icc.mp hj
          simpa only [levelCount, Nat.zero_add] using hquota j (by omega) hj'.2)
    have hchains : (Finset.range (continuationCount i N) : Set ℕ).PairwiseDisjoint
        (fun b => prefixesAfter (spine i a) (continuation N i b)) := by
      intro b hb c hc hbc
      simp only [continuation, ite_eq_left hiN']
      exact disjoint_spine_prefixesAfter (spine i a) hbc
    obtain ⟨b, hb, hclear'⟩ := exists_disjoint_of_card_lt
      (Finset.range (continuationCount i N)) late
      (fun b => prefixesAfter (spine i a) (continuation N i b)) hchains hlate
    have hchain : Disjoint A (prefixesAfter (spine i a) (continuation N i b)) := by
      apply Finset.disjoint_left.mpr
      intro w hwA hwpath
      obtain ⟨v, hv, hp, hvw⟩ := mem_prefixesAfter_iff.mp hwpath
      have hvpos : 0 < v.length := List.length_pos_iff_ne_nil.mpr hv
      have hvlen : v.length ≤ N - i := by
        simpa only [continuation_length hiN] using hp.length_le
      have hwlen : w.length = i + v.length := by
        rw [← hvw, List.length_append, spine_length hi]
      have hl : w ∈ late := Finset.mem_filter.mpr ⟨hwA, by omega, by omega⟩
      exact Finset.disjoint_left.mp hclear' hl hwpath
    refine ⟨leafWord N i a b, leafWord_mem ha' (Finset.mem_range.mp hb), ?_⟩
    rw [leafWord, prefixes_append_eq]
    apply Finset.disjoint_left.mpr
    intro w hwA hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.disjoint_left.mp hspine hwA hw
    · exact Finset.disjoint_left.mp hchain hwA hw
  · refine ⟨leafWord N i a 0,
      leafWord_mem ha' (continuationCount_pos i N), ?_⟩
    simpa only [leafWord, continuation, ite_eq_right hiN', List.append_nil] using hspine

def auxiliary (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) : AuxiliaryTree 1 where
  tree := tree N i hi hiN
  quota := phaseQuota
  quota_pos := fun depth _ _ => phaseQuota_pos depth
  red := red i
  blue := blue i
  red_subset := red_subset hi hiN
  blue_subset := blue_subset hi hiN
  root_not_red := root_not_red hi
  root_not_blue := root_not_blue hi
  red_blue_disjoint := red_blue_disjoint i
  red_level := fun depth _ _ => red_level hi depth
  blue_level := fun depth _ _ => blue_level hi depth
  total_count := fun _ hl => total_count hi hl
  red_witness := red_witness hi
  blue_witness := blue_witness hi
  avoids := by
    intro A hA
    exact avoids hi hiN A hA.1 hA.2

@[simp] theorem auxiliary_height (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (auxiliary N i hi hiN).tree.height = N := rfl

@[simp] theorem auxiliary_quota (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (auxiliary N i hi hiN).quota = phaseQuota := rfl

theorem auxiliary_red_depth (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N)
    {w : List ℕ} (hw : w ∈ (auxiliary N i hi hiN).red) : w.length = i :=
  red_depth hi hw

theorem auxiliary_blue_depth (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N)
    {w : List ℕ} (hw : w ∈ (auxiliary N i hi hiN).blue) : w.length = i :=
  blue_depth hi hw

@[simp] theorem auxiliary_card_red (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (auxiliary N i hi hiN).red.card = phaseQuota i := card_red i

@[simp] theorem auxiliary_card_blue (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (auxiliary N i hi hiN).blue.card = phaseQuota i := card_blue hi

end ForkGadget

open scoped BigOperators

end

namespace UniformTree

def liftMarks (T : UniformTree) (M : T.leaves → Finset (List ℕ)) : Finset (List ℕ) :=
  Finset.univ.biUnion (fun l : T.leaves => (M l).image (fun w => l.val ++ w))

@[simp] theorem mem_liftMarks (T : UniformTree) (M : T.leaves → Finset (List ℕ))
    {x : List ℕ} :
    x ∈ T.liftMarks M ↔ ∃ l : T.leaves, ∃ w ∈ M l, x = l.val ++ w := by
  constructor
  · intro hx
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨w, hw, hx⟩ := Finset.mem_image.mp hl
    exact ⟨l, w, hw, hx.symm⟩
  · rintro ⟨l, w, hw, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨l, Finset.mem_univ l, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩

theorem root_not_mem_lift (T : UniformTree) (M : T.leaves → Finset (List ℕ))
    (hroot : ∀ l, [] ∉ M l) : [] ∉ T.liftMarks M := by
  intro hx
  obtain ⟨l, w, hw, heq⟩ := (T.mem_liftMarks M).mp hx
  have hlen := congrArg List.length heq
  simp only [List.length_nil, List.length_append] at hlen
  have hwzero : w = [] := List.length_eq_zero_iff.mp (by omega)
  exact hroot l (hwzero ▸ hw)

theorem height_lt_length_of_mem_lift (T : UniformTree)
    (M : T.leaves → Finset (List ℕ)) (hroot : ∀ l, [] ∉ M l)
    {x : List ℕ} (hx : x ∈ T.liftMarks M) : T.height < x.length := by
  obtain ⟨l, w, hw, rfl⟩ := (T.mem_liftMarks M).mp hx
  have hwne : w.length ≠ 0 := by
    intro hz
    exact hroot l ((List.length_eq_zero_iff.mp hz) ▸ hw)
  rw [List.length_append, T.length_leaf l.val l.property]
  omega

theorem liftMarks_subset_graft_vertices (T : UniformTree)
    (G : T.leaves → UniformTree) (N : ℕ) (hG : ∀ l, (G l).height = N)
    (M : T.leaves → Finset (List ℕ)) (hM : ∀ l, M l ⊆ (G l).vertices) :
    T.liftMarks M ⊆ (T.graft G N hG).vertices := by
  intro x hx
  obtain ⟨l, w, hw, rfl⟩ := (T.mem_liftMarks M).mp hx
  exact T.append_mem_graft_vertices G N hG l (hM l hw)

theorem old_marks_disjoint_lift (T : UniformTree) (old : Finset (List ℕ))
    (M : T.leaves → Finset (List ℕ)) (hold : old ⊆ T.vertices)
    (hroot : ∀ l, [] ∉ M l) : Disjoint old (T.liftMarks M) := by
  apply Finset.disjoint_left.mpr
  intro x hxold hxlift
  have hle := T.length_le_height (hold hxold)
  have hlt := T.height_lt_length_of_mem_lift M hroot hxlift
  omega

theorem liftMarks_disjoint (T : UniformTree)
    (Mred Mblue : T.leaves → Finset (List ℕ))
    (hdisj : ∀ l, Disjoint (Mred l) (Mblue l)) :
    Disjoint (T.liftMarks Mred) (T.liftMarks Mblue) := by
  apply Finset.disjoint_left.mpr
  intro x hxred hxblue
  obtain ⟨l, u, hu, hequ⟩ := (T.mem_liftMarks Mred).mp hxred
  obtain ⟨m, v, hv, heqv⟩ := (T.mem_liftMarks Mblue).mp hxblue
  obtain ⟨hlm, huv⟩ := (T.append_eq_append_iff l m u v).mp (hequ.symm.trans heqv)
  subst m
  subst v
  exact Finset.disjoint_left.mp (hdisj l) hu hv

theorem filter_liftMarks_prefix (T : UniformTree)
    (M : T.leaves → Finset (List ℕ)) (l : T.leaves) (w : List ℕ) :
    (T.liftMarks M).filter (fun x => x.IsPrefix (l.val ++ w)) =
      ((M l).filter (fun v => v.IsPrefix w)).image (fun v => l.val ++ v) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxM, hxp⟩ := Finset.mem_filter.mp hx
    obtain ⟨m, v, hv, rfl⟩ := (T.mem_liftMarks M).mp hxM
    obtain ⟨hml, hvp⟩ := (T.append_prefix_append_iff m l v w).mp hxp
    subst m
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvp⟩, rfl⟩
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hvM, hvp⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨(T.mem_liftMarks M).mpr ⟨l, v, hvM, rfl⟩,
      (T.append_prefix_append_iff l l v w).mpr ⟨rfl, hvp⟩⟩

theorem colorCount_liftMarks (T : UniformTree)
    (M : T.leaves → Finset (List ℕ)) (l : T.leaves) (w : List ℕ) :
    colorCount (T.liftMarks M) (l.val ++ w) = colorCount (M l) w := by
  unfold colorCount
  rw [T.filter_liftMarks_prefix M l w]
  exact Finset.card_image_of_injective _ (fun _ _ h => List.append_cancel_left h)

theorem colorCount_union_liftMarks (T : UniformTree) (old : Finset (List ℕ))
    (M : T.leaves → Finset (List ℕ)) (hold : old ⊆ T.vertices)
    (hroot : ∀ l, [] ∉ M l) (l : T.leaves) (w : List ℕ) :
    colorCount (old ∪ T.liftMarks M) (l.val ++ w) =
      colorCount old l.val + colorCount (M l) w := by
  have hd : Disjoint (old.filter (fun x => x.IsPrefix (l.val ++ w)))
      ((T.liftMarks M).filter (fun x => x.IsPrefix (l.val ++ w))) :=
    (T.old_marks_disjoint_lift old M hold hroot).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsplit : colorCount (old ∪ T.liftMarks M) (l.val ++ w) =
      colorCount old (l.val ++ w) + colorCount (T.liftMarks M) (l.val ++ w) := by
    unfold colorCount
    rw [Finset.filter_union, Finset.card_union_of_disjoint hd]
  rw [hsplit, T.colorCount_liftMarks M l w]
  have holdcount : colorCount old (l.val ++ w) = colorCount old l.val :=
    congrArg Finset.card (T.filter_old_prefix_append old hold l w)
  rw [holdcount]

theorem levelCount_liftMarks_le (T : UniformTree)
    (M : T.leaves → Finset (List ℕ)) (rank : T.leaves → ℕ)
    (hinj : Function.Injective rank)
    (hlength : ∀ l, ∀ w ∈ M l, w.length = rank l)
    (hcard : ∀ l, (M l).card ≤ phaseQuota (rank l)) (depth : ℕ) :
    levelCount (T.liftMarks M) depth ≤ phaseQuota (depth - T.height) := by
  classical
  let A := (T.liftMarks M).filter (fun x => x.length = depth)
  by_cases hA : A.Nonempty
  · obtain ⟨x, hx⟩ := hA
    obtain ⟨hxM, hxdepth⟩ := Finset.mem_filter.mp hx
    obtain ⟨l, w, hw, heqx⟩ := (T.mem_liftMarks M).mp hxM
    have hlrank : T.height + rank l = depth := by
      rw [heqx, List.length_append, T.length_leaf l.val l.property, hlength l w hw] at hxdepth
      exact hxdepth
    have hsub : A ⊆ (M l).image (fun v => l.val ++ v) := by
      intro y hy
      obtain ⟨hyM, hydepth⟩ := Finset.mem_filter.mp hy
      obtain ⟨m, v, hv, heqy⟩ := (T.mem_liftMarks M).mp hyM
      have hmrank : T.height + rank m = depth := by
        rw [heqy, List.length_append, T.length_leaf m.val m.property, hlength m v hv] at hydepth
        exact hydepth
      have hml : m = l := hinj (by omega)
      subst m
      exact Finset.mem_image.mpr ⟨v, hv, heqy.symm⟩
    have hrank : rank l = depth - T.height := by omega
    calc
      levelCount (T.liftMarks M) depth = A.card := rfl
      _ ≤ ((M l).image (fun v => l.val ++ v)).card := Finset.card_le_card hsub
      _ ≤ (M l).card := Finset.card_image_le
      _ ≤ phaseQuota (rank l) := hcard l
      _ = phaseQuota (depth - T.height) := congrArg phaseQuota hrank
  · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ _
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

theorem levelCount_union_liftMarks (T : UniformTree) (old : Finset (List ℕ))
    (M : T.leaves → Finset (List ℕ)) (hold : old ⊆ T.vertices)
    (hroot : ∀ l, [] ∉ M l) (depth : ℕ) :
    levelCount (old ∪ T.liftMarks M) depth =
      if depth ≤ T.height then levelCount old depth else levelCount (T.liftMarks M) depth := by
  unfold levelCount
  split_ifs with hdepth
  · apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hxold | hxlift, hxlen⟩
      · exact ⟨hxold, hxlen⟩
      · have hlt := T.height_lt_length_of_mem_lift M hroot hxlift
        omega
    · rintro ⟨hxold, hxlen⟩
      exact ⟨Or.inl hxold, hxlen⟩
  · apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hxold | hxlift, hxlen⟩
      · have hle := T.length_le_height (hold hxold)
        omega
      · exact ⟨hxlift, hxlen⟩
    · rintro ⟨hxlift, hxlen⟩
      exact ⟨Or.inr hxlift, hxlen⟩

theorem levelCount_union_liftMarks_le (T : UniformTree) (old : Finset (List ℕ))
    (M : T.leaves → Finset (List ℕ))
    (hold : old ⊆ T.vertices) (hroot : ∀ l, [] ∉ M l)
    (rank : T.leaves → ℕ) (hinj : Function.Injective rank)
    (hlength : ∀ l, ∀ w ∈ M l, w.length = rank l)
    (hcard : ∀ l, (M l).card ≤ phaseQuota (rank l)) (quota : ℕ → ℕ)
    (holdquota : ∀ depth, 1 ≤ depth → depth ≤ T.height → levelCount old depth ≤ quota depth)
    (depth : ℕ) (hpos : 1 ≤ depth) :
    levelCount (old ∪ T.liftMarks M) depth ≤
      if depth ≤ T.height then quota depth else phaseQuota (depth - T.height) := by
  rw [T.levelCount_union_liftMarks old M hold hroot depth]
  split_ifs with hdepth
  · exact holdquota depth hpos hdepth
  · exact T.levelCount_liftMarks_le M rank hinj hlength hcard depth

end UniformTree
end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TreeAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

def extendPhaseQuota (height : ℕ) (old : ℕ → ℕ) (depth : ℕ) : ℕ :=
  if depth ≤ height then old depth else phaseQuota (depth - height)

theorem extendPhaseQuota_old (height : ℕ) (old : ℕ → ℕ) {depth : ℕ}
    (hdepth : depth ≤ height) : extendPhaseQuota height old depth = old depth := by
  simp only [extendPhaseQuota, ite_eq_left hdepth]

theorem extendPhaseQuota_new (height : ℕ) (old : ℕ → ℕ) {j : ℕ}
    (hj : 0 < j) : extendPhaseQuota height old (height + j) = phaseQuota j := by
  have hnot : ¬ height + j ≤ height := by omega
  simp only [extendPhaseQuota, ite_eq_right hnot, Nat.add_sub_cancel_left]

theorem graft_avoids {n : ℕ} (old : AuxiliaryTree n)
    (G : old.tree.leaves → AuxiliaryTree 1) (N : ℕ)
    (hG : ∀ l, (G l).tree.height = N)
    (hquota : ∀ l, (G l).quota = phaseQuota)
    (marks : Finset (List ℕ))
    (hmarks : RespectsTreeQuota
      (UniformTree.graft old.tree (fun l => (G l).tree) N hG)
      (extendPhaseQuota old.tree.height old.quota) marks) :
    ∃ leaf ∈ (UniformTree.graft old.tree (fun l => (G l).tree) N hG).leaves,
      Disjoint marks (UniformTree.prefixes leaf) := by
  have hold : RespectsTreeQuota old.tree old.quota marks := by
    refine ⟨hmarks.1, ?_⟩
    intro j hj hbound
    have hglobal := hmarks.2 j hj (by
      change j ≤ old.tree.height + N
      omega)
    simpa only [extendPhaseQuota_old old.tree.height old.quota hbound] using hglobal
  obtain ⟨l, hl, havoidOld⟩ := old.avoids marks hold
  let oldLeaf : old.tree.leaves := ⟨l, hl⟩
  have hlocal : RespectsTreeQuota (G oldLeaf).tree (G oldLeaf).quota
      (pullMarks l marks) := by
    constructor
    · rw [nil_mem_pullMarks]
      intro hmarked
      exact Finset.disjoint_left.mp havoidOld hmarked
        (UniformTree.mem_prefixes_iff.mpr (List.prefix_refl l))
    · intro j hj hbound
      have hjpos : 0 < j := by omega
      have hlocalBound : j ≤ N := by simpa only [hG oldLeaf] using hbound
      have hglobal := hmarks.2 (old.tree.height + j) (by omega) (by
        change old.tree.height + j ≤ old.tree.height + N
        omega)
      have hpull := levelCount_pullMarks_le l marks j
      rw [old.tree.length_leaf l hl] at hpull
      rw [hquota oldLeaf]
      exact hpull.trans (by
        simpa only [extendPhaseQuota_new old.tree.height old.quota hjpos] using hglobal)
  obtain ⟨w, hw, havoidNew⟩ := (G oldLeaf).avoids (pullMarks l marks) hlocal
  refine ⟨l ++ w, ?_, disjoint_prefixes_append_of_pull l w marks havoidOld havoidNew⟩
  exact (UniformTree.mem_graft_leaves old.tree (fun l => (G l).tree) N hG).mpr
    ⟨oldLeaf, w, hw, rfl⟩

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PhaseIteration
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

namespace UniformTree

def leafRank (T : UniformTree) (l : T.leaves) : ℕ :=
  ((T.leaves.orderIsoOfFin rfl).symm l).val + 1

theorem leafRank_pos (T : UniformTree) (l : T.leaves) : 0 < T.leafRank l := by
  unfold leafRank
  omega

theorem one_le_leafRank (T : UniformTree) (l : T.leaves) : 1 ≤ T.leafRank l :=
  T.leafRank_pos l

theorem leafRank_le (T : UniformTree) (l : T.leaves) : T.leafRank l ≤ T.leaves.card := by
  have h := ((T.leaves.orderIsoOfFin rfl).symm l).isLt
  unfold leafRank
  omega

theorem leafRank_injective (T : UniformTree) : Function.Injective T.leafRank := by
  intro l m h
  apply (T.leaves.orderIsoOfFin rfl).symm.injective
  apply Fin.ext
  exact Nat.add_right_cancel h

def rankedGadget (T : UniformTree) (l : T.leaves) : AuxiliaryTree 1 :=
  ForkGadget.auxiliary T.leaves.card (T.leafRank l)
    (T.one_le_leafRank l) (T.leafRank_le l)

@[simp] theorem rankedGadget_height (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).tree.height = T.leaves.card := rfl

@[simp] theorem rankedGadget_quota (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).quota = phaseQuota := rfl

theorem rankedGadget_red_depth (T : UniformTree) (l : T.leaves)
    {w : List ℕ} (hw : w ∈ (T.rankedGadget l).red) : w.length = T.leafRank l :=
  ForkGadget.auxiliary_red_depth _ _ _ _ hw

theorem rankedGadget_blue_depth (T : UniformTree) (l : T.leaves)
    {w : List ℕ} (hw : w ∈ (T.rankedGadget l).blue) : w.length = T.leafRank l :=
  ForkGadget.auxiliary_blue_depth _ _ _ _ hw

@[simp] theorem rankedGadget_card_red (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).red.card = phaseQuota (T.leafRank l) :=
  ForkGadget.auxiliary_card_red _ _ _ _

@[simp] theorem rankedGadget_card_blue (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).blue.card = phaseQuota (T.leafRank l) :=
  ForkGadget.auxiliary_card_blue _ _ _ _

def nextPhase (T : UniformTree) : UniformTree :=
  T.graft (fun l => (T.rankedGadget l).tree) T.leaves.card
    (fun l => T.rankedGadget_height l)

@[simp] theorem nextPhase_height (T : UniformTree) :
    T.nextPhase.height = T.height + T.leaves.card := rfl

theorem mem_nextPhase_leaves (T : UniformTree) {x : List ℕ} :
    x ∈ T.nextPhase.leaves ↔
      ∃ l : T.leaves, ∃ w ∈ (T.rankedGadget l).tree.leaves, x = l.val ++ w :=
  T.mem_graft_leaves _ _ _

def singletonRoot : UniformTree where
  height := 0
  leaves := {[]}
  leaves_nonempty := ⟨[], Finset.mem_singleton_self []⟩
  length_leaf := by
    intro l hl
    have hl' : l = [] := Finset.mem_singleton.mp hl
    simp only [hl', List.length_nil]
  positive_labels := by
    intro l hl a ha
    have hl' : l = [] := Finset.mem_singleton.mp hl
    simp only [hl', List.not_mem_nil] at ha

end UniformTree

namespace AuxiliaryTree

def initial : AuxiliaryTree 0 where
  tree := UniformTree.singletonRoot
  quota := fun _ => 0
  quota_pos := by
    intro depth hpos hle
    change depth ≤ 0 at hle
    omega
  red := ∅
  blue := ∅
  red_subset := Finset.empty_subset _
  blue_subset := Finset.empty_subset _
  root_not_red := by simp
  root_not_blue := by simp
  red_blue_disjoint := by simp
  red_level := by simp [levelCount]
  blue_level := by simp [levelCount]
  total_count := by simp [colorCount]
  red_witness := ⟨[], Finset.mem_singleton_self [], by simp [colorCount]⟩
  blue_witness := ⟨[], Finset.mem_singleton_self [], by simp [colorCount]⟩
  avoids := by
    intro marks hmarks
    refine ⟨[], Finset.mem_singleton_self [], ?_⟩
    apply Finset.disjoint_left.mpr
    intro w hw hp
    have heq : w = [] := by
      simpa only [UniformTree.mem_prefixes_iff, List.prefix_nil] using hp
    exact hmarks.1 (heq ▸ hw)

def step {n : ℕ} (old : AuxiliaryTree n) : AuxiliaryTree (n + 1) where
  tree := old.tree.nextPhase
  quota := extendPhaseQuota old.tree.height old.quota
  quota_pos := by
    intro depth hpos _
    unfold extendPhaseQuota
    split_ifs with hdepth
    · exact old.quota_pos depth hpos hdepth
    · exact phaseQuota_pos _
  red := old.red ∪ old.tree.liftMarks (fun l => (old.tree.rankedGadget l).red)
  blue := old.blue ∪ old.tree.liftMarks (fun l => (old.tree.rankedGadget l).blue)
  red_subset := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact old.tree.vertices_subset_graft _ _ _ (old.red_subset hw)
    · exact old.tree.liftMarks_subset_graft_vertices _ _ _ _
        (fun l => (old.tree.rankedGadget l).red_subset) hw
  blue_subset := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact old.tree.vertices_subset_graft _ _ _ (old.blue_subset hw)
    · exact old.tree.liftMarks_subset_graft_vertices _ _ _ _
        (fun l => (old.tree.rankedGadget l).blue_subset) hw
  root_not_red := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact old.root_not_red h
    · exact old.tree.root_not_mem_lift _
        (fun l => (old.tree.rankedGadget l).root_not_red) h
  root_not_blue := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact old.root_not_blue h
    · exact old.tree.root_not_mem_lift _
        (fun l => (old.tree.rankedGadget l).root_not_blue) h
  red_blue_disjoint := by
    apply Finset.disjoint_left.mpr
    intro w hr hb
    rcases Finset.mem_union.mp hr with hr | hr <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact Finset.disjoint_left.mp old.red_blue_disjoint hr hb
    · exact Finset.disjoint_left.mp
        (old.tree.old_marks_disjoint_lift old.red _ old.red_subset
          (fun l => (old.tree.rankedGadget l).root_not_blue)) hr hb
    · exact Finset.disjoint_left.mp
        (old.tree.old_marks_disjoint_lift old.blue _ old.blue_subset
          (fun l => (old.tree.rankedGadget l).root_not_red)) hb hr
    · exact Finset.disjoint_left.mp
        (old.tree.liftMarks_disjoint _ _
          (fun l => (old.tree.rankedGadget l).red_blue_disjoint)) hr hb
  red_level := by
    intro depth hpos _
    simpa only [extendPhaseQuota] using
      old.tree.levelCount_union_liftMarks_le old.red
        (fun l => (old.tree.rankedGadget l).red)
        old.red_subset (fun l => (old.tree.rankedGadget l).root_not_red)
        old.tree.leafRank old.tree.leafRank_injective
        (fun l _ hw => old.tree.rankedGadget_red_depth l hw)
        (fun l => (old.tree.rankedGadget_card_red l).le)
        old.quota old.red_level depth hpos
  blue_level := by
    intro depth hpos _
    simpa only [extendPhaseQuota] using
      old.tree.levelCount_union_liftMarks_le old.blue
        (fun l => (old.tree.rankedGadget l).blue)
        old.blue_subset (fun l => (old.tree.rankedGadget l).root_not_blue)
        old.tree.leafRank old.tree.leafRank_injective
        (fun l _ hw => old.tree.rankedGadget_blue_depth l hw)
        (fun l => (old.tree.rankedGadget_card_blue l).le)
        old.quota old.blue_level depth hpos
  total_count := by
    intro leaf hleaf
    obtain ⟨l, w, hw, rfl⟩ := old.tree.mem_nextPhase_leaves.mp hleaf
    rw [old.tree.colorCount_union_liftMarks old.red _ old.red_subset
        (fun l => (old.tree.rankedGadget l).root_not_red),
      old.tree.colorCount_union_liftMarks old.blue _ old.blue_subset
        (fun l => (old.tree.rankedGadget l).root_not_blue)]
    have hold := old.total_count l.val l.property
    have hnew := (old.tree.rankedGadget l).total_count w hw
    omega
  red_witness := by
    obtain ⟨l, hl, hold⟩ := old.red_witness
    let leaf : old.tree.leaves := ⟨l, hl⟩
    obtain ⟨w, hw, hnew⟩ := (old.tree.rankedGadget leaf).red_witness
    refine ⟨l ++ w, old.tree.mem_nextPhase_leaves.mpr ⟨leaf, w, hw, rfl⟩, ?_⟩
    change colorCount (old.red ∪ old.tree.liftMarks
      (fun l => (old.tree.rankedGadget l).red)) (leaf.val ++ w) = n + 1
    rw [old.tree.colorCount_union_liftMarks old.red _ old.red_subset
      (fun l => (old.tree.rankedGadget l).root_not_red) leaf w]
    exact congrArg₂ (· + ·) hold hnew
  blue_witness := by
    obtain ⟨l, hl, hold⟩ := old.blue_witness
    let leaf : old.tree.leaves := ⟨l, hl⟩
    obtain ⟨w, hw, hnew⟩ := (old.tree.rankedGadget leaf).blue_witness
    refine ⟨l ++ w, old.tree.mem_nextPhase_leaves.mpr ⟨leaf, w, hw, rfl⟩, ?_⟩
    change colorCount (old.blue ∪ old.tree.liftMarks
      (fun l => (old.tree.rankedGadget l).blue)) (leaf.val ++ w) = n + 1
    rw [old.tree.colorCount_union_liftMarks old.blue _ old.blue_subset
      (fun l => (old.tree.rankedGadget l).root_not_blue) leaf w]
    exact congrArg₂ (· + ·) hold hnew
  avoids := graft_avoids old old.tree.rankedGadget old.tree.leaves.card
    old.tree.rankedGadget_height old.tree.rankedGadget_quota

@[simp] theorem step_height {n : ℕ} (old : AuxiliaryTree n) :
    old.step.tree.height = old.tree.height + old.tree.leaves.card := rfl

end AuxiliaryTree

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ApproximationImpliesP
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ApproximationDecisionMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinaryEncoding
open BinPackingCompleteness.BinaryEncoding (bitsValue bitsValue_bits frame)

theorem borrowPred_value (bits : List Bool) :
    match borrowPred bits with
    | none => bitsValue bits = 0
    | some out => bitsValue bits = bitsValue out + 1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases bit with
    | true => simp [borrowPred, bitsValue, Nat.bit]
    | false =>
      cases h : borrowPred bits with
      | none => simp [borrowPred, h, bitsValue, Nat.bit] at ih ⊢; omega
      | some out => simp [borrowPred, h, bitsValue, Nat.bit] at ih ⊢; omega

theorem predWord_value (bits : List Bool) :
    bitsValue (predWord bits) = bitsValue bits - 1 := by
  have h := borrowPred_value bits
  cases hb : borrowPred bits with
  | none => simp [predWord, hb, bitsValue] at h ⊢; omega
  | some out => simp [predWord, hb] at h ⊢; omega

theorem process_length_le (count : Fin 5) (bits : List Bool) (assignments : List Nat) :
    (process count bits assignments).length ≤ bits.length := by
  induction assignments generalizing count bits with
  | nil => rfl
  | cons a tail ih =>
    simp only [process]
    by_cases h : count.val = 4
    · simpa only [ite_eq_left h] using
        (ih (nextCount count) (predWord bits)).trans (predWord_length_le bits)
    · simpa only [ite_eq_right h] using ih (nextCount count) bits

theorem process_value (count : Fin 5) (bits : List Bool) (assignments : List Nat) :
    bitsValue (process count bits assignments) =
      bitsValue bits - (count.val + assignments.length) / 5 := by
  induction assignments generalizing count bits with
  | nil => simp [process, Nat.div_eq_of_lt count.isLt]
  | cons a tail ih =>
    by_cases h : count.val = 4
    · have hq : (count.val + (a :: tail).length) / 5 = 1 + tail.length / 5 := by
        simp only [List.length_cons, h]; omega
      simp only [process, ite_eq_left h, nextCount, dite_eq_left h, ih, Fin.val_zero,
        Nat.zero_add, predWord_value, Nat.sub_sub, hq]
    · have hn : (nextCount count).val = count.val + 1 := by simp [nextCount, h]
      simp only [process, ite_eq_right h, ih, hn, List.length_cons]
      congr 2
      omega

theorem process_test (c bins : Nat) (assignments : List Nat) :
    bitsValue (process 0 bins.bits assignments) ≤ c ↔
      5 * bins ≤ assignments.length + 5 * c := by
  rw [process_value, bitsValue_bits]
  simp only [Fin.val_zero, Nat.zero_add]
  omega

def code (c : Nat) : Label → TM2.Stmt Alphabet Label Register
  | .start => .pop .input (fun _ bit => read bit)
      (.branch (fun state => (head state).getD false)
        (pushConstant c.bits.reverse (go .binRead)) (finish false))
  | .binRead => .pop .input (fun _ bit => read bit)
      (.branch (fun state => (head state).getD false)
        (.pop .input (fun _ bit => read bit)
          (.push .scratch (fun state => (head state).getD false) (go .binRead)))
        (go .binRestore))
  | .binRestore => loopAt .scratch .binary id false .binRestore (some (.items 0))
  | .items count => .pop .input (fun _ bit => read bit)
      (.branch (fun state => (head state).getD false) (go (.name count)) (go .compare))
  | .name count => .pop .input (fun _ bit => read bit)
      (.branch (fun state => (head state).getD false)
        (.pop .input (fun _ bit => read bit) (go (.name count)))
        (go (if count.val = 4 then .decrement else .items (nextCount count))))
  | .decrement => .pop .binary (fun _ bit => read bit)
      (.branch (fun state => (head state).isNone) (go .predDrain)
        (.branch (fun state => (head state).getD false)
          (.push .binary (fun _ => false) (go .predRestore))
          (.push .scratch (fun _ => true) (go .decrement))))
  | .predRestore => loopAt .scratch .binary id false .predRestore (some (.items 0))
  | .predDrain => .pop .scratch (fun _ bit => read bit)
      (.branch (fun state => (head state).isSome) (go .predDrain) (go (.items 0)))
  | .compare => BinaryOrderMachine.loop .binary .constant .compare orderExit
  | .answer bit => finish bit

def borrowOutput (bits : List Bool) (n : Nat) : List Bool :=
  match borrowPred bits with
  | none => []
  | some out => List.replicate n true ++ out

end BinPackingGap.ApproximationDecisionMachine

noncomputable section

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

def AbsoluteAdditiveAlgorithm.rawComputation {c : Nat}
    (algorithm : AbsoluteAdditiveAlgorithm c) :
    TM2ComputableInPolyTime BinaryEncoding.rawInstanceBits BinaryEncoding.packingResultBits
      (fun r => algorithm.run (BinaryEncoding.rawInstanceBits r)) where
  tm := algorithm.computation.tm
  inputAlphabet := algorithm.computation.inputAlphabet
  outputAlphabet := algorithm.computation.outputAlphabet
  time := algorithm.computation.time
  outputsFun r := algorithm.computation.outputsFun (BinaryEncoding.rawInstanceBits r)

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionCapacityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionFractionMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

abbrev State (A : Type) := BinaryAddMachine.State A

end BinPackingGap.ExtensionFractionMachine

end OAI
end


