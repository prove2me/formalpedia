-- Prove2me | Definitions.Def_OAIQ087A015
-- name    : OAIQ087A015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:26:39.546379+00:00
-- url     : https://prove2.me/theorems/39a557d0-1d9d-455f-8d20-6cafce1050c3
-- title:
--   Definitions bundle OAIQ087A015 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 501 declarations of OpenAI's Lean: 262 definitions, 5 inductive types or structures, 7 instances and 227 theorems. The definitions and types are `OAI.MaxCutGames.Decoder.ActualAdviceSampling.sampledAgreement`, `OAI.MaxCutGames.Decoder.ActualAdviceUpper.Visible`, `OAI.MaxCutGames.Decoder.ActualAdviceUpper.complementMap`, `OAI.MaxCutGames.Decoder.ActualAdviceUpper.fullInput`, `OAI.MaxCutGames.Decoder.ActualAdviceUpper.policies`, `OAI.MaxCutGames.Decoder.ActualAdviceUpper.projectedInput`, `OAI.MaxCutGames.Decoder.ActualAdviceUpper.rowMap`, `OAI.MaxCutGames.Decoder.ActualAdviceUpper.sourceIncidence`, `OAI.MaxCutGames.Decoder.ActualConditionalLaw.datumAgreement`, `OAI.MaxCutGames.Decoder.ActualConditionalLaw.homFintype`, `OAI.MaxCutGames.Decoder.ActualEvents.Context`, `OAI.MaxCutGames.Decoder.ActualEvents.FullTableSample`, `OAI.MaxCutGames.Decoder.ActualEvents.Sample`, `OAI.MaxCutGames.Decoder.ActualEvents.fullTableEquiv`, `OAI.MaxCutGames.Decoder.ActualEvents.homFintype`, `OAI.MaxCutGames.Decoder.ActualEvents.sliceEvent`, `OAI.MaxCutGames.Decoder.ActualEvents.targetHit`, `OAI.MaxCutGames.Decoder.ActualEvents.unrestricted`, `OAI.MaxCutGames.Decoder.ActualGoodRows.adviceMass`, `OAI.MaxCutGames.Decoder.ActualGoodRows.homFintype`, `OAI.MaxCutGames.Decoder.ActualGoodRows.table`, `OAI.MaxCutGames.Decoder.ActualProjectedTransfer.slopeVariation`, `OAI.MaxCutGames.Decoder.ActualSeedEvents.Datum`, `OAI.MaxCutGames.Decoder.ActualSeedEvents.Seed`, `OAI.MaxCutGames.Decoder.ActualSeedEvents.draw`, `OAI.MaxCutGames.Decoder.ActualSeedEvents.law`, `OAI.MaxCutGames.Decoder.ActualSeedEvents.pad`, `OAI.MaxCutGames.Decoder.ActualSeedEvents.slice`, `OAI.MaxCutGames.Decoder.ActualSeedEvents.targetHit`, `OAI.MaxCutGames.Decoder.ActualSeedSampling.drawAgreement`, `OAI.MaxCutGames.Decoder.ActualSeedVariation.homFintype`, `OAI.MaxCutGames.Decoder.ActualSpectral.fiberAcceptance`, `OAI.MaxCutGames.Decoder.ActualSpectral.homFintype`, `OAI.MaxCutGames.Decoder.AdviceExperiment.FullAdvice`, `OAI.MaxCutGames.Decoder.AdviceExperiment.ProjectedAdvice`, `OAI.MaxCutGames.Decoder.AdviceExperiment.leftObservation`, `OAI.MaxCutGames.Decoder.AdviceExperiment.paddedMatrix`, `OAI.MaxCutGames.Decoder.AdviceExperiment.projection`, `OAI.MaxCutGames.Decoder.AdviceExperiment.rightObservation`, `OAI.MaxCutGames.Decoder.AdviceLaw.actualSuccess` and 227 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_ActualAdviceSampling`, `MaxCut_Encoding_ActualAdviceUpper`, `MaxCut_Encoding_ActualEvents`, `MaxCut_Encoding_ActualGoodRows`, `MaxCut_Encoding_AdviceFibers`, `MaxCut_Encoding_AdviceLaw`, `MaxCut_Encoding_MatrixCoordinates`, `MaxCut_Encoding_PaddedLaw`, `MaxCut_Encoding_PrivateFourier`, `MaxCut_Encoding_SelectedPolicies`, `MaxCut_Encoding_SurrogateFibers`, `MaxCut_Encoding_TableKeys`, `MaxCut_Encoding_TableKeysAddressGame`, `MaxCut_Encoding_TableKeysGame`, `MaxCut_Encoding_TransferredDecoding`, `MaxCut_Encoding_VisibleTransfer`, `MaxCut_Games_AddressGame`, `MaxCut_Games_AddressOdometerSchedule`, `MaxCut_Games_AddressTupleLoaded`, `MaxCut_Games_CanonicalAddress`, `MaxCut_Games_CanonicalWordTemplate`, `MaxCut_Games_EquationLookup`, `MaxCut_Games_IncidenceExtraction`, `MaxCut_Games_MatrixNoise`, `MaxCut_Games_RawPrivateTable`, `MaxCut_Machines_AddressMachineInitial`, `MaxCut_Machines_AddressMachineLoop`, `MaxCut_Machines_AddressMachineProgram`, `MaxCut_Machines_CanonicalBodyMachine`, `MaxCut_Machines_CloneMachineModel`, `MaxCut_Machines_Machine`, `MaxCut_Machines_MachineHorner`, `MaxCut_Machines_MachineInitialHeaders`, `MaxCut_Machines_MachineRhsLoad`, `MaxCut_Machines_MachineSingleOrbitProgram`, `MaxCut_Machines_MachineTemplateAddress`, `MaxCut_Machines_MachineTuple`, `MaxCut_Machines_MachineUnaryMultiply`, `MaxCut_PCP_HeaderCounts`.
--
--   **Imports.** It imports the bundles `OAIQ087A007`, `OAIQ087A008` and `OAIQ087A009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A021`, `OAIQ087A022`, `OAIQ087A023`, `OAIQ087A025`, `OAIQ087A026` and `OAIQ087A027`; the statement `OAI.MaxCutGames.Decoder.ActualMatrixContradiction.contradiction`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A007
import Definitions.Def_OAIQ087A008
import Definitions.Def_OAIQ087A009

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Machine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complete-stack cleanup, with an arbitrary continuation. Each symbol
costs one transition and the empty-stack branch costs one final transition. -/

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace MaxCutGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def localInstruction (source : K) (labels : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineDrain.drain source (labels ()) exit

def instruction (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) :
    Label chosen → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction (LocalLabel (K := K)) (fun _ => ())
    localInstruction chosen labels exit

end MaxCutGames.Foundations.Complexity.MachineDrainMany

namespace MaxCutGames.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

/-- All instructions act on physical stacks. The final load only resets the
finite internal register; no input-dependent integer is stored in it. -/
def statement (clearKeys : List K) (accumulator output : K) (canonical : σ)
    (labels : Label clearKeys → Λ) (exit : Option Λ) :
    Label clearKeys → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl label => MachineDrainMany.instruction clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) label
  | .inr false => Reduction.MachineTransfer.loopAt accumulator output id false
      (labels (.inr false)) (some (labels (.inr true)))
  | .inr true => .load (fun _ => (canonical, none)) (Reduction.MachineTransfer.exitAt output exit)

open scoped BigOperators

end MaxCutGames.Foundations.Hastad.SourceRuntimeFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_IncidenceExtraction
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
This bridge connects the concrete partner projection to the actual equation/name
predicate of the incidence game. It uses no probabilistic or analytic hypotheses.
-/

namespace MaxCutGames.Reduction.ActualHomogeneous

open Integration.BinaryLinear
open scoped BigOperators

variable {k : Nat}

theorem finrank_E (k : Nat) : Module.finrank F2 (E k) = 1 + 2 * k := by
  simp [E, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]

end MaxCutGames.Reduction.ActualHomogeneous

/-! Canonical-row descent for every actual partner linear map. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RawPrivateTable
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The private Fourier table is defined from displayed data alone. Compatibility
with every hidden extension follows from the proved canonical locality theorem. -/

namespace MaxCutGames.Soundness.RawPrivateTable
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open PartnerProjection RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Id Name : Type}

variable (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
  {R D C Label : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]
  [DecidableEq Id] [DecidableEq Name]

def projection (occ : Fin k → Id) (slot : Fin k → Slot) :
    ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  rawProjection (fun j => toBit (rhs (occ j))) J slot

end
end MaxCutGames.Soundness.RawPrivateTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineUnaryMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An actual five-stack unary multiplication subroutine. Both isolated input
fields are preserved. The product field prefixes the previous output stack;
the counter and scratch return empty and all other stacks are framed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

/-- Slots 0 and 1 contain the operands, 2 the output, 3 the counter, and
4 the reusable empty scratch. The code is independent of operand values. -/
def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .copyDrain => Reduction.MachineTransfer.loopAt (slots 1) (slots 4) id false
      (labels .copyDrain) (some (labels .copyFork))
  | .copyFork => MachineCopy.forkLoop (slots 4) (slots 1) (slots 3) false
      (labels .copyFork) (some (labels .seed))
  | .seed => .push (slots 2) (fun _ => false) (.goto fun _ => labels .guard)
  | .guard => MachineUnaryCounter.guard (slots 3) (labels .scan) (labels .finish)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore)
  | .emitFalse => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () false
  | .emitTrue => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () true
  | .restore => Reduction.MachineTransfer.loopAt (slots 4) (slots 0) id false
      (labels .restore) (some (labels .guard))
  | .finish => .pop (slots 3) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 2) exit)

end MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

/-!
One actual Horner step on unary field stacks. Multiplication and addition are
executions of the same finite program. All three operands are preserved; only
the output stack receives a new field and both work stacks return empty.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRadixStep

open Turing

variable {K Λ σ : Type}

variable [DecidableEq K]

def statement (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .multiply label => MachineUnaryMultiply.statement (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) label
  | .digitDrain => Reduction.MachineTransfer.loopAt (slots 2) (slots 5) id false
      (labels .digitDrain) (some (labels .digitFork))
  | .digitFork => MachineCopy.forkLoop (slots 5) (slots 2) (slots 4) false
      (labels .digitFork) (some (labels .add))
  | .add => MachineUnaryAddAt.loop (slots 4) (slots 3) (labels .add) (some (labels .finish))
  | .finish => .pop (slots 4) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 3) exit)

end MaxCutGames.Foundations.Complexity.MachineRadixStep

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fixed-width Horner traversal by actual radix steps. Two accumulators alternate:
a radix step writes into the empty alternate, then the previous accumulator is
consumed. The base, digit fields, and arbitrary external tapes are preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

def statement (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => .push (slots (.inl 1)) (fun _ => false)
      (.load (fun state => (state.1, none)) (.goto fun _ => labels (entryLabel width 0)))
  | .radix i inner => MachineRadixStep.statement (radixSlots slots i)
      (fun l => labels (.radix i l)) (some (labels (.clear i))) inner
  | .clear i => drainLoop (slots (.inl (accumulator (parity i.val))))
      (labels (.clear i)) (some (labels (entryLabel width (i.val + 1))))
  | .finishDrain => Reduction.MachineTransfer.loopAt
      (slots (.inl (accumulator (parity width)))) (slots (.inl 5)) id false
      (labels .finishDrain) (some (labels .finishRestore))
  | .finishRestore => Reduction.MachineTransfer.loopAt (slots (.inl 5)) (slots (.inl 3)) id false
      (labels .finishRestore) exit

open scoped BigOperators

end MaxCutGames.Foundations.Complexity.MachineHorner

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_HeaderCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceHeaderCounts

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

def statement (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ) :
    Label p → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl _ => prependFields (word p slots) (indices p slots)
      (.goto fun _ => labels (inner p .start))
  | .inr (.inl l) => MachineHorner.statement slots (fun l => labels (inner p l))
      (some (labels (finish p))) l
  | .inr (.inr _) => clearFields (fun k => (word p slots k).length) (indices p slots)
      (Reduction.MachineTransfer.exitAt (slots (.inl 3)) exit)

end Eval

end

end MaxCutGames.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_AdviceFibers
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact visible row advice and private matrix coordinates

Every nonempty fiber of `M ↦ A ∘ M` is an affine copy of
`Hom(E, ker A)`, whether or not `A` is surjective.  Choosing one base matrix
for each attainable row gives a product decomposition of the complete matrix
space.  Uniform sampling therefore makes visible row advice and the hidden
kernel-valued matrix independent.
-/

/-! The finite set of realizable orbit records.  Vertices are the image of the
actual canonical-data map, so equal retained data from different questions
become one vertex.  The two sides remain distinct. -/

namespace MaxCutGames.Reduction.ActualOrbit

open MaxCutGames.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

def unfold (can : Q → Ambient s d × T) (label : Vertex can → Vector s) (q : Q) :
    Vector s := label (vertex can q) + offset can q

end MaxCutGames.Reduction.ActualOrbit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineInitialHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual caller-program traces for non-destructive unary-prefix emission and
the two headers of the raw initial graph. Unread suffixes are never scanned.
-/

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

namespace MaxCutGames.Foundations.Complexity.MachineOdometerInit
open Turing

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

/-- Place one of finitely many actual statements into an arbitrary ambient
Boolean-tape program, preserving the ambient state component. -/
def statement (tape : Tape k → K) (labels : Label k → Λ) (exit : Option Λ) :
    Label k → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .seed j => .push (tape (.current j)) (fun _ => false)
      (.goto (fun _ => labels (.copyOut j)))
  | .copyOut j => Reduction.MachineTransfer.loopAt (tape .radix) (tape .scratch)
      id false (labels (.copyOut j)) (some (labels (.copyBack j)))
  | .copyBack j => MachineCopy.forkLoop (tape .scratch) (tape .radix) (tape (.remaining j))
      false (labels (.copyBack j)) (some (labels (.trim j)))
  | .trim j => .pop (tape (.remaining j)) (fun state _ => state)
      (.goto (fun _ => labelAt labels (j.val+1)))
  | .done => .load (fun state => (state.1,none))
      (Reduction.MachineTransfer.exitAt (tape .radix) exit)

end MaxCutGames.Foundations.Complexity.MachineOdometerInit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_PaddedLaw
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual linear-map realization of the sparse padded-table experiment.
The finite sample has one independent full pair or singleton coefficient at
each occurrence position and one independent homogeneous intercept. Its map
is formed by composing a genuine map on the raw projected target with the
actual parity projection. The third position contributes its parity-dependent
intercept; it is not treated as a homogeneous two-coordinate projection.
-/

namespace MaxCutGames.Decoder.PaddedLaw

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget RawMapLaw
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

def drawCoefficients (d : Fin k → BlockDraw V) (z : V) :
    RawCoefficients (singletonPositions d) V
  | none => z
  | some (.inl (j, i)) =>
      match d j.val with
      | .inl ab => if i = 0 then ab.1 else ab.2
      | .inr _ => 0
  | some (.inr j) =>
      match d j.val with
      | .inl _ => 0
      | .inr ia => ia.2

def paddedMap (rhs : Fin k → Bool) (d : Fin k → BlockDraw V) (z : V) :
    ActualHomogeneous.E k →ₗ[F2] V :=
  (rawMap (singletonPositions d) V (drawCoefficients d z)).comp
    (rawProjection rhs (singletonPositions d) (drawSlots d))

variable [Fintype V]

omit [Module F2 V] in
theorem blockWeights_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    MaxCutGames.Foundations.Information.IsProbability (blockWeights (V := V) β) := by
  constructor
  · intro d
    cases d with
    | inl ab => exact mul_nonneg (sub_nonneg.mpr hβ') (uniformWeights_pos ab).le
    | inr ia => exact mul_nonneg (div_nonneg hβ (by norm_num)) (uniformWeights_pos ia.2).le
  · rw [Fintype.sum_sum_type]
    simp only [blockWeights, ← Finset.mul_sum,
      (uniformWeights_isProbability (α := V × V)).2, mul_one, Fintype.sum_prod_type,
      (uniformWeights_isProbability (α := V)).2]
    simp

end
end MaxCutGames.Decoder.PaddedLaw

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TableKeys
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact affine-table keys for the v2 outer questions

The retained data has one entry at every original block position.  A full entry
contains the equation *occurrence ID*, a singleton entry contains the actual
variable ID, and the first component is the entire reduced affine intercept.
The common coefficient-normalization implementation below is independent of
every latent-gadget existence or inverse theorem.

The explicit binary slope cases justify its use for the v2 rank-zero, rank-one,
and rank-two rule.  In particular, the third-position pullback adds the parity
intercept twice, so exact sharing preserves the intercept as well as the slopes.
-/

namespace MaxCutGames.Decoder.TableKeys

section

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open scoped BigOperators

universe u v w

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
variable {k : Nat}

def key (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (P : ActualHomogeneous.E k →ₗ[F2] R) : Key k Name Id R :=
  ActualCanonical.canonical occ names rhs P

variable [DecidableEq Name] [DecidableEq Id]

/-- The reduced table attached to visible data is independent of the compatible
full question used to realize it.  This is equality of the entire key. -/
noncomputable def projectedKey (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (Q : RawPrivateTable.SupportedV J names) (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) :
    Key k Name Id R :=
  key (RawPrivateTable.representative Q).1 names rhs
    (Y.comp (RawPrivateTable.projection J rhs (RawPrivateTable.representative Q).1
      (RawPrivateTable.representative Q).2))

end

/-! Surjective affine-coordinate projection and uniqueness of visible tables. -/

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R]
variable {k : Nat}

/-- Read the shared homogeneous coordinate in the visible coordinate system. -/
def visibleTau (J : Finset (Fin k)) : RawPartnerTarget.RawPoint J →ₗ[F2] F2 :=
  LinearMap.proj none

end MaxCutGames.Decoder.TableKeys

/-!
The concrete observation maps of the v2 projected-advice experiment.

The full hidden draw contains the equation occurrence IDs, singleton positions,
projection choices, public row map, and the two sampled tables. The observations
are precisely `(U,A,Tπ,AMπ)` and `(O,A,T,AM)`. The hidden matrix is absent from
both observation types. Changing its kernel-valued part preserves both inputs
and hence every deterministic witness or strategy chosen from those inputs.
-/

namespace MaxCutGames.Decoder.AdviceExperiment

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness

noncomputable section

variable (k : Nat) (Id K W R : Type)
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup W] [Module F2 W]
variable [AddCommGroup R] [Module F2 R]

/-- The first prover's entire information; no singleton-choice or private
matrix field is present. -/
structure FullAdvice where
  occurrences : Fin k → Id
  rowMap : K →ₗ[F2] R
  complement : ActualHomogeneous.E k →ₗ[F2] W
  rows : ActualHomogeneous.E k →ₗ[F2] R

variable {k Id K W R}

variable {Name : Type} (names : Id → Fin 3 → Name)

/-- The second prover sees actual equation/variable tags, retaining ordered
block positions but omitting every hidden singleton occurrence ID. -/
structure ProjectedAdvice (J : Finset (Fin k)) where
  question : RawPrivateTable.SupportedV J names
  rowMap : K →ₗ[F2] R
  complement : RawPartnerTarget.RawPoint J →ₗ[F2] W
  rows : RawPartnerTarget.RawPoint J →ₗ[F2] R

variable (rhs : Id → F2)

def projection (d : Draw k Id K W R) :
    ActualHomogeneous.E k →ₗ[F2] RawPartnerTarget.RawPoint d.singletons :=
  RawPrivateTable.projection d.singletons rhs d.occurrences d.positions

def leftObservation (d : Draw k Id K W R) : FullAdvice k Id K W R where
  occurrences := d.occurrences
  rowMap := d.rowMap
  complement := d.complement.comp (projection rhs d)
  rows := (d.rowMap.comp d.hiddenMatrix).comp (projection rhs d)

def rightObservation (d : Draw k Id K W R) :
    (J : Finset (Fin k)) × ProjectedAdvice (K := K) (W := W) (R := R) names J :=
  ⟨d.singletons, {
    question := RawPrivateTable.supported d.singletons names d.occurrences d.positions
    rowMap := d.rowMap
    complement := d.complement
    rows := d.rowMap.comp d.hiddenMatrix }⟩

/-- The same full sampled table used in the unconditional variation comparison.
Its projection choices have not been supplied as extra compared coordinates. -/
def paddedMatrix (d : Draw k Id K W R) : ActualHomogeneous.E k →ₗ[F2] K :=
  d.hiddenMatrix.comp (projection rhs d)

end
end MaxCutGames.Decoder.AdviceExperiment

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_AdviceLaw
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual finite advice law. Uniform independent hidden/complement maps induce
the exact uniform visible-map law, including for rank-deficient public maps.
The whole-table comparison retains an arbitrary common occurrence/public-data
law, so weighted occurrence sampling is not replaced by uniform IDs.
-/

namespace MaxCutGames.Decoder.AdviceLaw

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Soundness
open ConditionalIncidences RawPartnerTarget RawMapLaw
open MaxCutGames.Foundations.Games
open MaxCutGames.Clean

noncomputable section
attribute [local instance] Classical.propDecidable

section VisibleMap

variable {k : ℕ} {K W R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup W] [Module F2 W] [Fintype W]
  [AddCommGroup R] [Module F2 R] [Fintype R]

/-- The precise visible table `(T,A M)`, with the second component in its
actual attainable range. The argument order is complement, hidden matrix. -/
def visibleMap (A : K →ₗ[F2] R) {J : Finset (Fin k)}
    (T : RawPoint J →ₗ[F2] W) (M : RawPoint J →ₗ[F2] K) :
    RawPoint J →ₗ[F2] (W × A.range) :=
  T.prod (A.rangeRestrict.comp M)

def rawMapPairCoefficientsEquiv (J : Finset (Fin k)) :
    ((RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K)) ≃
      (RawSlot J → W × K) :=
  (Equiv.prodCongr (rawMapEquiv J W).symm (rawMapEquiv J K).symm).trans
    (Equiv.arrowProdEquivProdArrow (RawSlot J) (fun _ => W) (fun _ => K)).symm

variable {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

/-- Actual success starts with genuinely sampled hidden and complement maps.
The iid incidence law includes every slot choice, including unused choices at
full positions. Policies receive only their respective visible table. -/
def actualSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (A : K →ₗ[F2] R)
    (policy : ActualAdviceStochasticBridge.Policies k g (W × A.range))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      ((RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] W) ×
        (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] K))).expectation fun TM =>
      ActualAdviceStochasticBridge.fixedMapSuccess μ g policy
        (NativeExperiment.maskSet mask) (visibleMap A TM.1 TM.2)

end VisibleMap

section WholeTable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
  [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

def drawDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution ((Fin k → PaddedLaw.BlockDraw V) × V) where
  weight := PaddedLaw.drawWeights β k
  nonnegative dz := mul_nonneg
    ((SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).1 dz.1)
    (SparseLaw.uniformWeights_pos dz.2).le
  normalized := by
    rw [Fintype.sum_prod_type]
    simp only [PaddedLaw.drawWeights, ← Finset.mul_sum,
      (SparseLaw.uniformWeights_isProbability (α := V)).2, mul_one]
    exact (SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).2

def paddedDistribution (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ActualHomogeneous.E k →ₗ[F2] V) :=
  (drawDistribution β hβ hβ').pushforward (fun dz => PaddedLaw.paddedMap rhs dz.1 dz.2)

end WholeTable

section HiddenRows

variable {k : ℕ} {K R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup R] [Module F2 R] [Fintype R]

instance observedRowsFintype (J : Finset (Fin k)) (A : K →ₗ[F2] R) :
    Fintype (AdviceFibers.ObservedRow (E := RawPoint J) A) := Fintype.ofFinite _

end HiddenRows

section ProjectionSeeds

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]

def projectionSeedDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ProjectionSeed k V) where
  weight s := PaddedLaw.choiceTupleWeight β s.1 * SparseLaw.uniformWeights _ s.2
  nonnegative s := mul_nonneg
    ((PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').1 s.1)
    (SparseLaw.uniformWeights_pos s.2).le
  normalized := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (SparseLaw.uniformWeights_isProbability).2, mul_one]
    exact (PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').2

def projectSeedMap (rhs : Fin k → Bool) (s : ProjectionSeed k V) :
    ActualHomogeneous.E k →ₗ[F2] V :=
  s.2.comp (rawProjection rhs (PaddedLaw.choiceMask s.1) (PaddedLaw.choiceSlots s.1))

end ProjectionSeeds

section ActualDraw

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

/-- Convert the actual two-stage seed into the full hidden experiment. The
second summand of the seed remains available for the target-side observation. -/
def seedToActualDraw (occ : Fin k → Id) (A : K →ₗ[F2] R)
    (s : ProjectionSeed k (K × W)) : AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask s.1
  occurrences := occ
  positions := PaddedLaw.choiceSlots s.1
  rowMap := A
  hiddenMatrix := (LinearMap.fst F2 K W).comp s.2
  complement := (LinearMap.snd F2 K W).comp s.2

end ActualDraw

/-- A finite hidden sample whose actual Draw is `seedToActualDraw`. -/
def fullSeedLaw {k : ℕ} {Id A V : Type} [Fintype Id] [Fintype A]
    [AddCommGroup V] [Module F2 V] [Fintype V]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :=
  (occurrences.product publicLaw).product (projectionSeedDistribution (k := k) (V := V) β hβ hβ')

def fullSeedPad {k : ℕ} {Id A V : Type} [AddCommGroup V] [Module F2 V]
    (rhs : Id → Bool) (s : ((Fin k → Id) × A) × ProjectionSeed k V) :
    ((Fin k → Id) × A) × (ActualHomogeneous.E k →ₗ[F2] V) :=
  (s.1, projectSeedMap (fun j => rhs (s.1.1 j)) s.2)

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

/-- The actual Draw obtained from the complete-data fiber coordinates. -/
def completeDraw (d : CompleteData k Id K W R) (N : PrivateMap d) :
    AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask d.2.1
  occurrences := d.1.1
  positions := PaddedLaw.choiceSlots d.2.1
  rowMap := d.1.2
  hiddenMatrix := AdviceFibers.assemble d.1.2 (AdviceFibers.observedBase d.1.2 d.2.2.2) N
  complement := d.2.2.1

theorem completeDraw_rows (d : CompleteData k Id K W R) (N : PrivateMap d) :
    (completeDraw d N).rowMap.comp (completeDraw d N).hiddenMatrix = d.2.2.2.val := by
  exact (AdviceFibers.observed_assemble _ _ N).trans
    (AdviceFibers.observedBase_property _ _)

theorem completeDraw_left (rhs : Id → F2) (d : CompleteData k Id K W R)
    (N : PrivateMap d) :
    AdviceExperiment.leftObservation rhs (completeDraw d N) = {
      occurrences := d.1.1, rowMap := d.1.2,
      complement := d.2.2.1.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)),
      rows := d.2.2.2.val.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)) } := by
  simp only [AdviceExperiment.leftObservation, completeDraw_rows] ; rfl

variable [Fintype Id] [Fintype K] [Fintype W] [Fintype R] [Fintype (K →ₗ[F2] R)]

def completeWeight (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (d : CompleteData k Id K W R) : ℝ :=
  (occurrences.weight d.1.1 * publicLaw.weight d.1.2) *
    (PaddedLaw.choiceTupleWeight β d.2.1 *
      (1 / (Fintype.card (RawPoint (PaddedLaw.choiceMask d.2.1) →ₗ[F2] (K × W)) : ℝ)))

end
end MaxCutGames.Decoder.AdviceLaw

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixNoise
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MaxCutGames.Fourier.MatrixNoise

open scoped BigOperators Matrix
open MaxCutGames.Integration.BinaryLinear (Vector)
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- Evaluation of a uniformly chosen linear functional is a binary character. -/
def evaluationCharacter (w : E) : AddChar (E →ₗ[F2] F2) ℂ where
  toFun ℓ := binarySign (ℓ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp only [LinearMap.add_apply, binarySign_add]

@[simp] theorem evaluationCharacter_apply (w : E) (ℓ : E →ₗ[F2] F2) :
    evaluationCharacter w ℓ = binarySign (ℓ w) := rfl

end MaxCutGames.Fourier.MatrixNoise
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_PrivateFourier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Decoder.PrivateFourier

open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open scoped BigOperators Classical

section Signs

/-- A real-valued binary character, with the uniform Fourier normalization. -/
def sign (a : F2) : ℝ := (binarySign a).re

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

theorem sign_sq (a : F2) : sign a ^ 2 = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

@[simp] theorem sign_abs (a : F2) : |sign a| = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

end Signs

section ActualFourier

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]

/-- The private sign function, formed from the table on one visible row fiber. -/
def tableSign (F : (E →ₗ[F2] H) → K) (σ : K →ₗ[F2] F2)
    (N : E →ₗ[F2] H) : ℝ := sign (σ (F N))

/-- The actual probability assigned to a reverse-map frequency. -/
def frequencyWeight (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) : ℝ :=
  linearCoeff f Φ ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (H →ₗ[F2] E)] in
theorem frequencyWeight_nonneg (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) :
    0 ≤ frequencyWeight f Φ := sq_nonneg _

/-- Squared Fourier coefficients of the private sign form a probability law. -/
theorem tableSign_frequencyWeight_sum (F : (E →ₗ[F2] H) → K)
    (σ : K →ₗ[F2] F2) :
    ∑ Φ : H →ₗ[F2] E, frequencyWeight (tableSign F σ) Φ = 1 := by
  simp only [frequencyWeight, linear_parseval, tableSign, sign_sq]
  exact Fintype.expect_const 1

end ActualFourier

end MaxCutGames.Decoder.PrivateFourier

/-!
# Actual private response laws for v2 Fourier decoding

The right response law has only its row-fiber table, the inclusion of its hidden
kernel, a first-bit map, and an actual fallback answer as arguments.  In
particular it has no column slice or witness.  Zero-mass invalid frequencies
are repaired to the fallback so that the response type always consists of
actual answers.  Witness data occur only in the success analysis.
-/

namespace MaxCutGames.Decoder.PrivateStrategy

attribute [local instance] Classical.propDecidable

open PrivateFourier
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Foundations.Games
open scoped BigOperators Classical

section Candidates

variable {E E' : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup E'] [Module F2 E'] [Fintype E]

def candidates (Z : Submodule F2 E) (z : E) (τ : E →ₗ[F2] F2) : Finset E :=
  Finset.univ.filter fun v => v - z ∈ Z ∧ τ v = 1

theorem mem_candidates (Z : Submodule F2 E) (z v : E) (τ : E →ₗ[F2] F2) :
    v ∈ candidates Z z τ ↔ v - z ∈ Z ∧ τ v = 1 := by simp [candidates]

end Candidates

section RightRule

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

omit [FiniteDimensional F2 H] in
theorem exists_unit (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) : ∃ h, σ h = 1 := by
  have hn : ∃ h, σ h ≠ 0 := by
    by_contra hh
    apply hne
    ext h
    by_contra hh'
    exact hh ⟨h, hh'⟩
  obtain ⟨h, hh⟩ := hn
  exact ⟨h, (MaxCutGames.Integration.BinaryLinear.scalar_cases _).resolve_left hh⟩

def chooseUnit (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) : H :=
  Classical.choose (exists_unit σ hne)

abbrev ActualAnswer (τ : E →ₗ[F2] F2) := {v : E // τ v = 1}

/-- The uniform output character followed by its actual Fourier frequency. -/
def privateSeedLaw (F : (E →ₗ[F2] H) → K) :
    FiniteDistribution ((K →ₗ[F2] F2) × (H →ₗ[F2] E)) where
  weight p := frequencyWeight (tableSign F p.1) p.2 /
    (Fintype.card (K →ₗ[F2] F2) : ℝ)
  nonnegative p := div_nonneg (frequencyWeight_nonneg _ _) (Nat.cast_nonneg _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_div, tableSign_frequencyWeight_sum]
    simp [Fintype.card_ne_zero]

/-- The decoder receives no left witness.  The first-bit repair affects only
zero-mass frequencies when the table is folded. -/
def privateOutput (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2)
    (fallback : ActualAnswer τ) (p : (K →ₗ[F2] F2) × (H →ₗ[F2] E)) :
    ActualAnswer τ :=
  if hn : p.1.comp ι = 0 then fallback else
    let v := p.2 (chooseUnit (p.1.comp ι) hn)
    if hv : τ v = 1 then ⟨v, hv⟩ else fallback

/-- This is an actual finite distribution on actual answers, for every visible
row table.  The sampler's normalization is Parseval, not a hypothesis. -/
def privateLaw [Fintype E] (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) :
    FiniteDistribution (ActualAnswer τ) :=
  (privateSeedLaw F).pushforward (privateOutput ι τ fallback)

end RightRule

section LeftRule

variable {E : Type*} [AddCommGroup E] [Module F2 E] [Fintype E]

/-- The left rule is uniform on its own chosen affine-answer candidates. -/
def candidateLaw (Z : Submodule F2 E) (z : E) (τ : E →ₗ[F2] F2)
    (hz : τ z = 1) : FiniteDistribution (ActualAnswer τ) := by
  letI : Nonempty {v // v ∈ candidates Z z τ} :=
    ⟨⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩⟩
  exact (FiniteDistribution.uniform {v // v ∈ candidates Z z τ}).pushforward
    (fun v => ⟨v.1, ((mem_candidates Z z v.1 τ).1 v.2).2⟩)

end LeftRule

end MaxCutGames.Decoder.PrivateStrategy
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TableKeysGame
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.TableKeysGame

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction
open ActualSource Foundations.Target
open scoped BigOperators

abbrev Question (S : Source) (k : Nat) := ActualGame.Question S k
abbrev Map (k s d : Nat) := ActualGame.Map k s d
abbrev shiftQuery (S : Source) (k s d : Nat) := ActualGame.shiftQuery S k s d

/-- Restore the removed alphabet component of the affine intercept. -/
noncomputable def unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (q : Query S k s d) : Alphabet s :=
  ActualOrbit.unfold (canonical S k s d) (vertexLabel S k s d labeling) q

theorem unfolded_equivariant (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (q : Query S k s d) (c : Alphabet s) :
    unfolded S k s d labeling (shiftQuery S k s d c q) =
      unfolded S k s d labeling q + c := by
  change vertexLabel S k s d labeling
      (ActualGame.vertex S k s d (ActualGame.shiftQuery S k s d c q)) +
    ActualGame.offset S k s d (ActualGame.shiftQuery S k s d c q) = _
  rw [ActualGame.vertex_shiftQuery, ActualGame.offset_shiftQuery]
  exact (add_assoc _ _ _).symm

end MaxCutGames.Decoder.TableKeysGame

/-!
Restore actual orbit labels as a total function of the entire reduced key.
The arbitrary value at unrealized orbit bodies is used only to make this
function total; every table queried by the verifier and by the sparse
experiment is proved to be an actual realization.  Folding holds even for
the total extension, because the removed intercept is always restored.
-/

namespace MaxCutGames.Decoder.TableKeysRestoration

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

section OrbitExtension

variable {Q T : Type} {s d : Nat}

def extendedLabel (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (body : Vector d × T) : Alphabet s :=
  if h : ∃ q, ActualOrbit.body can q = body then label ⟨body, h⟩ else 0

/-- Restore the full affine intercept after labeling the orbit body. -/
def restoredData (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (D : Ambient s d × T) : Alphabet s :=
  extendedLabel can label (D.1.2, D.2) + D.1.1

end OrbitExtension

/-- The actual verifier labeling, viewed as a function of exact affine keys. -/
def keyAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (D : TableKeys.Key k (Fin S.«variables») (Fin S.occurrences) (Ambient s d)) : Alphabet s :=
  restoredData (TableKeysGame.canonical S k s d)
    (TableKeysGame.vertexLabel S k s d labeling) D

def projectedAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) : Alphabet s :=
  keyAnswer S k s d labeling
    (TableKeys.projectedKey J (ActualGame.names S) (ActualGame.rhs S) O Y)

end

end MaxCutGames.Decoder.TableKeysRestoration

/-!
The private row table obtained from an actual single-orbit labeling.  Its
parameters are only the visible question, public row map, visible row value,
and complement table.  Neither a hidden full question nor a selected affine
witness is supplied to its definition.  Affine target intercepts remain
explicit when the matrix is expressed in private kernel coordinates.
-/

namespace MaxCutGames.Decoder.TableKeysPrivateRow

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ActualSource

noncomputable section

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

/-- The right player's actual private table, formed from visible row advice. -/
def rowAnswer (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker) : Alphabet s :=
  TableKeysRestoration.projectedAnswer S k s d labeling J Q
    ((AdviceFibers.assemble A (AdviceFibers.observedBase A rows) N).prod T)

end

end MaxCutGames.Decoder.TableKeysPrivateRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TransferredDecoding
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Decoding an actual transferred column slice

The point `Mstar` used to parametrize a transferred slice is distinct from the
canonical visible row base `observedBase A rows`.  The right strategy uses only
the latter.  Their kernel-valued difference appears solely in the analysis.
The exact quotient equivalence transports uniform slice agreement, including
the affine offset, to the conditional private-decoder theorem.
-/

noncomputable section

namespace MaxCutGames.Decoder.TransferredDecoding

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ActualSource
open PrivateFourier PrivateStrategy
open scoped BigOperators Classical

open MaxCutGames.Inverse

attribute [local instance] Fintype.ofFinite

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

local instance homFintype_r2c6deb_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
/-- A default actual projected answer depends only on the displayed positions. -/
def visibleFallback (J : Finset (Fin k)) : ActualAnswer (TableKeys.visibleTau J) :=
  ⟨Pi.single none 1, by simp [TableKeys.visibleTau]⟩

end MaxCutGames.Decoder.TransferredDecoding

namespace MaxCutGames.Decoder.VisiblePolicies

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
open ActualSource PrivateStrategy
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- The part of a normalized affine witness needed by the left sampler. -/
structure ResponseWitness (k : ℕ) where
  columns : Submodule F2 (ActualHomogeneous.E k)
  coefficient : ActualHomogeneous.E k
  firstBit : ActualHomogeneous.tau coefficient = 1

def defaultWitness (k : ℕ) : ResponseWitness k :=
  ⟨⊥, ActualHomogeneous.hBasis k, ActualHomogeneous.tau_hBasis⟩

variable {k s d : ℕ} {R : Type} [AddCommGroup R] [Module F2 R]

abbrev LeftInput (S : Source) (k s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.FullAdvice k (Fin S.occurrences) (Alphabet s) (Vector d) R

abbrev RightInput (S : Source) (J : Finset (Fin k)) (s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.ProjectedAdvice (K := Alphabet s) (W := Vector d) (R := R)
    (ActualGame.names S) J

/-- The witness choice has only the left observation as its variable input. -/
def chosenWitness {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) : ResponseWitness k :=
  if h : ∃ w, good q w then Classical.choose h else defaultWitness k

def leftPolicy {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) : FiniteDistribution (ActualAnswer (ActualHomogeneous.tau (k := k))) :=
  let w := chosenWitness good q
  candidateLaw w.columns w.coefficient ActualHomogeneous.tau w.firstBit

/-- The right kernel consumes its own complete visible observation only. -/
def rightPolicy (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (q : RightInput S J s d R) :
    FiniteDistribution (ActualAnswer (TableKeys.visibleTau J)) :=
  if h : ∃ M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s,
      q.rowMap.comp M = q.rows then
    privateLaw
      (TableKeysPrivateRow.rowAnswer S labeling J q.question q.rowMap ⟨q.rows, h⟩ q.complement)
      q.rowMap.ker.subtype (TableKeys.visibleTau J) (TransferredDecoding.visibleFallback J)
  else pointLaw (TransferredDecoding.visibleFallback J)

/-- The literal product of the two observation-local stochastic responses. -/
def observedAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) : ℝ :=
  ((leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)).product
    (rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2)).probability
    (fun answers => decide
      (AdviceExperiment.projection (ActualGame.rhs S) draw answers.1.1 = answers.2.1))

end MaxCutGames.Decoder.VisiblePolicies
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualAdviceUpper
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The clean-coordinate upper bound for the actual private-decoding policies.
At every fixed public map `A`, the visible coefficient space is
`Vector d × A.range`.  Its cardinality is at most `2^(d+rs)`, including when
`A` is rank deficient.  The true independent uniform maps `T,M`, the
Bernoulli mask, and all iid occurrence/position draws are retained by the
proved sampling equality, before averaging over the uniform public map.
-/

namespace MaxCutGames.Decoder.ActualAdviceUpper

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

instance publicMapFintype (s rs : Nat) : Fintype (Alphabet s →ₗ[F2] Vector rs) :=
  Fintype.ofInjective (fun A : Alphabet s →ₗ[F2] Vector rs => (A : Alphabet s → Vector rs))
    DFunLike.coe_injective

/-- The ordinary game uses actual occurrence IDs and actual variable names. -/
def sourceIncidence (S : Source) :
    IncidenceExtraction.Incidence (Fin S.occurrences) (Fin S.«variables») where
  name := ActualGame.names S
  rhs e := (S.equation e).rhs

abbrev Visible (d : Nat) (A : Alphabet s →ₗ[F2] Vector rs) := Vector d × A.range

def complementMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector d :=
  (LinearMap.fst F2 (Vector d) A.range).comp Y

def rowMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector rs :=
  A.range.subtype.comp ((LinearMap.snd F2 (Vector d) A.range).comp Y)

/-- Decode only the data visible to the first player. -/
def fullInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (occ : Fin k → Fin S.occurrences)
    (Y : ActualHomogeneous.E k →ₗ[F2] Visible d A) :
    VisiblePolicies.LeftInput S k s d (Vector rs) where
  occurrences := occ
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

/-- Decode only the displayed question and the visible row/complement maps. -/
def projectedInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Visible d A) :
    VisiblePolicies.RightInput S J s d (Vector rs) where
  question := O
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

/-- Actual observation-local stochastic policies, in the exact advice space
used by the clean-coordinate experiment.  Public `A` is fixed before questions. -/
def policies (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) :
    Clean.ActualAdviceStochasticBridge.Policies k (sourceIncidence S) (Visible d A) where
  first _ occ Y := VisiblePolicies.leftPolicy good (fullInput S A occ Y)
  second J O Y := VisiblePolicies.rightPolicy S labeling J (projectedInput S A J O Y)

end

end MaxCutGames.Decoder.ActualAdviceUpper

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CanonicalAddress
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct canonical-body addresses. The fixed list of canonical words is
interpreted in big-endian order, matching forward Horner steps `B*acc+digit`.
Unused addresses represent isolated vertices. These are semantic encoding and
polynomial-size results, not an assumed machine implementation. -/

/-! Finite noise tables for the executable outer reduction. Positions, including
positions containing equal vectors, remain distinct sample outcomes. -/

namespace MaxCutGames.Integration.NoiseTables

open BinaryLinear MaxCutGames.Reduction.ActualSource

variable {s d : Nat}

namespace Table

def gadget (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : SplitGadget s d where
  f := f
  equivariant := hf
  NoiseIndex := Fin T.vectors.length
  noiseFintype := inferInstance
  noiseNonempty := ⟨⟨0, List.length_pos_iff.mpr T.nonempty⟩⟩
  noise := T.vectors.get

end Table
end MaxCutGames.Integration.NoiseTables

namespace MaxCutGames.Integration.TableReduction

open BinaryLinear NoiseTables MaxCutGames.Reduction.ActualSource
open MaxCutGames.Reduction.ActualGame MaxCutGames.Foundations.Target

variable {s d : Nat}

def tableEnumeration (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : NoiseEnumeration (T.gadget f hf) where
  indices := List.finRange T.vectors.length
  nodup := List.nodup_finRange _
  complete i := List.mem_finRange i

/-- The projection is used only to fill an erased witness field. It is never
used when generating constraints or evaluating their permutation tables. -/
def tableSkeleton (T : Table s d) : SplitGadget s d :=
  T.gadget Prod.fst (fun _ _ => rfl)

end MaxCutGames.Integration.TableReduction

/-! Injective vertex addresses may leave unused output vertices. The actual
instance is obtained by mapping endpoints in the original constraint list;
constraint order, multiplicity, and permutation tables are retained exactly. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TableKeysAddressGame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Direct addresses for the v2 single-orbit matrix game. There is one canonical
body address space, with no side bit and no extra right-endpoint offset.
Unused addresses are isolated. Runtime construction uses canonical words and
radix arithmetic, not deduplication or inverse vertex enumeration.
-/

namespace MaxCutGames.Decoder.TableKeysAddressGame

open MaxCutGames.Reduction
open ActualSource Foundations.Target
open Integration.VertexEmbedding

abbrev vertexCount (S : Source) (k s d : Nat) : Nat :=
  CanonicalAddress.capacity S.«variables» S.occurrences k s d

def vertexAddress (S : Source) (k s d : Nat) (v : TableKeysGame.Vertex S k s d) :
    Fin (vertexCount S k s d) := CanonicalAddress.bodyAddress v.val

/-- Both endpoints use this same routine and this same address block. -/
def queryAddress (S : Source) (k s d : Nat) (q : TableKeysGame.Query S k s d) :
    Fin (vertexCount S k s d) :=
  CanonicalAddress.bodyAddress (ActualOrbit.body (TableKeysGame.canonical S k s d) q)

@[simp] theorem vertexAddress_query (S : Source) (k s d : Nat)
    (q : TableKeysGame.Query S k s d) :
    vertexAddress S k s d (TableKeysGame.vertex S k s d q) =
      queryAddress S k s d q := rfl

/-- This inverse is a proof adapter only; the output constructor never calls it. -/
def explicitToAddress (S : Source) (k s d : Nat) :
    Fin (TableKeysGame.explicitVertexCount S k s d) → Fin (vertexCount S k s d) :=
  fun i => vertexAddress S k s d ((TableKeysGame.explicitVertexEncoding S k s d).symm i)

@[simp] theorem explicitToAddress_apply (S : Source) (k s d : Nat)
    (v : TableKeysGame.Vertex S k s d) :
    explicitToAddress S k s d (TableKeysGame.explicitVertexEncoding S k s d v) =
      vertexAddress S k s d v := by
  simp only [explicitToAddress, Equiv.symm_apply_apply]

def addressEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : TableKeysGame.Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := queryAddress S k s d (TableKeysGame.leftQuery S k g ω)
  target := queryAddress S k s d (TableKeysGame.rightQuery S k g ω)
  permutation := Encoding.translationTable
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))

/-- The correcting function is not evaluated when producing an edge list. -/
def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (addressEdge S k g)
  nonempty h := by
    have hempty := List.map_eq_nil_iff.mp h
    apply (TableKeysGame.outputInstanceWithEnumeration S k g en).nonempty
    change (ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g) = []
    rw [hempty]
    rfl

@[simp] theorem outputInstance_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstance S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstance, List.length_map, ActualGame.explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

end MaxCutGames.Decoder.TableKeysAddressGame

/-! Transport the matrix-test bound to the actual direct-address edge list.
Every address labeling restricts to a semantic orbit labeling, with exactly
the same satisfied fraction and the same occurrence multiplicities. -/

/-!
Completeness on the actual single-orbit address output. An honest semantic
labeling is extended over unused addresses, with its satisfied fraction
unchanged. The two rational error bounds need no packaged error parameter.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CanonicalWordTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.CanonicalBodyTemplate

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding
open scoped BigOperators

variable {k : Nat}

theorem flatMap_encodeWord (fields : Fin k → Fin 4 → Nat) (tokens : List (Token k)) :
    tokens.flatMap (fun token => encodeWord (evalToken fields token)) =
      encodeWords (evalTemplate fields tokens) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.flatMap_cons, evalTemplate, List.map_cons, encodeWords]
    exact congrArg (List.append (encodeWord (evalToken fields token))) ih

end MaxCutGames.Reduction.CanonicalBodyTemplate

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CloneMachineModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.CloneMachineModel

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

end MaxCutGames.Reduction.CloneMachineModel

/-!
# Affine word emission in the actual clone-table machine

The shared machine keeps its context fixed while copying one saved word. Its
finite transducer therefore acts by a fixed symbol substitution. The lemmas
below identify that substitution with the established unary encoding of
`offset + scale * value`, including all header and equation-field contexts.
Scale, offset, and the triple-table length remain symbolic.
-/

namespace MaxCutGames.Reduction.MachineAddressHeaders

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
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

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base (slots 1) [])
    (slots 2) (encodeWord n ++ base (slots 2))) (slots 3) (encodeWord m ++ base (slots 3))

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

def resultTapes (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base
    (control slots .baseValue) (encodeWord (radix s d n m)))
    (control slots .capacity) (encodeWord (capacity k s d n m)))
    (control slots .reversed) ((headerBits k s d noiseCount n m).reverse ++ base (control slots .reversed))

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

theorem prefixLocal_apply (k s d noiseCount : Nat) (index : Fin 5) :
    prefixLocal k s d noiseCount index = (match index.val with
      | 0 => .inl 0 | 1 => .inl 1
      | 2 => .inr (.inl .variableCount)
      | 3 => .inr (.inl .occurrenceCount)
      | _ => .inr (.inl .scratch)) := by
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

def resultTapes (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Arithmetic.resultTapes (arithmeticSlots slots)
    (Prefix.resultTapes (prefixSlots slots) base n m) n m

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

end MaxCutGames.Reduction.MachineAddressHeaders

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTemplateAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed canonical-word template followed by actual radix-address execution.
The program is determined by the fixed tokens and tape layout. Numeric field
values enter only the tape invariants and execution theorem, never the labels. -/

namespace MaxCutGames.Reduction.MachineTemplateAddress

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

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

end MaxCutGames.Reduction.MachineTemplateAddress

/-! Actual edge emission from two fixed address templates. Capacity is copied
before unary addition, so the original capacity tape is preserved. All local
labels and literal instructions depend only on fixed templates and layout. -/

namespace MaxCutGames.Reduction.MachineAddressEdge

open Turing
open MaxCutGames.Foundations.Complexity
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

end MaxCutGames.Reduction.MachineAddressEdge

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_EquationLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.SourceEquationLookup

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
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

end MaxCutGames.Reduction.SourceEquationLookup

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.MachineSourceTuple

open Turing MaxCutGames.Foundations.Complexity
open SourceEncoding
open MachineComposition

variable {width : Nat} {Extra σ : Type}

variable [DecidableEq Extra]

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

def nameField (j : Fin width) (s : Fin 3) : Tape width Extra := .field j (nameSlot s)

end MaxCutGames.Reduction.MachineSourceTuple

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CanonicalBodyMachine
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower a complete canonical-body template to the actual field-template
machine. There are four saved fields per query position, numbered by
`field + 4 * position`. The template constants depend only on finite coefficient
and RHS data; names and occurrence identifiers remain saved tape contents. -/

namespace MaxCutGames.Reduction.CanonicalBodyMachine

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding

variable {k : Nat}

def savedFields (fields : Fin k → Fin 4 → Nat) (index : Fin (4*k)) : List Bool :=
  encodeWord (fields ((fieldEquiv k).symm index).1 ((fieldEquiv k).symm index).2)

@[simp] theorem savedFields_fieldIndex (fields : Fin k → Fin 4 → Nat)
    (position : Fin k) (field : Fin 4) :
    savedFields fields (fieldIndex position field) = encodeWord (fields position field) := by
  simp [savedFields, fieldIndex]

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

end MaxCutGames.Reduction.CanonicalBodyMachine

namespace MaxCutGames.Reduction.AddressMachineSpace

open MaxCutGames.Foundations.Complexity

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
def edgeDecode_inline_AddressMachineSpace : Tape k s d noiseCount →
    Option (MachineAddressEdge.Tape (4 * k) (1 + 9 * k))
  | .savedIndex j => some (.inl (.field (CanonicalBodyMachine.fieldIndex j 3)))
  | .field j slot => if slot = 3 then none
      else some (.inl (.field (CanonicalBodyMachine.fieldIndex j slot)))
  | .extra (.inl (.inl .baseValue)) => some (.inl .radix)
  | .extra (.inl (.inl .capacity)) => some (.inr 0)
  | .extra (.inl (.inl .reversed)) => some (.inr 1)
  | .extra (.inr (.inl tape)) => some (.inl tape)
  | _ => none

theorem edgeDecode_canonicalField_inline_AddressMachineSpace (position : Fin k) (slot : Fin 4) :
    edgeDecode_inline_AddressMachineSpace k s d noiseCount (canonicalField k s d noiseCount position slot) =
      some (.inl (.field (CanonicalBodyMachine.fieldIndex position slot))) := by
  by_cases h : slot = 3 <;> simp [canonicalField, edgeDecode_inline_AddressMachineSpace, h]

theorem edgeDecode_edgeSlot_inline_AddressMachineSpace (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    edgeDecode_inline_AddressMachineSpace k s d noiseCount (edgeSlot k s d noiseCount tape) = some tape := by
  rcases tape with tape | i
  · cases tape <;> try rfl
    rename_i index
    rw [edgeSlot, edgeDecode_canonicalField_inline_AddressMachineSpace]
    exact congrArg (fun i => some (Sum.inl (MachineTemplateAddress.Tape.field i)))
      ((CanonicalBodyMachine.fieldEquiv k).apply_symm_apply index)
  · fin_cases i <;> rfl

def addressEdgeSlots : MachineAddressEdge.Tape (4 * k) (1 + 9 * k) ↪ Tape k s d noiseCount where
  toFun := edgeSlot k s d noiseCount
  inj' := by
    intro a b h
    have decoded := congrArg (edgeDecode_inline_AddressMachineSpace k s d noiseCount) h
    apply Option.some.inj
    simpa only [edgeDecode_edgeSlot_inline_AddressMachineSpace] using decoded

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

end MaxCutGames.Reduction.AddressMachineSpace

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressTupleLoaded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Integration.AddressTupleCleanup

open Turing MaxCutGames.Reduction MaxCutGames.Foundations.Complexity

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

variable {Λ : Type}

abbrev entry (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :=
  MachineDrainMany.entry (loadedFields k s d noiseCount) labels exit

/-- Fixed concrete drain instructions on the actual shared address state. -/
def instruction (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :
    Label k s d noiseCount → TM2.Stmt
      (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool) Λ (AddressMachineSpace.State k) :=
  MachineDrainMany.instruction (loadedFields k s d noiseCount) labels exit

end MaxCutGames.Integration.AddressTupleCleanup

/-!
# The exact frame after a tuple body and its field cleanup

Loading replaces the initially empty equation-field tapes. Appending writes
only the shared reversed-output header, which is outside those fields. The
actual field drains therefore restore the original arena with precisely the
same appended bytes. Saved occurrence indices and the odometer survive.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRhsLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Execute all fixed outcome rows after the existing RHS loader. A single
dispatcher freezes the loaded finite RHS vector into labels. Every row is an
actual address-edge phase; no row-run or whole-loop execution is assumed.
Program definitions contain only fixed templates, literal permutations, and
tape/label placement. Numeric names, radix, and capacity occur only in tapes
and the semantic correctness hypotheses. -/

namespace MaxCutGames.Reduction.MachineOutcomeRows

open Turing
open MaxCutGames.Foundations.Complexity

abbrev Row (k q width : Nat) := Rhs k → Spec q width

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

def sequenceInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) rows place exit

def selected (rows : List (Row k q width)) (rhs : Rhs k) : List (Spec q width) :=
  rows.map (fun row => row rhs)

@[simp] theorem selected_length (rows : List (Row k q width)) (rhs : Rhs k) :
    (selected rows rhs).length = rows.length := by simp [selected]

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

end MaxCutGames.Reduction.MachineOutcomeRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressGame
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Executable direct addresses for the actual canonical game. Every original
edge occurrence and its translation table is retained, in the same order.
Addresses not representing realized bodies are isolated vertices. No vertex
list, duplicate removal, or inverse enumeration is evaluated by the output. -/

namespace MaxCutGames.Reduction.AddressGame

open ActualSource
open Foundations.Target
open Integration.VertexEmbedding

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

end MaxCutGames.Reduction.AddressGame

namespace MaxCutGames.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration _root_.OAI.MaxCutGames.Reduction.Explicit

variable {N α β γ R : Type*}

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

end MaxCutGames.Reduction.FixedOutcomes

namespace MaxCutGames.Reduction.AddressByteSemantics

open Integration.BinaryLinear Foundations.Complexity ActualSource

def queryWords {k s d : Nat} (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) : List Nat :=
  CanonicalBodyTemplate.evalTemplate fields
    (CanonicalBodyTemplate.template (X (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple X) b)

def permutationWords {k s d : Nat} (X Y : ActualGame.Map k s d)
    (b : Fin k → F2) : List Nat :=
  tableWords (Encoding.translationTable
    (CanonicalBodyTemplate.alphabetOffset (X (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple X) b)
    (CanonicalBodyTemplate.alphabetOffset (Y (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple Y) b))

@[simp] theorem queryWords_length {k s d : Nat} (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) :
    (queryWords fields X b).length = 1 + 9*k := by
  simp only [queryWords, CanonicalBodyTemplate.evalTemplate, List.length_map,
    CanonicalBodyTemplate.template_length]

@[simp] theorem permutationWords_length {k s d : Nat} (X Y : ActualGame.Map k s d)
    (b : Fin k → F2) : (permutationWords X Y b).length = 2^s :=
  tableWords_length _

end MaxCutGames.Reduction.AddressByteSemantics

namespace MaxCutGames.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

variable {s d : Nat} {α : Type*}

abbrev Spec (k : Nat) := MachineOutcomeRows.Spec (4*k) (1+9*k)
abbrev Parameter (k : Nat) (T : NoiseTables.Table s d) :=
  FixedOutcomes.Parameter k s d (Fin T.vectors.length)

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

theorem interpreted_encoded (width : Nat) (words : List Nat) (hlen : words.length = width) :
    (interpreted width (encodeWords words)).val = words := by
  simp [interpreted, hlen]

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

def rhsBits (S : Source) {k : Nat} (U : ActualGame.Question S k) : Fin k → Bool :=
  fun j => (S.equation (U j)).rhs

@[simp] theorem bitVector_rhsBits (S : Source) {k : Nat} (U : ActualGame.Question S k) :
    bitVector (rhsBits S U) = fun j => ActualGame.rhs S (U j) := rfl

def tupleBits (S : Source) (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (U : ActualGame.Question S k) : List Bool :=
  (FixedOutcomes.tableParams k T).flatMap (fun p =>
    encodeWords (constraintWords (AddressGame.addressEdge S k (TableReduction.tableSkeleton T)
      (FixedOutcomes.assemble U p))))

end MaxCutGames.Reduction.AddressOutcomeSpecs

namespace MaxCutGames.Integration.AddressTupleBody

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

def source (F : SourceEncoding.Input) : ActualSource.Source :=
  ActualSource.Source.ofList F.equations F.nonempty

end MaxCutGames.Integration.AddressTupleBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressOdometerSchedule
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressOdometerSchedule

open Turing
open MaxCutGames.Foundations.Complexity MachineTupleOdometer
open MaxCutGames.Foundations.Hastad
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

theorem digitCases_inline_AddressOdometerSchedule {P : Tape k s d noiseCount → Prop} (tape : Tape k s d noiseCount)
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
  apply digitCases_inline_AddressOdometerSchedule tape
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

@[simp] theorem setDigits_savedIndex (m : Nat) (digits : Fin k → Nat)
    (base : Tape k s d noiseCount → List Bool) (j : Fin k) :
    setDigits m digits base (.savedIndex j) = encodeWord (digits j.rev) := by
  have h : j.rev.val < k := j.rev.isLt
  simp only [setDigits, h, dite_eq_left]

@[simp] theorem setAcc_other (base : Tape k s d noiseCount → List Bool)
    (bits : List Bool) (tape : Tape k s d noiseCount)
    (h : tape ≠ accumulator k s d noiseCount) : setAcc base bits tape = base tape := by
  simp [setAcc, h]

def configuration (label : Λ) (canonical : σ) (tapes : Tape k s d noiseCount → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ := ⟨some label, (canonical, none), tapes⟩

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) : Configuration (Tape k s d noiseCount) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc base ((allBits bits).reverse ++ base (accumulator k s d noiseCount))))

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
end MaxCutGames.Reduction.AddressOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineProgram
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration
open MachineComposition

noncomputable section

abbrev Tape (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :=
  AddressMachineSpace.Tape k s d T.vectors.length

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

def accumulator : Tape k T := AddressMachineSpace.headerTape k s d T.vectors.length .reversed
def output : Tape k T := AddressMachineSpace.finalOutput k s d T.vectors.length

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

end
end MaxCutGames.Reduction.AddressMachineProgram

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineInitial

open Turing MaxCutGames.Foundations.Complexity

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def afterHeaders (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineAddressHeaders.resultTapes (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
    (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F))
    F.«variables» F.equations.length

def initialized (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineOdometerInit.stageTapes (AddressMachineSpace.odometerSlots k s d T.vectors.length)
    F.equations.length (afterHeaders k T F) k

theorem input_header_inline_AddressMachineInitial (F : SourceEncoding.Input)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
      (AddressMachineSpace.headerTape k s d T.vectors.length c) = [] := by
  apply AddressMachineProgram.inputTapes_other
  simp [AddressMachineSpace.headerTape]

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
  exact (MachineAddressHeaders.resultTapes_source _ _ F.«variables» F.equations.length).trans
    (AddressMachineProgram.inputTapes_source k T _)

@[simp] theorem afterHeaders_variables (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) =
      encodeWord F.«variables» := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .variableCount) = _
  rw [MachineAddressHeaders.resultTapes_n]
  change encodeWord F.«variables» ++ AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
    (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) = _
  rw [input_header_inline_AddressMachineInitial, List.append_nil]

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
  rw [input_header_inline_AddressMachineInitial, List.append_nil]

@[simp] theorem afterHeaders_base (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.«variables» F.equations.length) :=
  MachineAddressHeaders.resultTapes_base _ _ _ _

@[simp] theorem afterHeaders_capacity (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.«variables» F.equations.length) :=
  MachineAddressHeaders.resultTapes_capacity _ _ _ _

@[simp] theorem afterHeaders_reversed (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.«variables» F.equations.length).reverse := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .reversed) = _
  rw [MachineAddressHeaders.resultTapes_reversed]
  change (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
    F.«variables» F.equations.length).reverse ++ AddressMachineProgram.inputTapes k T
      (SourceEncoding.inputBits F) (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) = _
  rw [input_header_inline_AddressMachineInitial, List.append_nil]

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
      encodeWord F.«variables» := by rw [initialized_header, afterHeaders_variables]
@[simp] theorem initialized_occurrences (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) =
      encodeWord F.equations.length := by rw [initialized_header, afterHeaders_occurrences]
@[simp] theorem initialized_base (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.«variables» F.equations.length) := by
  rw [initialized_header, afterHeaders_base]
@[simp] theorem initialized_capacity (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.«variables» F.equations.length) := by
  rw [initialized_header, afterHeaders_capacity]
@[simp] theorem initialized_reversed (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.«variables» F.equations.length).reverse := by
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

end
end MaxCutGames.Reduction.AddressMachineInitial

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSingleOrbitProgram
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

/-! Exact streaming traces in the single-orbit postprocessor. -/

/-! Physical unary header conversion, with an exact TM2 transition count. -/

/-! Actual subtraction of the right-side address offset, preserving the unary
capacity tape for every later edge. -/

/-! The exact input/output codec of the one-orbit postprocessor. Doubling is
only an encoding adapter: no equality of game values under independent labels
on the two copies is asserted. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitCodec

open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Complexity

def doubleConstraint {n q : Nat} (c : Constraint n q) : Constraint (2 * n) q where
  source := ⟨c.source.val, by have := c.source.isLt; omega⟩
  target := ⟨n + c.target.val, by have := c.target.isLt; omega⟩
  permutation := c.permutation

def rowBits {n q : Nat} (c : Constraint n q) : List Bool :=
  encodeWords (constraintWords c)

def doubledRowBits {n q : Nat} (c : Constraint n q) : List Bool :=
  encodeWords (constraintWords (doubleConstraint c))

@[simp] theorem rowBits_eq {n q : Nat} (c : Constraint n q) :
    rowBits c = encodeWord c.source.val ++ encodeWord c.target.val ++
      encodeWords (tableWords c.permutation) := by
  simp [rowBits, constraintWords, encodeWords, List.append_assoc]

@[simp] theorem doubledRowBits_eq {n q : Nat} (c : Constraint n q) :
    doubledRowBits c = encodeWord c.source.val ++ encodeWord (n + c.target.val) ++
      encodeWords (tableWords c.permutation) := by
  simp [doubledRowBits, constraintWords, doubleConstraint, encodeWords, List.append_assoc]

end MaxCutGames.Explicit.MachineSingleOrbitCodec

/-! Complete ordered row traversal of the physical one-orbit postprocessor. -/

/-! Actual tape cleanup, accumulator reversal, and halt for the one-orbit
postprocessor. The time bound is derived from an actual executed prefix. -/

/-!
Complete finite-machine postprocessing of the doubled address representation.
Every input field and row is physically processed. The time polynomial is in
the literal input bit length, including the final reversal and all tape cleanup.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineLoop

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

def finalTapes (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  (AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
    (AddressMachineInitial.initialized k T F) (bits k T F)).stk

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
        F.«variables» F.equations.length).reverse := by
  change (AddressOdometerSchedule.finalConfiguration _ _ _ _).stk (AddressOdometerSchedule.accumulator _ _ _ _) = _
  rw [AddressOdometerSchedule.final_accumulator]
  change (AddressOdometerSchedule.allBits (bits k T F)).reverse ++ _ = _
  rw [allBits_eq]
  congr 1
  exact AddressMachineInitial.initialized_reversed k T F

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

end
end MaxCutGames.Reduction.AddressMachineLoop

/-!
The actual address machine's final bridge, cleanup, reversal, and halt. The
polynomial cleanup bound follows from space used by the supplied actual prefix
execution. The complete reduction supplies that prefix in `MachineAddressGame`.
-/

/-!
# The complete addressed outer-reduction machine

The fixed finite machine reads an encoded nonempty E3LIN occurrence list and
writes the exact encoded addressed Unique Games instance. Its execution covers
all headers, all occurrence tuples, every fixed noise/coefficient outcome,
every permutation image, reversal, and complete tape cleanup.
-/

/-!
The old addressed producer is reused only as a code generator. Its exact output
is the doubled codec of the new single-orbit game. The proved physical
postprocessor then yields the new game, with no premise about the value of the
legacy game and no legacy gadget or inverse theorem used.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SurrogateFibers
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The surrogate perturbation fixes the complementary table exactly. Splitting
the actual uniform matrix law therefore expresses surrogate acceptance as the
mean of the uniform shortcode tests on the `(U,T)` fibers, including zero
perturbation factors. This supplies the sampling identification needed before
applying the inverse theorem to the many useful fibers.
-/

namespace MaxCutGames.Decoder.SurrogateFibers

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier
open scoped BigOperators

noncomputable section

variable {E K W C : Type*}
variable [AddCommGroup E] [Module F2 E]
variable [AddCommGroup K] [Module F2 K] [Fintype K]
variable [AddCommGroup W] [Module F2 W] [Fintype W]
variable [Fintype (E →ₗ[F2] F2)]
variable [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)]
variable [Fintype (E →ₗ[F2] K × W)]

/-- Uniform shortcode sampling; neither nonzero-factor conditioning nor
rank-one-matrix-uniform sampling is substituted for its two independent factors. -/
def shortcodeAcceptance (f : (E →ₗ[F2] K) → C) : ℝ := by
  classical
  exact 𝔼 M, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
    if f M = f (M + l.smulRight a) then (1 : ℝ) else 0

end
end MaxCutGames.Decoder.SurrogateFibers

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Reduction.ActualSource
open MaxCutGames.Fourier.MatrixNoise

namespace MaxCutGames.Decoder.ActualSpectral

open TableKeysGame NoiseSampler SurrogateFibers

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

def fiberAcceptance (S : Source) (k s d : Nat)
    (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (U : Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) : ℝ :=
  shortcodeAcceptance (fun M : ActualHomogeneous.E k →ₗ[F2] Alphabet s =>
    unfolded S k s d label (U, M.prod T))

end MaxCutGames.Decoder.ActualSpectral
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_MatrixCoordinates
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

local instance homFintype_r2c6deb_2 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def domainCoordinates (k : ℕ) :
    ActualHomogeneous.E k ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [ActualHomogeneous.finrank_E, Module.finrank_fin_fun])

def changeDomain {D E K : Type*} [AddCommGroup D] [Module F2 D]
    [AddCommGroup E] [Module F2 E] [AddCommGroup K] [Module F2 K]
    (e : D ≃ₗ[F2] E) : (D →ₗ[F2] K) ≃ₗ[F2] (E →ₗ[F2] K) where
  toFun M := M.comp e.symm.toLinearMap
  invFun M := M.comp e.toLinearMap
  left_inv M := by ext x; simp
  right_inv M := by ext x; simp
  map_add' M N := by ext x; rfl
  map_smul' c M := by ext x; rfl

def mapEquiv (k ell : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) ≃ₗ[F2]
      Inverse.Shortcode.Mat ell (1 + 2 * k) :=
  (changeDomain (domainCoordinates k)).trans LinearMap.toMatrix'

@[simp] theorem mapEquiv_apply (k ell : ℕ)
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k ell M = LinearMap.toMatrix' (M.comp (domainCoordinates k).symm.toLinearMap) :=
  rfl

@[simp] theorem mapEquiv_symm_apply (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) :
    (mapEquiv k ell).symm M = (Matrix.toLin' M).comp (domainCoordinates k).toLinearMap :=
  rfl

def functionalEquiv (k : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] F2) ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  (changeDomain (domainCoordinates k)).trans ((Pi.basisFun F2 (Fin (1 + 2 * k))).constr F2).symm

@[simp] theorem functionalEquiv_apply (k : ℕ)
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (j : Fin (1 + 2 * k)) :
    functionalEquiv k l j = l ((domainCoordinates k).symm (Pi.single j 1)) := by
  simp [functionalEquiv, changeDomain, Module.Basis.constr_symm_apply, Pi.basisFun_apply]

theorem mapEquiv_rankOne (k ell : ℕ) (l : ActualHomogeneous.E k →ₗ[F2] F2)
    (a : Fin ell → F2) :
    mapEquiv k ell (l.smulRight a) = Inverse.Shortcode.rankOne a (functionalEquiv k l) := by
  ext i j
  simp [Inverse.Shortcode.rankOne, mul_comm]

theorem mapEquiv_symm_add_rankOne (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k))
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (a : Fin ell → F2) :
    (mapEquiv k ell).symm (M + Inverse.Shortcode.rankOne a (functionalEquiv k l)) =
      (mapEquiv k ell).symm M + l.smulRight a := by
  apply (mapEquiv k ell).injective
  rw [LinearEquiv.apply_symm_apply, map_add, LinearEquiv.apply_symm_apply, mapEquiv_rankOne]

def coordinateTau (k : ℕ) : (Fin (1 + 2 * k) → F2) →ₗ[F2] F2 :=
  ActualHomogeneous.tau.comp (domainCoordinates k).symm.toLinearMap

theorem functionalEquiv_tau (k : ℕ) :
    functionalEquiv k ActualHomogeneous.tau =
      Inverse.Shortcode.functionalRow (coordinateTau k) := by
  ext j
  rw [functionalEquiv_apply]
  rfl

theorem mapEquiv_symm_firstBit_shift (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) (a : Fin ell → F2) :
    (mapEquiv k ell).symm
        (M + Inverse.Shortcode.rankOne a (Inverse.Shortcode.functionalRow (coordinateTau k))) =
      (mapEquiv k ell).symm M + ActualHomogeneous.tau.smulRight a := by
  rw [← functionalEquiv_tau]
  exact mapEquiv_symm_add_rankOne k ell M ActualHomogeneous.tau a

theorem mapEquiv_rowAdvice (k ell r : ℕ)
    (A : (Fin ell → F2) →ₗ[F2] (Fin r → F2))
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k r (A.comp M) =
      Inverse.RowErasureMatrix.rowAdvice (LinearMap.toMatrix' A) (mapEquiv k ell M) := by
  change LinearMap.toMatrix' (A.comp (M.comp (domainCoordinates k).symm.toLinearMap)) = _
  rw [LinearMap.toMatrix'_comp]
  rfl

end
end MaxCutGames.Decoder.MatrixCoordinates

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualGoodRows
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.ActualGoodRows

open Integration.BinaryLinear Reduction ActualSource
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

def table (S : Source) (k s d : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (U : ActualGame.Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (M : Mat s (1 + 2 * k)) : Vector s :=
  TableKeysGame.unfolded S k s d labeling
    (U, ((MatrixCoordinates.mapEquiv k s).symm M).prod T)

/-- The row-advice probability in actual matrix coordinates. In particular,
dependent rows of `A` are sampled with their full multiplicity. -/
def adviceMass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) : ℝ :=
  𝔼 U : ActualGame.Question S k,
    𝔼 T : ActualHomogeneous.E k →ₗ[F2] Vector d,
      RowErasure.adviceMass
        ((RowErasureMatrix.family s (1 + 2 * k) r).goodAt (table S k s d labeling U T) α)

end
end MaxCutGames.Decoder.ActualGoodRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualEvents
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two full-table events used in the projected-witness transfer. Their
sample space contains actual occurrence tuples and complete affine tables,
but no projection choice. The selected witness depends on row advice only.
-/

namespace MaxCutGames.Decoder.ActualEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat)
open scoped BigOperators Classical

noncomputable section

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

abbrev Context (S : Source) (k d : ℕ) :=
  ActualGame.Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)

abbrev Sample (S : Source) (k s d r : ℕ) :=
  Context S k d × (RowErasureDescriptions.RowMap s r × Mat s (1 + 2 * k))

abbrev FullTableSample (S : Source) (k s d r : ℕ) :=
  (ActualGame.Question S k × (Alphabet s →ₗ[F2] Vector r)) × ActualGame.Map k s d

/-- A bijection merely rearranges the full sampled table and changes its
matrix coordinates. It never appends the hidden projection to this law. -/
def fullTableEquiv (S : Source) (k s d r : ℕ) :
    FullTableSample S k s d r ≃ Sample S k s d r where
  toFun p := ((p.1.1, (LinearMap.snd F2 (Alphabet s) (Vector d)).comp p.2),
    (LinearMap.toMatrix' p.1.2,
      MatrixCoordinates.mapEquiv k s ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp p.2)))
  invFun q := ((q.1.1, Matrix.toLin' q.2.1),
    ((MatrixCoordinates.mapEquiv k s).symm q.2.2).prod q.1.2)
  left_inv p := by
    rcases p with ⟨⟨U, A⟩, P⟩
    apply Prod.ext
    · simp
    · apply LinearMap.ext
      intro x
      simp only [LinearEquiv.symm_apply_apply, LinearMap.prod_apply]
      rfl
  right_inv q := by
    rcases q with ⟨⟨U, T⟩, A, M⟩
    apply Prod.ext
    · apply Prod.ext rfl
      apply LinearMap.ext
      intro x
      rfl
    · apply Prod.ext
      · exact LinearMap.toMatrix'_toLin' A
      · change MatrixCoordinates.mapEquiv k s
          ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp
            (((MatrixCoordinates.mapEquiv k s).symm M).prod T)) = M
        have hf : (LinearMap.fst F2 (Alphabet s) (Vector d)).comp
            (((MatrixCoordinates.mapEquiv k s).symm M).prod T) =
              (MatrixCoordinates.mapEquiv k s).symm M := by
          apply LinearMap.ext
          intro x
          rfl
        rw [hf, LinearEquiv.apply_symm_apply]

def unrestricted (S : Source) (k s d r : ℕ) : FiniteDistribution (Sample S k s d r) :=
  FiniteDistribution.uniform _

def sliceEvent (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r) : Bool :=
  decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
    (ActualGoodRows.table S k s d labeling p.1.1 p.1.2) α p.2.1 p.2.2)

def targetHit (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r) : Bool :=
  decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
    (ActualGoodRows.table S k s d labeling p.1.1 p.1.2) α p.2.1 p.2.2)

end
end MaxCutGames.Decoder.ActualEvents

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SelectedPolicies
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual visible selector used by the stochastic decoder

At fixed labeling, the matrix table depends only on the occurrence question and
complement map. Its normalized row/column witness is selected from the observed
row map and row value. Transporting this witness through the actual homogeneous
coordinates supplies `VisiblePolicies.ResponseWitness`; the selected target's
affine intercept is retained separately, including exact equality on the slice.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedPolicies

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction
open MaxCutGames.Inverse
open ActualSource VisiblePolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

/-- The table at a fixed actual occurrence question and complement map. -/
def matrixTable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (occ : ActualGame.Question S k)
    (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (M : Shortcode.Mat s (1 + 2 * k)) : Alphabet s :=
  TableKeysGame.unfolded S k s d labeling
    (occ, ((mapEquiv k s).symm M).prod T)

/-- No hidden matrix is an input to this fixed table function. -/
def fullTable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (q : LeftInput S k s d (Vector r)) : Shortcode.Mat s (1 + 2 * k) → Alphabet s :=
  matrixTable S labeling q.occurrences q.complement

theorem matrixTable_fold (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (occ : ActualGame.Question S k)
    (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (h : Alphabet s) (M : Shortcode.Mat s (1 + 2 * k)) :
    matrixTable S labeling occ T
        (M + Shortcode.rankOne h (Shortcode.functionalRow (coordinateTau k))) =
      matrixTable S labeling occ T M + h := by
  unfold matrixTable
  rw [mapEquiv_symm_firstBit_shift]
  have hprod : (((mapEquiv k s).symm M + ActualHomogeneous.tau.smulRight h).prod T) =
      ((mapEquiv k s).symm M).prod T +
        ActualHomogeneous.tau.smulRight (h, (0 : Vector d)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · simp
  rw [hprod]
  exact TableKeysGame.unfolded_equivariant S k s d labeling
    (occ, ((mapEquiv k s).symm M).prod T) h

def GoodAdvice (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (q : LeftInput S k s d (Vector r)) : Prop :=
  (RowErasureMatrix.family s (1 + 2 * k) r).GoodAdvice (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows)

/-- The actual normalized description, chosen using only the left observation. -/
def normalizedDescription (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    RowErasureDescriptions.Description s (1 + 2 * k) r :=
  RowErasureMatrix.normalizedChosenDescription (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood (coordinateTau k)
    (matrixTable_fold S labeling q.occurrences q.complement) hα hsmall

theorem normalizedDescription_spec (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    let F := RowErasureMatrix.family s (1 + 2 * k) r
    let D := normalizedDescription S labeling α hα hsmall q hgood
    let D₀ := F.chosenDescription (fullTable S labeling q) α
      (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood
    F.rowMap D = LinearMap.toMatrix' q.rowMap ∧
      F.rowValue D = mapEquiv k r q.rows ∧
      (F.points D).Nonempty ∧
      α / 2 ≤ F.agreement (fullTable S labeling q) D ∧
      coordinateTau k D.coefficient = 1 ∧
      D.toSlice = D₀.toSlice ∧
      F.agreement (fullTable S labeling q) D = F.agreement (fullTable S labeling q) D₀ ∧
      ∀ M, M ∈ F.points D₀ → F.target D M = F.target D₀ M :=
  RowErasureMatrix.normalizedChosenDescription_spec (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood (coordinateTau k)
    (matrixTable_fold S labeling q.occurrences q.complement) hα hsmall

/-- The response coefficient and columns in the actual homogeneous space. -/
def normalizedResponse (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    ResponseWitness k where
  columns := (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan.map
    (domainCoordinates k).symm.toLinearMap
  coefficient := (domainCoordinates k).symm
    (normalizedDescription S labeling α hα hsmall q hgood).coefficient
  firstBit := (normalizedDescription_spec S labeling α hα hsmall q hgood).2.2.2.2.1

end MaxCutGames.Decoder.SelectedPolicies
end

/-! The selected full-table events pulled back to the genuine projected
experiment. The comparison space forgets the projection, while complete data
retains it only for the subsequent finite conditional-law argument. -/

namespace MaxCutGames.Decoder.ActualSeedEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype_r2c6deb_3 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
abbrev Seed (S : Source) (k s d r : ℕ) :=
  AdviceLaw.FullSeed k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)

abbrev Datum (S : Source) (k s d r : ℕ) :=
  AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)

def law (S : Source) (k s d r : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (Seed S k s d r) :=
  AdviceLaw.fullSeedLaw (V := Ambient s d)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ'

def draw {S : Source} {k s d r : ℕ} (x : Seed S k s d r) :=
  AdviceLaw.seedToActualDraw x.1.1 x.1.2 x.2

def pad (S : Source) (k s d r : ℕ) (x : Seed S k s d r) : ActualEvents.Sample S k s d r :=
  ActualEvents.fullTableEquiv S k s d r
    (AdviceLaw.fullSeedPad (fun i => toBit (ActualGame.rhs S i)) x)

def slice (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    Seed S k s d r → Bool :=
  fun x => ActualEvents.sliceEvent S k s d r labeling α (pad S k s d r x)

def targetHit (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    Seed S k s d r → Bool :=
  fun x => ActualEvents.targetHit S k s d r labeling α (pad S k s d r x)

theorem slice_eq_selectedEvent (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) :
    slice S k s d r labeling α x = decide
      ((Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
        (SelectedPolicies.fullTable S labeling
          (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
        (LinearMap.toMatrix' (draw x).rowMap)
        (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))) :=
  rfl

end
end MaxCutGames.Decoder.ActualSeedEvents

/-! Whole-table variation for the exact projected seed law in the selected
event coordinates. The projection is averaged out before the comparison. -/

namespace MaxCutGames.Decoder.ActualSeedVariation

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end
end MaxCutGames.Decoder.ActualSeedVariation

/-!
# Conditional success of the actual selected policies

This endpoint uses the normalized witness chosen from the left observation and
the private Fourier kernel chosen from the right observation. The hypothesis is
literal uniform agreement on a transferred affine column slice. Deriving that
hypothesis from the actual visible conditional law is the separate transfer
step; it is not assumed as an inverse theorem or as extra prover information.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedDecoding

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_r2c6deb_4 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
/-- Normalizing the target preserves the actual selected event, point by point. -/
theorem selectedEvent_iff_normalized (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k))
    (hrow : RowErasureMatrix.rowAdvice (LinearMap.toMatrix' q.rowMap) M =
      mapEquiv k r q.rows) :
    (RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
        (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap) M ↔
      M ∈ (RowErasureMatrix.family s (1 + 2 * k) r).points
        (normalizedDescription S labeling α hα hsmall q hgood) := by
  have he := (RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent_iff_of_advice
    (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap)
    (mapEquiv k r q.rows) hgood M hrow
  obtain ⟨_, _, _, _, _, hslice, _, _⟩ :=
    normalizedDescription_spec S labeling α hα hsmall q hgood
  rw [show (RowErasureMatrix.family s (1 + 2 * k) r).points
      (normalizedDescription S labeling α hα hsmall q hgood) =
      (RowErasureMatrix.family s (1 + 2 * k) r).points
        ((RowErasureMatrix.family s (1 + 2 * k) r).chosenDescription
          (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap)
          (mapEquiv k r q.rows) hgood) from congrArg Shortcode.Slice.points hslice]
  exact he

end MaxCutGames.Decoder.SelectedDecoding
end

/-!
# The selected padded slice is the actual projected affine slice

After fixing row advice, the selected full-domain column equations on `Mπ` are
exactly the equations fixing `M` on the image of the selected column span under
`π`. The equivalence keeps the same maps, so both uniform sampling and affine
target equality transport without changing the chosen intercept.
-/

noncomputable section

namespace MaxCutGames.Decoder.ProjectedColumnSlice

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

section Algebra

variable {V : Type*} [AddCommGroup V] [Module F2 V]

/-- Two successive images of a column subspace express the same pointwise
agreement as composition with the coordinate change and projection. -/
theorem column_agreement_iff (Q : Submodule F2 (Vector (1 + 2 * k)))
    (π : ActualHomogeneous.E k →ₗ[F2] V) (M Mstar : V →ₗ[F2] Alphabet s) :
    (∀ x ∈ Q, M (π ((domainCoordinates k).symm x)) =
      Mstar (π ((domainCoordinates k).symm x))) ↔
      ∀ v ∈ (Q.map (domainCoordinates k).symm.toLinearMap).map π, M v = Mstar v := by
  constructor
  · intro h v hv
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
    exact h x hx
  · intro h x hx
    apply h
    exact Submodule.mem_map.mpr ⟨(domainCoordinates k).symm x,
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- A simultaneous matrix slice pulls back to the projected column equations
once the actual row equation is fixed. -/
theorem contains_padded_iff
    (D : RowErasureDescriptions.Description s (1 + 2 * k) r)
    (A : Alphabet s →ₗ[F2] Vector r)
    (hDrow : (RowErasureMatrix.family s (1 + 2 * k) r).rowMap D = LinearMap.toMatrix' A)
    (π : ActualHomogeneous.E k →ₗ[F2] V) (Mstar : V →ₗ[F2] Alphabet s)
    (hstar : mapEquiv k s (Mstar.comp π) ∈ D.toSlice.points)
    (M : V →ₗ[F2] Alphabet s) (hrow : A.comp M = A.comp Mstar) :
    mapEquiv k s (M.comp π) ∈ D.toSlice.points ↔
      ∀ v ∈ (D.toSlice.columnSpan.map (domainCoordinates k).symm.toLinearMap).map π,
        M v = Mstar v := by
  have hr : D.toSlice.rowMap = A := by
    change Matrix.toLin' D.1 = A
    change D.1 = LinearMap.toMatrix' A at hDrow
    rw [hDrow, Matrix.toLin'_toMatrix']
  have hc (N : V →ₗ[F2] Alphabet s) :
      Matrix.toLin' (mapEquiv k s (N.comp π)) =
        (N.comp π).comp (domainCoordinates k).symm.toLinearMap := by
    rw [mapEquiv_apply, Matrix.toLin'_toMatrix']
  have hs : D.toSlice.Contains (mapEquiv k s (Mstar.comp π)) :=
    (Finset.mem_filter.mp hstar).2
  have he := D.toSlice.contains_iff_inSlice (mapEquiv k s (Mstar.comp π)) hs
    (mapEquiv k s (M.comp π))
  rw [AffineWitness.InSlice, hr, hc, hc] at he
  have hrows : A.comp ((M.comp π).comp (domainCoordinates k).symm.toLinearMap) =
      A.comp ((Mstar.comp π).comp (domainCoordinates k).symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hrow (π ((domainCoordinates k).symm x))
  constructor
  · intro h
    have hh := he.mp (Finset.mem_filter.mp h).2
    exact (column_agreement_iff D.toSlice.columnSpan π M Mstar).mp hh.2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, he.mpr ⟨hrows,
      (column_agreement_iff D.toSlice.columnSpan π M Mstar).mpr h⟩⟩

end Algebra

end MaxCutGames.Decoder.ProjectedColumnSlice
end

/-! A finite experiment whose sample weights are constant on the selected
event becomes exactly uniform after conditioning on that event. The event is
allowed to have arbitrary positive mass, so this applies after the complete
visible datum and the chosen column constraints have both been fixed. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_VisibleTransfer
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete-data conditional law of the actual projected experiment.
The residual private matrix is uniform even when the occurrence law is
weighted and the public row map has deficient rank. -/

namespace MaxCutGames.Decoder.ActualConditionalLaw

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

variable {k s d r : ℕ}

def datumAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) : ℝ :=
  VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data 0)

end
end MaxCutGames.Decoder.ActualConditionalLaw

/-!
# Actual conditional selected-fiber agreement

The selected event is the full-table event used by the total-variation
comparison. On a positive complete-data fiber it becomes the uniform actual
affine row/column slice. The selector is fixed by the left observation; the
extra complete data and a supporting matrix occur only in this analysis.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedFiberLaw

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Inverse MaxCutGames.Foundations.Games
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates ActualSeedEvents
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_r2c6deb_5 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def datumLeft (S : Source) (data : Datum S k s d r) : LeftInput S k s d (Vector r) :=
  AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

def datumMatrix (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :=
  (AdviceLaw.completeDraw data N).hiddenMatrix

def datumProjection (S : Source) (data : Datum S k s d r) :=
  AdviceExperiment.projection (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

theorem datumLeft_eq (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data N) =
      datumLeft S data := by
  unfold datumLeft
  rw [AdviceLaw.completeDraw_left, AdviceLaw.completeDraw_left]

theorem datumMatrix_rows (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    data.1.2.comp (datumMatrix S data N) = data.2.2.2.val :=
  AdviceLaw.completeDraw_rows data N

theorem datumMatrix_rowAdvice (S : Source) (data : Datum S k s d r)
    (N : AdviceLaw.PrivateMap data) :
    RowErasureMatrix.rowAdvice (LinearMap.toMatrix' data.1.2)
        (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data))) =
      mapEquiv k r (datumLeft S data).rows := by
  rw [← mapEquiv_rowAdvice]
  change mapEquiv k r ((data.1.2.comp (datumMatrix S data N)).comp (datumProjection S data)) =
    mapEquiv k r ((data.1.2.comp (datumMatrix S data 0)).comp (datumProjection S data))
  rw [datumMatrix_rows, datumMatrix_rows] ; rfl

/-- Every event membership uses the same selected normalized witness on the
entire complete-data fiber. -/
theorem slice_assemble_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (N : AdviceLaw.PrivateMap data) :
    slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true ↔
      mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)) ∈
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).toSlice.points := by
  rw [slice_eq_selectedEvent]
  change decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
      (fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S)
        (AdviceLaw.completeDraw data N))) α (LinearMap.toMatrix' data.1.2)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)))) = true ↔ _
  rw [datumLeft_eq, decide_eq_true_eq]
  exact SelectedDecoding.selectedEvent_iff_normalized S labeling α hα hsmall
    (datumLeft S data) hgood _ (datumMatrix_rowAdvice S data N)

/-- The actual selected private coordinates are in bijection with the complete
projected affine slice. The supporting point is used only to state its column
equations; the canonical visible base still defines the private coordinates. -/
def selectedPrivateEquiv (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true) :
    {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true} ≃
      RowErasureSliceQuotient.AffineSlice data.1.2
        ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
          (datumProjection S data)) (datumMatrix S data Nstar) := by
  let D := normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood
  let e := AdviceFibers.rowFiberEquiv data.1.2 data.2.2.2.val
    (AdviceFibers.observedBase data.1.2 data.2.2.2)
    (AdviceFibers.observedBase_property data.1.2 data.2.2.2)
  have hs : mapEquiv k s ((datumMatrix S data Nstar).comp (datumProjection S data)) ∈ D.toSlice.points :=
    (slice_assemble_iff S labeling α hα hsmall data hgood Nstar).mp hstar
  have hrow (N : AdviceLaw.PrivateMap data) :
      data.1.2.comp (datumMatrix S data N) = data.1.2.comp (datumMatrix S data Nstar) := by
    rw [datumMatrix_rows, datumMatrix_rows]
  let lift := fun M : RowErasureSliceQuotient.AffineSlice data.1.2
      ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
        (datumProjection S data)) (datumMatrix S data Nstar) =>
    e.symm ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩
  have hlift (M) : datumMatrix S data (lift M) = M.val :=
    congrArg Subtype.val (e.apply_symm_apply ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩)
  refine {
    toFun := fun N => ⟨datumMatrix S data N.val, hrow N.val, ?_⟩
    invFun := fun M => ⟨lift M, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs
      (datumMatrix S data N.val) (hrow N.val)).mp
        ((slice_assemble_iff S labeling α hα hsmall data hgood N.val).mp N.property)
  · apply (slice_assemble_iff S labeling α hα hsmall data hgood (lift M)).mpr
    rw [hlift]
    exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs M.val M.property.1).mpr M.property.2
  · intro N
    apply Subtype.ext
    exact e.symm_apply_apply N.val
  · intro M
    apply Subtype.ext
    exact hlift M

@[simp] theorem selectedPrivateEquiv_val (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true)
    (N : {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true}) :
    (selectedPrivateEquiv S labeling α hα hsmall data hgood Nstar hstar N).val =
      datumMatrix S data N.val := rfl

end MaxCutGames.Decoder.SelectedFiberLaw
end

/-! The full selected-witness argument on the actual projected experiment.
The variation comparison precedes all conditioning. Its visible event then
pays the independent private decoder success on every selected datum. -/

namespace MaxCutGames.Decoder.ActualProjectedTransfer

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_r2c6deb_6 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def slopeVariation (k s d : ℕ) (β : ℝ) : ℝ :=
  Foundations.Information.totalVariation
    (SparseLaw.independentWeights
      (SparseLaw.mixture β (SparseLaw.singletonPairWeights (Ambient s d))) k)
    (SparseLaw.uniformWeights (Fin k → Ambient s d × Ambient s d))

end
end MaxCutGames.Decoder.ActualProjectedTransfer

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualAdviceSampling
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The stochastic clean upper bound applies to the literal agreement of the two
actual local decoders.  The equality below retains every sampled mask, all
occurrence/position draws, and both independently uniform target maps.
-/

namespace MaxCutGames.Decoder.ActualAdviceSampling

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
open ActualSource ActualAdviceUpper

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

/-- The actual experiment, before identifying its visible-map marginal with
the clean-coordinate law. The two private answer draws are already averaged
inside `observedAgreement`. -/
def sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
        (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
      fun TM => (FiniteDistribution.table (fun _ : Fin k => μ)).expectation fun draw =>
        VisiblePolicies.observedAgreement S labeling good
          (actualDraw S A (Clean.NativeExperiment.maskSet mask) (fun j => (draw j).1)
            (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) TM.1 TM.2)

end

end MaxCutGames.Decoder.ActualAdviceSampling

/-!
Pointwise and uniform-law identification of the retained projection seed with
the actual decoder draw. Auxiliary slots at full positions affect neither the
projection nor the displayed target question. The entire target map is retained
when it is repacked into its independent hidden and complement components.
-/

/-!
The complete seed used for the lower-bound conditioning argument and the
mask/slot/map experiment used for the clean upper bound have exactly the same
actual decoder success. Unused positions are removed only by the pointwise
observation equality; occurrence IDs and their ordered local copies remain.
-/

namespace MaxCutGames.Decoder.ActualSeedSampling

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
open ActualSource ActualAdviceUpper ActualAdviceSampling

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

/-- A named pointwise observable makes the finite expectation permutations
explicit without changing the actual sampled draw. -/
def drawAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) (mask : Fin k → Bool)
    (occ : Fin k → Fin S.occurrences) (slots : Fin k → Fin 3)
    (TM :
      (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
      (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s)) : ℝ :=
  VisiblePolicies.observedAgreement S labeling good
    (actualDraw S A (Clean.NativeExperiment.maskSet mask) occ
      (fun j => Clean.ActualAdviceBridge.indexSlot (slots j)) TM.1 TM.2)

end

end MaxCutGames.Decoder.ActualSeedSampling

/-! The contradiction uses the same actual seed and local decoder on both
sides. Its lower bound comes from full-table variation followed by visible
conditioning; its upper bound comes from the exact incidence sampler. -/

end OAI
end


