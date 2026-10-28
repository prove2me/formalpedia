-- Prove2me | Definitions.Def_OAIQ085D001
-- name    : OAIQ085D001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:52:38.289727+00:00
-- url     : https://prove2.me/theorems/f87954d7-435e-4331-b5c2-f71e77446a48
-- title:
--   Definitions bundle OAIQ085D001 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1098 declarations of OpenAI's Lean: 684 definitions, 64 inductive types or structures, 26 instances and 324 theorems. The definitions and types are `OAI.DFVSGames.Appendix.A4IndexCount.Index`, `OAI.DFVSGames.Appendix.A4IndexCount.Valid`, `OAI.DFVSGames.Appendix.A4IndexCount.aToRange`, `OAI.DFVSGames.Appendix.A4IndexCount.encode`, `OAI.DFVSGames.Appendix.A4IndexCount.encodeFixed`, `OAI.DFVSGames.Appendix.A4IndexCount.factorViaRange`, `OAI.DFVSGames.Appendix.A4IndexCount.quotientRestriction`, `OAI.DFVSGames.Appendix.A5Scalar.positiveSum`, `OAI.DFVSGames.Appendix.A5WeightedReindex.fiber`, `OAI.DFVSGames.Appendix.BadConvolution.mobius`, `OAI.DFVSGames.Appendix.BinaryA4.F2`, `OAI.DFVSGames.Appendix.CoordinateTransport.codomainEquiv`, `OAI.DFVSGames.Appendix.CoordinateTransport.complementRangeEquiv`, `OAI.DFVSGames.Appendix.CoordinateTransport.domainEquiv`, `OAI.DFVSGames.Appendix.CoordinateTransport.rangeTransport`, `OAI.DFVSGames.Appendix.CoordinateTransport.toBlocks`, `OAI.DFVSGames.Appendix.DegreeCover.F2`, `OAI.DFVSGames.Appendix.DyadicError.dyadicError`, `OAI.DFVSGames.Appendix.DyadicError.quarterError`, `OAI.DFVSGames.Appendix.DyadicError.quarterSum`, `OAI.DFVSGames.Appendix.Level.LinearRank.compress`, `OAI.DFVSGames.Appendix.LinearIdentities.A4Index`, `OAI.DFVSGames.Appendix.LinearIdentities.A4Survives`, `OAI.DFVSGames.Appendix.LinearIdentities.A5PairSurvives`, `OAI.DFVSGames.Appendix.LinearIdentities.Hybrid`, `OAI.DFVSGames.Appendix.LinearIdentities.compress`, `OAI.DFVSGames.Appendix.RankAdditivity.RankBelow`, `OAI.DFVSGames.Appendix.RestrictionTransport.sameRangeEquiv`, `OAI.DFVSGames.Appendix.SubmoduleInterval.lowerIntervalEquiv`, `OAI.DFVSGames.Appendix.SubmoduleInterval.lowerIntervalSpaceEquiv`, `OAI.DFVSGames.Appendix.SubmoduleInterval.lowerWeightedTotal`, `OAI.DFVSGames.Appendix.SubspaceCounting.generators`, `OAI.DFVSGames.Appendix.SubspaceCounting.quotientImageMap`, `OAI.DFVSGames.Appendix.SubspaceExtensions.extension`, `OAI.DFVSGames.Appendix.SubspaceExtensions.hKernel`, `OAI.DFVSGames.Appendix.SubspaceExtensions.horizontal`, `OAI.DFVSGames.Appendix.SubspaceExtensions.mobiusTotal`, `OAI.DFVSGames.Appendix.SubspaceExtensions.mobiusWeight`, `OAI.DFVSGames.Appendix.SubspaceExtensions.quotientFintype`, `OAI.DFVSGames.Appendix.SubspaceExtensions.scalarMap` and 708 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Analysis_MatrixCharacters`, `DirectedFeedback_CookLevin_PolynomialMachine`, `DirectedFeedback_Encoding_ActualGoodRows`, `DirectedFeedback_Encoding_Bounds`, `DirectedFeedback_Encoding_CanonicalWordTemplate`, `DirectedFeedback_Encoding_CompareLoop`, `DirectedFeedback_Encoding_EmitRows`, `DirectedFeedback_Encoding_ExpanderTableWords`, `DirectedFeedback_Encoding_FinalCNFPattern`, `DirectedFeedback_Encoding_FormulaEncoding`, `DirectedFeedback_Encoding_Lookup`, `DirectedFeedback_Encoding_PortTables`, `DirectedFeedback_Encoding_PoweringAddresses`, `DirectedFeedback_Encoding_PoweringTables`, `DirectedFeedback_Encoding_PreprocessingOverlayTables`, `DirectedFeedback_Encoding_PreprocessingRegularTables`, `DirectedFeedback_Encoding_PreprocessingStageMaps`, `DirectedFeedback_Encoding_Queries`, `DirectedFeedback_Encoding_Setup`, `DirectedFeedback_Encoding_VerifierCNF`, `DirectedFeedback_Games_A4IndexCount`, `DirectedFeedback_Games_A5ForwardIndex`, `DirectedFeedback_Games_A5Scalar`, `DirectedFeedback_Games_ActualAdviceUpper`, `DirectedFeedback_Games_ActualCanonical`, `DirectedFeedback_Games_AddressTupleBody`, `DirectedFeedback_Games_AddressTupleLoaded`, `DirectedFeedback_Games_AffineWitnessNormalization`, `DirectedFeedback_Games_AlphabetReduction`, `DirectedFeedback_Games_CanonicalAddress`, `DirectedFeedback_Games_CayleySampling`, `DirectedFeedback_Games_CayleySpectral`, `DirectedFeedback_Games_ConditionalIncidences`, `DirectedFeedback_Games_CoordinateTransport`, `DirectedFeedback_Games_DegreeCover`, `DirectedFeedback_Games_Derivatives`, `DirectedFeedback_Games_ExpanderFamily`, `DirectedFeedback_Games_Explicit`, `DirectedFeedback_Games_FieldArray`, `DirectedFeedback_Games_FinishReduction`, `DirectedFeedback_Games_Generator`, `DirectedFeedback_Games_GeneratorModel`, `DirectedFeedback_Games_InitialGraph`, `DirectedFeedback_Games_KernelCardinality`, `DirectedFeedback_Games_PartnerFullSampling`, `DirectedFeedback_Games_PositiveMultiplier`, `DirectedFeedback_Games_PoweringReach`, `DirectedFeedback_Games_Preprocessing`, `DirectedFeedback_Games_Product`, `DirectedFeedback_Games_ProductLaw`, `DirectedFeedback_Games_ProfileCorrection`, `DirectedFeedback_Games_RowErasureSliceUniform`, `DirectedFeedback_Games_RowErasureSlices`, `DirectedFeedback_Games_SignaturePrepare`, `DirectedFeedback_Games_StageData`, `DirectedFeedback_Games_SubmoduleInterval`, `DirectedFeedback_Games_Target`, `DirectedFeedback_Games_UniformReduction`, `DirectedFeedback_Games_UpperMobius`, `DirectedFeedback_Games_VisibleTransfer`, `DirectedFeedback_Machines_AddressMachineInitial`, `DirectedFeedback_Machines_ContextClear`, `DirectedFeedback_Machines_ContextLoad`, `DirectedFeedback_Machines_GraphCounterFinish`, `DirectedFeedback_Machines_LoopInit`, `DirectedFeedback_Machines_MachineAddressHeaders`, `DirectedFeedback_Machines_MachineAffineLookup`, `DirectedFeedback_Machines_MachineBinaryLiteralMachine`, `DirectedFeedback_Machines_MachineBinaryNameMachine`, `DirectedFeedback_Machines_MachineBinaryRenameMachine`, `DirectedFeedback_Machines_MachineBinaryTokenMachine`, `DirectedFeedback_Machines_MachineBinaryTotalInputMachine`, `DirectedFeedback_Machines_MachineCloudCount`, `DirectedFeedback_Machines_MachineCloudPadding`, `DirectedFeedback_Machines_MachineEmbedding`, `DirectedFeedback_Machines_MachineExpanderFamilyLoop`, `DirectedFeedback_Machines_MachineExpanderRow`, `DirectedFeedback_Machines_MachineExpanderRowDivision`, `DirectedFeedback_Machines_MachineLookupSpec`, `DirectedFeedback_Machines_MachineOutcomeRows`, `DirectedFeedback_Machines_MachinePaddedExpanderFamily`, `DirectedFeedback_Machines_MachinePreservingLookupClean`, `DirectedFeedback_Machines_MachineProductPower`, `DirectedFeedback_Machines_MachineRegularOriginalBody`, `DirectedFeedback_Machines_MachineSingleOrbitBridge`, `DirectedFeedback_Machines_MachineSingleOrbitCodec`, `DirectedFeedback_Machines_MachineStateEquiv`, `DirectedFeedback_Machines_MachineSubdivisionRows`, `DirectedFeedback_Machines_MachineSubstitution`, `DirectedFeedback_Machines_MachineTemplateAddress`, `DirectedFeedback_Machines_MachineTransducer`, `DirectedFeedback_Machines_MachineTuple`, `DirectedFeedback_Machines_MachineUnaryAdd`, `DirectedFeedback_Machines_PoweringMachineLoop`, `DirectedFeedback_Machines_PoweringMachineOuterLoop`, `DirectedFeedback_Machines_PoweringMachineRelationField`, `DirectedFeedback_Machines_PoweringMachineRowBody`, `DirectedFeedback_Machines_PoweringMachineWord`, `DirectedFeedback_Machines_RawInitialMachineFinish`, `DirectedFeedback_Machines_RuntimeFinish`, `DirectedFeedback_Machines_RuntimeSpace`, `DirectedFeedback_Machines_TupleOrder`, `DirectedFeedback_Probability_Mixture`, `DirectedFeedback_Probability_PoweringFieldPlan`, `DirectedFeedback_Probability_RepeatedGameBounds`, `DirectedFeedback_Probability_TraceLaw`, `DirectedFeedback_RankGraph_Clone100Counting`, `DirectedFeedback_RankGraph_CloneGap`, `DirectedFeedback_RankGraph_MachineClone100Finish`, `DirectedFeedback_RankGraph_SumBox`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D006`, `OAIQ085D007`, `OAIQ085D008`, `OAIQ085D009` and `OAIQ085D010`; the statement `OAI_DFVSGames_Inverse_KMSExpansion_kms_expansion`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ085_DF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineComposition

theorem natPolynomial_eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h degree)

noncomputable def compositionPolynomial (first second intermediate : Polynomial Nat) : Polynomial Nat :=
  first + Polynomial.C 2 * (intermediate + 1) + second.comp intermediate

theorem compositionBudget_le (first second intermediate : Polynomial Nat)
    (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength) :
    first.eval inputLength + 2 * (intermediateLength + 1) + second.eval intermediateLength ≤
      (compositionPolynomial first second intermediate).eval inputLength := by
  have secondBound := natPolynomial_eval_mono second intermediateBound
  have transferBound := Nat.mul_le_mul_left 2 (Nat.add_le_add_right intermediateBound 1)
  simp only [compositionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_comp]
  omega

end DFVSGames.Foundations.Complexity.MachineComposition


namespace DFVSGames.Reduction.MachineTransfer

open Turing

variable {α β : Type} [Fintype α] [Fintype β]


variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def nextAt (dst : K) (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (configuration : Option (TM2.Cfg Γ Λ (σ × Option (Γ dst)))) :
    Option (TM2.Cfg Γ Λ (σ × Option (Γ dst))) :=
  configuration.bind (TM2.step program)


end DFVSGames.Reduction.MachineTransfer


namespace DFVSGames.Foundations.Complexity.MachineCopy

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

def forkTapes (source left right : K) (base : K → List β)
    (input leftOutput rightOutput : List β) : K → List β :=
  Function.update (Function.update (Function.update base source input) left leftOutput)
    right rightOutput

end DFVSGames.Foundations.Complexity.MachineCopy

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceMachine

open Turing
open DFVSGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def fieldStart (destination : K) (loopLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .push destination (fun _ => false) (.goto fun _ => loopLabel)

def fieldTapes (source destination : K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem fieldTapes_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output source = input := by
  simp [fieldTapes, hne]

@[simp] theorem fieldTapes_destination (source destination : K)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output destination = output := by
  simp [fieldTapes]

@[simp] theorem fieldTapes_self (source destination : K) (base : K → List Bool) :
    fieldTapes source destination base (base source) (base destination) = base := by
  simp [fieldTapes]

end DFVSGames.Foundations.Hastad.SourceMachine


namespace DFVSGames.Foundations.Complexity.MachineDrain

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end DFVSGames.Foundations.Complexity.MachineDrain


namespace DFVSGames.Foundations.Complexity.MachineFiniteSequence

open Turing MachineComposition

variable {Command : Type} (LocalLabel : Command → Type)

def Label : List Command → Type
  | [] => Empty
  | command :: commands => LocalLabel command ⊕ Label commands

instance labelFintype [∀ command, Fintype (LocalLabel command)]
    (commands : List Command) : Fintype (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (Fintype (LocalLabel command ⊕ Label LocalLabel commands))

instance labelDecidableEq [∀ command, DecidableEq (LocalLabel command)]
    (commands : List Command) : DecidableEq (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (LocalLabel command ⊕ Label LocalLabel commands))

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

def entry : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ → Option Λ
  | [], _, exit => exit
  | command :: _, labels, _ => some (labels (.inl (main command)))

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

def instruction : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ →
    Label LocalLabel commands → TM2.Stmt Γ Λ σ
  | [], _, _, label => nomatch label
  | command :: commands, labels, exit, .inl label =>
      localInstruction command (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit) label
  | _ :: commands, labels, exit, .inr label =>
      instruction commands (fun l => labels (.inr l)) exit label

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

def resultOf : List Command → Data → Data
  | [], data => data
  | command :: commands, data => resultOf commands (result command data)

def steps : List Command → Data → Nat
  | [], _ => 0
  | command :: commands, data => cost command data + steps commands (result command data)

end DFVSGames.Foundations.Complexity.MachineFiniteSequence


namespace DFVSGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev Tapes (K : Type) := K → List Bool
abbrev LocalLabel (_ : K) := Unit
abbrev Label (chosen : List K) := MachineFiniteSequence.Label (LocalLabel (K := K)) chosen
abbrev Data (K : Type) := Tapes K × Option Bool

def entry (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel (K := K)) (fun _ => ()) chosen labels exit

def result (source : K) (data : Data K) : Data K :=
  (Function.update data.1 source [], none)

def cost (source : K) (data : Data K) : Nat := (data.1 source).length + 1

def finalTapes : List K → Tapes K → Tapes K
  | [], base => base
  | source :: chosen, base => finalTapes chosen (Function.update base source [])

def finalRegister : List K → Option Bool → Option Bool
  | [], register => register
  | _ :: _, _ => none

omit [DecidableEq K] in
@[simp] theorem finalRegister_none (chosen : List K) : finalRegister chosen none = none := by
  cases chosen <;> rfl

def steps : List K → Tapes K → Nat
  | [], _ => 0
  | source :: chosen, base => (base source).length + 1 +
      steps chosen (Function.update base source [])

@[simp] theorem sequence_result (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.resultOf result chosen (base, register) =
      (finalTapes chosen base, finalRegister chosen register) := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      change MachineFiniteSequence.resultOf result chosen (Function.update base source [], none) =
        (finalTapes chosen (Function.update base source []), none)
      rw [ih, finalRegister_none]

@[simp] theorem sequence_steps (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.steps result cost chosen (base, register) = steps chosen base := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      simp only [MachineFiniteSequence.steps, result, cost, steps, ih]

theorem finalTapes_apply (chosen : List K) (base : Tapes K) (k : K) :
    finalTapes chosen base k = if k ∈ chosen then [] else base k := by
  induction chosen generalizing base with
  | nil => simp [finalTapes]
  | cons source chosen ih =>
      rw [finalTapes, ih]
      by_cases h : k = source
      · subst k
        simp
      · simp [List.mem_cons, h]

theorem finalTapes_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∈ chosen) :
    finalTapes chosen base k = [] := by rw [finalTapes_apply, ite_eq_left h]

theorem finalTapes_not_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∉ chosen) :
    finalTapes chosen base k = base k := by rw [finalTapes_apply, ite_eq_right h]

def workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K) : List K :=
  (List.ofFn (fun i => enumeration i)).filter (fun k => decide (k ≠ output))

@[simp] theorem mem_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output k : K) :
    k ∈ workTapes enumeration output ↔ k ≠ output := by
  have hmem : k ∈ List.ofFn (fun i => enumeration i) := by
    apply List.mem_ofFn.mpr
    exact ⟨enumeration.symm k, enumeration.apply_symm_apply k⟩
  simp [workTapes, hmem]

end DFVSGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_SumBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.FinishBounds

theorem subdivision_completeness (vH vB d τ : ℝ)
    (hH : 1 - d ≤ vH)
    (hround : |vB - (1 - (1 - vH) / 4)| ≤ τ / 4) :
    1 - (d + τ) / 4 ≤ vB := by
  have h := (abs_le.mp hround).1
  linarith

theorem final_completeness (vB vG d τ ε₀ ε : ℝ) (t : Nat) (ht : 0 < t)
    (hB : 1 - (d + τ) / 4 ≤ vB)
    (hG : 1 - (t : ℝ) * (1 - vB) ≤ vG)
    (hd : d ≤ ε₀ / t) (hτ : τ ≤ ε₀ / t)
    (hε₀ : 0 ≤ ε₀) (hε : ε₀ ≤ ε) :
    1 - ε ≤ vG := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hd' := (le_div_iff₀ ht').mp hd
  have hτ' := (le_div_iff₀ ht').mp hτ
  have hB' : (t : ℝ) * (1 - vB) ≤ t * ((d + τ) / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) ht'.le
  nlinarith

end DFVSGames.Explicit.FinishBounds


namespace DFVSGames.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

end DFVSGames.Foundations.Complexity.Runtime

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.MachineSubstitution

open Turing

open DFVSGames.Foundations.Complexity

section PushWord

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def pushWord (dst : K) : List (Γ dst) → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], continuation => continuation
  | symbol :: word, continuation =>
      .push dst (fun _ => symbol) (pushWord dst word continuation)

theorem stepAux_pushWord (dst : K) (word : List (Γ dst))
    (continuation : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (pushWord dst word continuation) state tapes =
      TM2.stepAux continuation state
        (Function.update tapes dst (word.reverse ++ tapes dst)) := by
  induction word generalizing tapes with
  | nil => simp [pushWord]
  | cons symbol word ih =>
    simp only [pushWord, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.reverse_cons,
      List.append_assoc, List.singleton_append]

end PushWord

def loop : TM2.Stmt (fun _ : Bool => Bool) (Option Bool) (Option Bool) :=
  .pop false (fun _ head => head)
    (.branch Option.isSome
      (.goto fun state => some (state.getD false))
      .halt)

def program (emit : Bool → List Bool) :
    Option Bool → TM2.Stmt (fun _ : Bool => Bool) (Option Bool) (Option Bool)
  | none => loop
  | some symbol => pushWord true (emit symbol) (.goto fun _ => none)

def machine (emit : Bool → List Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Option Bool
  main := none
  σ := Option Bool
  initialState := none
  m := program emit

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

def running (emit : Bool → List Bool) (input output : List Bool) (state : Option Bool) :
    (machine emit).Cfg :=
  ⟨some none, state, tapeStacks input output⟩

def emitting (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) : (machine emit).Cfg :=
  ⟨some (some symbol), state, tapeStacks input output⟩

def halted (emit : Bool → List Bool) (output : List Bool) : (machine emit).Cfg :=
  ⟨none, none, tapeStacks [] output⟩

theorem update_input_inline_MachineSubstitution (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output_inline_MachineSubstitution (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

theorem step_empty (emit : Bool → List Bool) (output : List Bool) (state : Option Bool) :
    (machine emit).step (running emit [] output state) = some (halted emit output) := by
  change some (TM2.stepAux loop state (tapeStacks [] output)) = some (halted emit output)
  simp [loop, TM2.stepAux, tapeStacks, halted]
  rw [update_input_inline_MachineSubstitution]
  rfl

theorem step_cons (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) :
    (machine emit).step (running emit (symbol :: input) output state) =
      some (emitting emit symbol input output (some symbol)) := by
  change some (TM2.stepAux loop state (tapeStacks (symbol :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, emitting]
  rw [update_input_inline_MachineSubstitution]
  rfl

theorem step_emit (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) :
    (machine emit).step (emitting emit symbol input output state) =
      some (running emit input ((emit symbol).reverse ++ output) state) := by
  change some (TM2.stepAux (pushWord true (emit symbol) (.goto fun _ => none))
    state (tapeStacks input output)) = _
  rw [stepAux_pushWord]
  simp only [TM2.stepAux]
  change some (⟨some none, state,
    Function.update (tapeStacks input output) true ((emit symbol).reverse ++ output)⟩ :
    TM2.Cfg (fun _ : Bool => Bool) (Option Bool) (Option Bool)) = _
  rw [update_output_inline_MachineSubstitution]
  rfl

def next (emit : Bool → List Bool) (configuration : Option (machine emit).Cfg) :
    Option (machine emit).Cfg :=
  configuration.bind (machine emit).step

theorem two_steps_cons (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) :
    (next emit)^[2] (some (running emit (symbol :: input) output state)) =
      some (running emit input ((emit symbol).reverse ++ output) (some symbol)) := by
  change (machine emit).step (running emit (symbol :: input) output state) >>=
    (machine emit).step = _
  rw [step_cons]
  exact step_emit emit symbol input output (some symbol)

theorem substitution_steps (emit : Bool → List Bool)
    (input output : List Bool) (state : Option Bool) :
    (next emit)^[2 * input.length + 1] (some (running emit input output state)) =
      some (halted emit ((input.flatMap emit).reverse ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.flatMap_nil, List.reverse_nil, List.nil_append]
      using step_empty emit output state
  | cons symbol input ih =>
    rw [List.length_cons]
    rw [show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega]
    rw [Function.iterate_add_apply, two_steps_cons, ih]
    simp only [List.flatMap_cons, List.reverse_append, List.append_assoc]

theorem initList_eq (emit : Bool → List Bool) (input : List Bool) :
    initList (machine emit) input = running emit input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (emit : Bool → List Bool) (output : List Bool) :
    haltList (machine emit) output = halted emit output := by
  unfold haltList halted
  congr 1

theorem substitution_init_steps (emit : Bool → List Bool) (input : List Bool) :
    (next emit)^[2 * input.length + 1] (some (initList (machine emit) input)) =
      some (haltList (machine emit) (input.flatMap emit).reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using substitution_steps emit input [] none

def outputsInTime (emit : Bool → List Bool) (input : List Bool) :
    TM2OutputsInTime (machine emit) input (some (input.flatMap emit).reverse)
      (2 * input.length + 1) where
  steps := 2 * input.length + 1
  evals_in_steps := substitution_init_steps emit input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (emit : Bool → List Bool) (input : List Bool) :
    (outputsInTime emit input).steps = 2 * input.length + 1 := rfl

end DFVSGames.Reduction.MachineSubstitution


namespace DFVSGames.Reduction.MachineReverse

open Turing

def loop : TM2.Stmt (fun _ : Bool => Bool) Unit (Option Bool) :=
  .pop false (fun _ head => head)
    (.branch Option.isSome
      (.push true (fun state => state.getD false) (.goto fun _ => ()))
      .halt)

def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ := loop

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

def running (input output : List Bool) (state : Option Bool) : machine.Cfg :=
  ⟨some (), state, tapeStacks input output⟩

def halted (output : List Bool) : machine.Cfg :=
  ⟨none, none, tapeStacks [] output⟩

theorem update_input_inline_MachineReverse (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output_inline_MachineReverse (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

theorem step_empty (output : List Bool) (state : Option Bool) :
    machine.step (running [] output state) = some (halted output) := by
  change some (TM2.stepAux loop state (tapeStacks [] output)) = some (halted output)
  simp [loop, TM2.stepAux, tapeStacks, halted, Function.update]
  rw [update_input_inline_MachineReverse]
  rfl

theorem step_cons (head : Bool) (input output : List Bool) (state : Option Bool) :
    machine.step (running (head :: input) output state) =
      some (running input (head :: output) (some head)) := by
  change some (TM2.stepAux loop state (tapeStacks (head :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, running, Function.update]
  rw [update_input_inline_MachineReverse, update_output_inline_MachineReverse]
  rfl

def next (configuration : Option machine.Cfg) : Option machine.Cfg :=
  configuration.bind machine.step

theorem reverse_steps (input output : List Bool) (state : Option Bool) :
    next^[input.length + 1] (some (running input output state)) =
      some (halted (input.reverse ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.reverse_nil, List.nil_append] using step_empty output state
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change next^[input.length + 1]
      (machine.step (running (head :: input) output state)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem initList_eq (input : List Bool) :
    initList machine input = running input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (output : List Bool) : haltList machine output = halted output := by
  unfold haltList halted
  congr 1

theorem reverse_init_steps (input : List Bool) :
    next^[input.length + 1] (some (initList machine input)) =
      some (haltList machine input.reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using reverse_steps input [] none

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input (some input.reverse) (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := reverse_init_steps input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (input : List Bool) :
    (outputsInTime input).steps = input.length + 1 := rfl

end DFVSGames.Reduction.MachineReverse


namespace DFVSGames.Foundations.Complexity.MachineControl

open Turing.TM2

variable {K Λ Λ' σ σ' : Type} {Γ : K → Type}

def configuration (labels : Λ → Λ') (states : σ ≃ σ') (c : Cfg Γ Λ σ) :
    Cfg Γ Λ' σ' where
  l := c.l.map labels
  var := states c.var
  stk := c.stk

def statement (labels : Λ → Λ') (states : σ ≃ σ') : Stmt Γ Λ σ → Stmt Γ Λ' σ'
  | .push k f next => .push k (fun st => f (states.symm st)) (statement labels states next)
  | .peek k f next => .peek k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .pop k f next => .pop k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .load f next => .load (fun st => states (f (states.symm st)))
      (statement labels states next)
  | .branch f yes no => .branch (fun st => f (states.symm st))
      (statement labels states yes) (statement labels states no)
  | .goto f => .goto (fun st => labels (f (states.symm st)))
  | .halt => .halt

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (states : σ ≃ σ')
    (q : Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement labels states q) (states state) tapes =
      configuration labels states (stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_false] using
        ihNo state tapes
    | true =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_true] using
        ihYes state tapes
  | goto f => simp [statement, stepAux, configuration]
  | halt => rfl

end DFVSGames.Foundations.Complexity.MachineControl


namespace DFVSGames.Foundations.Complexity.MachineSequential

open Turing

abbrev Tape (first second : FinTM2) := first.K ⊕ (second.K ⊕ Unit)
abbrev Label (first second : FinTM2) := first.Λ ⊕ (Bool ⊕ second.Λ)
abbrev Register (second : FinTM2) := Option (second.Γ second.k₀)
abbrev State (first second : FinTM2) := (first.σ × second.σ) × Register second

def firstStates (first second : FinTM2) :
    first.σ × (second.σ × Register second) ≃ State first second where
  toFun st := ((st.1, st.2.1), st.2.2)
  invFun st := (st.1.1, (st.1.2, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondStates (first second : FinTM2) :
    second.σ × (first.σ × Register second) ≃ State first second where
  toFun st := ((st.2.1, st.1), st.2.2)
  invFun st := (st.1.2, (st.1.1, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondLabels (first second : FinTM2) :
    second.Λ ⊕ (Bool ⊕ first.Λ) → Label first second
  | .inl label => .inr (.inr label)
  | .inr (.inl bit) => .inr (.inl bit)
  | .inr (.inr label) => .inl label

def bridgeLabel (first second : FinTM2) (bit : Bool) : Label first second :=
  .inr (.inl bit)

end DFVSGames.Foundations.Complexity.MachineSequential

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.MachineTransducer

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord )

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

theorem update_input_inline_MachineTransducer (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output_inline_MachineTransducer (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

variable {Q : Type} [Fintype Q]

def output (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Q → List Bool → List Bool
  | _, [] => []
  | state, symbol :: input =>
      emit state symbol ++ output transition emit (transition state symbol) input

def loop (initial : Q) :
    TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool) :=
  .pop false (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun state => some (state.1, state.2.getD false))
      (.load (fun _ => (initial, none)) .halt))

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
  rw [update_input_inline_MachineTransducer]
  rfl

theorem step_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state (symbol :: input) accumulator register) =
      some (emitting initial transition emit state symbol input accumulator (state, some symbol)) := by
  change some (TM2.stepAux (loop initial) (state, register)
    (tapeStacks (symbol :: input) accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, emitting]
  rw [update_input_inline_MachineTransducer]
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
    TM2.Cfg (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool)) = _
  rw [update_output_inline_MachineTransducer]
  rfl

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

def outputsInTime (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    TM2OutputsInTime (machine initial transition emit) input
      (some (output transition emit initial input).reverse) (2 * input.length + 1) where
  steps := 2 * input.length + 1
  evals_in_steps := transduce_init_steps initial transition emit input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    (outputsInTime initial transition emit input).steps = 2 * input.length + 1 := rfl

end DFVSGames.Reduction.MachineTransducer


namespace DFVSGames.Foundations.Complexity.MachineTransducerCopy

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ Q : Type} [DecidableEq K]

abbrev Alphabet (K : Type) (_ : K) := Bool
abbrev State (σ Q : Type) := (σ × Q) × Option Bool

def scanLoop (source scratch : K) (initial : Q)
    (emitterLabel : Q → Bool → Λ) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push scratch (fun state => state.2.getD false)
        (.goto fun state => emitterLabel state.1.2 (state.2.getD false)))
      (.load (fun state => ((state.1.1, initial), none)) (.goto fun _ => restoreLabel)))

def emitter (destination : K) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (scanLabel : Λ) (control : Q) (symbol : Bool) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .load (fun state => ((state.1.1, transition control symbol), state.2))
    (pushWord destination (emit control symbol) (.goto fun _ => scanLabel))

end DFVSGames.Foundations.Complexity.MachineTransducerCopy


namespace DFVSGames.Reduction.MachineFieldTemplate

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q : Nat} {K Λ σ : Type}

inductive Label (m : Nat)
  | entry (index : Fin m)
  | scan (index : Fin m)
  | emit (index : Fin m) (symbol : Bool)
  | restore (index : Fin m)
  | done
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet (_ : K) := Bool

def reset (state : State σ) : State σ := ((state.1.1, ()), none)

@[simp] theorem reset_reset (state : State σ) : reset (reset state) = reset state := rfl

def startAt (m i : Nat) : Label m :=
  if h : i < m then .entry ⟨i, h⟩ else .done

def jump (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def identityEmit (_ : Unit) (b : Bool) : List Bool := [b]

variable [DecidableEq K]

def outputTapes (base : K → List Bool) (output : K) (bits : List Bool) : K → List Bool :=
  Function.update base output (bits.reverse ++ base output)

@[simp] theorem outputTapes_self (base : K → List Bool) (output : K) :
    outputTapes base output [] = base := by simp [outputTapes]

@[simp] theorem outputTapes_output (base : K → List Bool) (output : K) (bits : List Bool) :
    outputTapes base output bits output = bits.reverse ++ base output := by simp [outputTapes]

theorem outputTapes_other (base : K → List Bool) (output : K) (bits : List Bool)
    (tape : K) (different : tape ≠ output) :
    outputTapes base output bits tape = base tape := by simp [outputTapes, different]

end DFVSGames.Reduction.MachineFieldTemplate

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (clearKeys : List K) := MachineDrainMany.Label clearKeys ⊕ Bool
abbrev Tapes (K : Type) := K → List Bool

def entry (clearKeys : List K) (labels : Label clearKeys → Λ) : Option Λ :=
  MachineDrainMany.entry clearKeys (fun l => labels (.inl l)) (some (labels (.inr false)))

def canonicalTapes (output : K) (word : List Bool) : Tapes K :=
  Function.update (fun _ => []) output word

open scoped BigOperators


end DFVSGames.Foundations.Hastad.SourceRuntimeFinish


namespace DFVSGames.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (restoreLabel : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun s => (s.1,none)) (.goto (fun _ => restoreLabel))

def scan (source scratch destination : K) (coefficient : Nat) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun s head => (s.1,head))
    (.branch (fun s => s.2.getD false)
      (.push scratch (fun _ => true)
        (pushWord destination (List.replicate coefficient true) (.goto (fun _ => scanLabel))))
      (.branch (fun s => s.2.isSome)
        (.push source (fun _ => false) (finish restoreLabel))
        (finish restoreLabel)))

inductive Label
  | seed | scan | restore
  deriving DecidableEq

instance instFintypeLabel : Fintype Label :=
  Fintype.ofList [.seed, .scan, .restore] (by
    intro label
    cases label <;> simp)

end DFVSGames.Foundations.Complexity.MachineUnaryAffineAt


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_FormulaEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

@[simp] theorem parseLabel_value {q : Nat} (label : Fin q) :
    parseLabel q label.val = some label := by simp [parseLabel, label.isLt]

@[simp] theorem parseLabels_values {q : Nat} (labels : List (Fin q)) :
    (labels.map Fin.val).mapM (parseLabel q) = some labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp [ih]

end DFVSGames.Foundations.Complexity


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_MatrixCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

def fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  𝔼 x, f x * star (ψ x)

end FiniteGroup

variable {E F : Type*}
variable [AddCommGroup E]
  [AddCommGroup F]

theorem complex_ofReal_expect {J : Type*} [Fintype J] (f : J → ℝ) :
    ((𝔼 j, f j : ℝ) : ℂ) = 𝔼 j, (f j : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  exact map_sum Complex.ofRealHom f Finset.univ

end DFVSGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def guard (counter : K) (bodyLabel exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek counter (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop counter (fun state _ => (state.1, none)) (.goto fun _ => bodyLabel))
      (.load (fun state => (state.1, none)) (.goto fun _ => exitLabel)))

end DFVSGames.Foundations.Complexity.MachineUnaryCounter


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

theorem input_finite (M : FinTM2) : Finite (M.Γ M.k₀) := by
  let := M.Γk₀Fin
  infer_instance

end DFVSGames.Foundations.Complexity.MachineFiniteAlphabet


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryNameMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.BinaryNameMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: bits => true :: bit :: frame bits

def finalDigit : List Bool → Option Bool → Option Bool
  | [], previous => previous
  | bit :: bits, _ => finalDigit bits (some bit)

def canonical (bits : List Bool) : Bool := (finalDigit bits none).getD true

structure Result where
  accepted : Bool
  remaining : List Bool
  reversedPayload : List Bool
  deriving DecidableEq

def scanSpec : List Bool → List Bool → Option Bool → Result
  | [], acc, _ => ⟨false, [], acc⟩
  | false :: rest, acc, last => ⟨last.getD true, rest, acc⟩
  | [true], acc, _ => ⟨false, [], acc⟩
  | true :: bit :: rest, acc, _ => scanSpec rest (bit :: acc) (some bit)

def steps : List Bool → Nat
  | true :: _ :: rest => steps rest + 1
  | _ => 1

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [frame]
  | cons bit bits ih => simp only [frame, List.length_cons, ih]; omega

theorem scanSpec_frame (bits suffix acc : List Bool) (last : Option Bool) :
    scanSpec (frame bits ++ suffix) acc last =
      ⟨(finalDigit bits last).getD true, suffix, bits.reverse ++ acc⟩ := by
  induction bits generalizing acc last with
  | nil => simp [frame, scanSpec, finalDigit]
  | cons bit bits ih =>
      simpa [frame, scanSpec, finalDigit, List.reverse_cons, List.append_assoc] using
        ih (bit :: acc) (some bit)

@[simp] theorem steps_frame (bits suffix : List Bool) :
    steps (frame bits ++ suffix) = bits.length + 1 := by
  induction bits with
  | nil => simp [frame, steps]
  | cons bit bits ih => simp [frame, steps, ih]

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool × Option Bool

def clean (ambient : A) : State A := (ambient, none, none)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1) (exitAt exit)

def scan (source destination : K) (again : Λ) (accepted rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, state.2.1, head))
    (.branch (fun state => state.2.2.isNone)
      (finish rejected)
      (.branch (fun state => state.2.2.getD false)
        (.pop source (fun state head => (state.1, state.2.1, head))
          (.branch (fun state => state.2.2.isSome)
            (.push destination (fun state => state.2.2.getD false)
              (.load (fun state => (state.1, state.2.2, none))
                (.goto fun _ => again)))
            (finish rejected)))
        (.branch (fun state => state.2.1.getD true)
          (finish accepted) (finish rejected))))

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A)
    (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

end Program

end DFVSGames.BinaryNameMachine


namespace DFVSGames.BinaryParsing

theorem canonical_cons_cons (a b : Bool) (bits : List Bool) :
    BinaryNameMachine.canonical (a :: b :: bits) = BinaryNameMachine.canonical (b :: bits) := rfl

end DFVSGames.BinaryParsing


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def discard (source : K) (loopLabel returnLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => returnLabel)))

def select (source destination : K) (copyLabel rejected : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (Hastad.SourceMachine.fieldStart destination copyLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => rejected)))

inductive Label
  | guard | skip | select | copy | accepted | rejected
  deriving DecidableEq

def tapes (index source destination : K) (base : K → List Bool)
    (counter input output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base index counter) source input)
    destination output

end DFVSGames.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLookupSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineSubroutine

open Turing

variable {K Λ Λ' σ : Type} {Γ : K → Type}

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | none => exit
  | some l => some (labels l)

def configuration (labels : Λ → Λ') (exit : Option Λ') (c : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ := ⟨label labels exit c.l, c.var, c.stk⟩

def statement (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (statement labels exit next)
  | .peek k f next => .peek k f (statement labels exit next)
  | .pop k f next => .pop k f (statement labels exit next)
  | .load f next => .load f (statement labels exit next)
  | .branch f yes no => .branch f (statement labels exit yes) (statement labels exit no)
  | .goto f => .goto (fun s => labels (f s))
  | .halt => match exit with
      | none => .halt
      | some l => .goto (fun _ => l)

end DFVSGames.Foundations.Complexity.MachineSubroutine


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end DFVSGames.Foundations.Complexity.MachinePreservingLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FieldArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceFieldArray

open Turing
open DFVSGames.Foundations.Complexity SourceMachine

variable {K Λ σ : Type} [DecidableEq K]

def boundedIndex (q j : Nat) : Fin (q + 1) := ⟨min j q, by omega⟩

@[simp] theorem boundedIndex_val {q j : Nat} (hj : j ≤ q) :
    (boundedIndex q j).val = j := Nat.min_eq_left hj

def startLabel (q j : Nat) : Fin (q + 1) × Bool := (boundedIndex q j, false)

end DFVSGames.Foundations.Hastad.SourceFieldArray


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_ContextLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceContextLoad

open Turing DFVSGames.Foundations.Complexity
open MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def variableSlot (s : Fin 3) : Fin 6 := ⟨2 * s.val, by omega⟩

end DFVSGames.Foundations.Hastad.SourceContextLoad


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_CloneGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.CloneGap

variable {Element OtherElement : Type*}

abbrev Index := Nat

end DFVSGames.Reduction.CloneGap


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineFieldProfile

open Turing

abbrev Profile (q : Nat) := Fin q → Fin q → Bool

def equalityProfile {q : Nat} (words : Fin q → List Bool) : Profile q :=
  fun i j => decide (words i = words j)

abbrev Tape (q : Nat) := Fin q ⊕ Fin 3


end DFVSGames.Foundations.Complexity.MachineFieldProfile


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SignaturePrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineStateFrame

open Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

def frameStatement : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ (σ × τ)
  | .push k f next => .push k (fun state => f state.1) (frameStatement next)
  | .peek k f next => .peek k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .pop k f next => .pop k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (frameStatement next)
  | .branch f yes no => .branch (fun state => f state.1)
      (frameStatement yes) (frameStatement no)
  | .goto f => .goto (fun state => f state.1)
  | .halt => .halt

def frameConfiguration (ambient : τ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ (σ × τ) :=
  ⟨c.l, (c.var, ambient), c.stk⟩

def frameProgram (source : Λ → TM2.Stmt Γ Λ σ) : Λ → TM2.Stmt Γ Λ (σ × τ) :=
  fun label => frameStatement (source label)

@[simp] theorem frameConfiguration_state (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.1 = c.var := rfl

@[simp] theorem frameConfiguration_metadata (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.2 = ambient := rfl

@[simp] theorem frameConfiguration_tapes (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).stk = c.stk := rfl

def configuration (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' (σ × τ) :=
  MachineSubroutine.configuration labels exit (frameConfiguration ambient c)

@[simp] theorem configuration_state (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.1 = c.var := rfl

@[simp] theorem configuration_metadata (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.2 = ambient := rfl

@[simp] theorem configuration_tapes (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).stk = c.stk := rfl

variable [DecidableEq K]

theorem frame_stepAux (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ)
    (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (frameStatement q) (state, ambient) tapes =
      frameConfiguration ambient (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [frameStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
    | true => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

theorem frame_step (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) :
    TM2.step (frameProgram source) (frameConfiguration ambient c) =
      (TM2.step source c).map (frameConfiguration ambient) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
    change some (TM2.stepAux (frameStatement (source label)) (state, ambient) tapes) = _
    rw [frame_stepAux]
    rfl

end DFVSGames.Foundations.Complexity.MachineStateFrame


namespace DFVSGames.Foundations.Hastad.SourceContextPrepare

open Turing DFVSGames.Foundations.Complexity
abbrev LoadState := Unit × Option Bool

end DFVSGames.Foundations.Hastad.SourceContextPrepare

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAffineLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end DFVSGames.Foundations.Complexity.MachineAffineLookup


namespace DFVSGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

inductive Label
  | copyDrain | copyFork | seed | guard | scan | emitFalse | emitTrue | restore | finish
  deriving DecidableEq

instance instFintypeLabel : Fintype Label :=
  Fintype.ofList [.copyDrain, .copyFork, .seed, .guard, .scan, .emitFalse, .emitTrue,
    .restore, .finish] (by intro label; cases label <;> simp)

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (_ : Unit) (bit : Bool) : List Bool := if bit then [true] else []

def emitterLabel (labels : Label → Λ) (_ : Unit) (bit : Bool) : Λ :=
  if bit then labels .emitTrue else labels .emitFalse

end DFVSGames.Foundations.Complexity.MachineUnaryMultiply

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineUnaryAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineRadixStep

open Turing

variable {K Λ σ : Type}

inductive Label
  | multiply (label : MachineUnaryMultiply.Label)
  | digitDrain | digitFork | add | finish
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := MachineUnaryMultiply.State σ

end DFVSGames.Foundations.Complexity.MachineRadixStep


namespace DFVSGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := MachineRadixStep.State σ

inductive Label (width : Nat)
  | start
  | radix (i : Fin width) (inner : MachineRadixStep.Label)
  | clear (i : Fin width)
  | finishDrain | finishRestore
  deriving DecidableEq, Fintype

def entryLabel (width n : Nat) : Label width :=
  if h : n < width then .radix ⟨n, h⟩ (.multiply .copyDrain) else .finishDrain

open scoped BigOperators

end DFVSGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_LoopInit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceLoopInit

open Turing DFVSGames.Foundations.Complexity
open MachineComposition SourceMachine

inductive HeaderTape | variableCount | clauseCount
  deriving DecidableEq

end DFVSGames.Foundations.Hastad.SourceLoopInit


namespace DFVSGames.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity

inductive BodyWork (Extra : Type)
  | leftBlock | dummy | bitCount | occurrenceCount
  | zero | rank | rightBase | leftBase
  | accA | accB | counter | arithScratch | coefficient
  | queryTemporary | queryScratch | accumulator
  | extra (value : Extra)
  deriving DecidableEq, Fintype

abbrev ArithmeticState := MachineHorner.State Unit

end DFVSGames.Foundations.Hastad.SourceRuntimeModel

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_CookLevin_PolynomialMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.CookLevin.PolynomialMachine

noncomputable def coefficientPolynomial : List Nat → Polynomial Nat
  | [] => 0
  | a :: rest => coefficientPolynomial rest * Polynomial.X + Polynomial.C a

noncomputable def coefficients (p : Polynomial Nat) :
    {cs : List Nat // coefficientPolynomial cs = p} := by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[], rfl⟩
  · intro q a hq ha ih
    rcases ih with ⟨cs, hcs⟩
    cases cs with
    | nil =>
      refine ⟨[a], ?_⟩
      rw [← hcs]
      simp [coefficientPolynomial]
    | cons b rest =>
      refine ⟨(b + a) :: rest, ?_⟩
      rw [← hcs]
      simp only [coefficientPolynomial, Polynomial.C_add, add_assoc]
  · intro q hq ih
    rcases ih with ⟨cs, hcs⟩
    refine ⟨0 :: cs, ?_⟩
    simp only [coefficientPolynomial, Polynomial.C_0, add_zero, hcs]

noncomputable def highCoefficients (p : Polynomial Nat) : List Nat :=
  (coefficients p).val.reverse

noncomputable def width (p : Polynomial Nat) : Nat := (highCoefficients p).length

noncomputable def digit (p : Polynomial Nat) (i : Nat) : Nat :=
  if hi : i < width p then (highCoefficients p)[i] else 0

section LiteralFields

open Turing
open DFVSGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def prependFields (word : K → List Bool) : List K →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], continuation => continuation
  | k :: rest, continuation =>
      pushWord k (word k).reverse (prependFields word rest continuation)

def prependFieldsTapes (word : K → List Bool) : List K →
    (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes =>
      prependFieldsTapes word rest (Function.update tapes k (word k ++ tapes k))

theorem prependFieldsTapes_apply (word : K → List Bool) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    prependFieldsTapes word indices tapes k =
      if k ∈ indices then word k ++ tapes k else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [prependFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [prependFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

def popN (k : K) : Nat → TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, continuation => continuation
  | n + 1, continuation => .pop k (fun state _ => state) (popN k n continuation)

def clearFields (count : K → Nat) : List K →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], continuation => continuation
  | k :: rest, continuation => popN k (count k) (clearFields count rest continuation)

end LiteralFields

end DFVSGames.Foundations.Complexity.CookLevin.PolynomialMachine


namespace DFVSGames.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

noncomputable section

def leftValue (u n : Nat) : Nat := 2 ^ (2 ^ u) * n ^ u
def rightValue (u m : Nat) : Nat := 2 ^ (8 ^ u) * m ^ u
def dummyValue (u n m : Nat) : Nat := leftValue u n + rightValue u m
def bitValue (u n m : Nat) : Nat := dummyValue u n m + 1

inductive Kind | left | right | occurrences
  deriving DecidableEq

inductive Control
  | variableCount | clauseCount | leftBlockSize | rightTemporary | dummyIndex
  | bitCount | occurrenceCount | accA | accB | counter | scratch
  deriving DecidableEq

end

end DFVSGames.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineOdometerInit
open Turing

inductive Tape (k : Nat)
  | radix | scratch | current (j : Fin k) | remaining (j : Fin k)
  deriving DecidableEq, Fintype

inductive Label (k : Nat)
  | seed (j : Fin k) | copyOut (j : Fin k) | copyBack (j : Fin k) | trim (j : Fin k)
  | done
  deriving DecidableEq, Fintype

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def labelAt (labels : Label k → Λ) (r : Nat) : Λ :=
  if h : r < k then labels (.seed ⟨r,h⟩) else labels .done

end DFVSGames.Foundations.Complexity.MachineOdometerInit

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_TupleOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineTupleOdometer
open Turing
open Reduction.MachineTransfer
variable {K Λ σ : Type} [DecidableEq K]
section Order
omit [DecidableEq K]
open scoped BigOperators

theorem tupleRank_snoc {n q : ℕ} (tail : Fin q → Fin n) (d : Fin n) :
    (finFunctionFinEquiv (Fin.snoc tail d)).val =
      (finFunctionFinEquiv tail).val + d.val * n ^ q := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rfl

end Order


end DFVSGames.Foundations.Complexity.MachineTupleOdometer


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_TraceLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

end DFVSGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FinishReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Decoder.SparseLaw

open scoped BigOperators
open DFVSGames.Foundations.Information

noncomputable section

variable {α : Type*} [Fintype α]

def uniformWeights (α : Type*) [Fintype α] : α → ℝ :=
  fun _ => 1 / Fintype.card α

theorem uniformWeights_pos [Nonempty α] (a : α) : 0 < uniformWeights α a := by
  exact div_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)

theorem uniformWeights_isProbability [Nonempty α] :
    IsProbability (uniformWeights α) := by
  constructor
  · exact fun a => (uniformWeights_pos a).le
  · simp [uniformWeights, Fintype.card_ne_zero]

def uniformChiSquare (p : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ) * ∑ a, (p a - uniformWeights α a) ^ 2

def mixture (β : ℝ) (p : α → ℝ) : α → ℝ :=
  fun a => (1 - β) * uniformWeights α a + β * p a

def independentWeights (p : α → ℝ) (k : ℕ) : (Fin k → α) → ℝ :=
  fun x => ∏ i, p (x i)

theorem independentWeights_isProbability (p : α → ℝ) (hp : IsProbability p)
    (k : ℕ) : IsProbability (independentWeights p k) := by
  constructor
  · intro x
    exact Finset.prod_nonneg fun i _ => hp.1 (x i)
  · change (∑ x : Fin k → α, ∏ i, p (x i)) = 1
    rw [← Fintype.sum_pow, hp.2, one_pow]

section Singleton

variable (V : Type*) [Fintype V] [Zero V] [DecidableEq V]

def lineCount (z : V × V) : ℝ :=
  (if z.2 = 0 then 1 else 0) + (if z.1 = 0 then 1 else 0) +
    (if z.1 = z.2 then 1 else 0)

def singletonPairWeights (z : V × V) : ℝ := lineCount V z / (3 * Fintype.card V)

def singletonSamplerWeights (z : V × V) : ℝ :=
  ((∑ a : V, if (a, 0) = z then uniformWeights V a else 0) +
    (∑ a : V, if (0, a) = z then uniformWeights V a else 0) +
    (∑ a : V, if (a, a) = z then uniformWeights V a else 0)) / 3

end Singleton


end
end DFVSGames.Decoder.SparseLaw


namespace DFVSGames.Soundness.PartnerProjection

theorem and_xor (b h h' : Bool) :
    (b && h).xor (b && h') = (b && h.xor h') := by
  cases b <;> cases h <;> cases h' <;> decide

end DFVSGames.Soundness.PartnerProjection

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KernelCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.ZeroInformation

abbrev Bits (R : Type) := R → Bool

def zero {R : Type} : Bits R := fun _ => false

def add {R : Type} (a b : Bits R) : Bits R := fun r => a r ^^ b r

def scale {R : Type} (coefficient : Bits R) (bit : Bool) : Bits R :=
  fun r => coefficient r && bit

@[simp] theorem scale_zero {R : Type} (bit : Bool) :
    scale (zero : Bits R) bit = zero := by
  funext r
  simp [scale, zero]

def rowSum {P R : Type} (positions : List P) (term : P → Bits R) : Bits R :=
  positions.foldr (fun j acc => add (term j) acc) zero

def pullbackRow {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (indices : P → Fin 3) (homogeneous : Bool) (x : P → Fin 3 → Bool) : Bits R :=
  add (scale zeta0 homogeneous) (rowSum positions fun j =>
    if single j then scale (omega j) (x j (indices j))
    else add (scale (zeta1 j) (x j 0)) (scale (zeta2 j) (x j 1)))

abbrev FirstRow (P R : Type) := Bool → (P → Fin 3 → Bool) → Bits R

abbrev SecondRow (P R : Type) :=
  Bool → (P → Fin 3 → Bool) → (P → Bool) → Bits R

structure FirstInput (P R O : Type) where
  question : P → O
  row : FirstRow P R

structure SecondInput (P R O N : Type) where
  question : P → Sum O N
  row : SecondRow P R

def partnerQuestion {P O N : Type} (single : P → Bool) (occurrences : P → O)
    (names : P → N) : P → Sum O N :=
  fun j => if single j then .inr (names j) else .inl (occurrences j)

def partnerRow {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) : SecondRow P R :=
  fun homogeneous x y => add (scale zeta0 homogeneous) (rowSum positions fun j =>
    if single j then scale (omega j) (y j)
    else add (scale (zeta1 j) (x j 0)) (scale (zeta2 j) (x j 1)))

def firstInput {P R O : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (indices : P → Fin 3) : FirstInput P R O :=
  ⟨occurrences, pullbackRow positions single zeta0 zeta1 zeta2 omega indices⟩

def secondInput {P R O N : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (names : P → N) : SecondInput P R O N :=
  ⟨partnerQuestion single occurrences names,
    partnerRow positions single zeta0 zeta1 zeta2 omega⟩

def projectFull {P : Type} (single : P → Bool) (x : P → Fin 3 → Bool) :
    P → Fin 3 → Bool :=
  fun j i => if single j then false else x j i

def projectSingles {P : Type} (single : P → Bool) (indices : P → Fin 3)
    (x : P → Fin 3 → Bool) : P → Bool :=
  fun j => if single j then x j (indices j) else false

end DFVSGames.Soundness.ZeroInformation

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ConditionalIncidences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

abbrev Draw (P O : Type) := P → O × Fin 3

end

end DFVSGames.Soundness.ConditionalIncidences
end

namespace DFVSGames.Soundness.IncidenceExtraction

structure Game (QA QB A B : Type) where
  accepts : QA → QB → A → B → Prop

structure Strategies (QA QB A B : Type) where
  first : QA → A
  second : QB → B

def Strategies.wins {QA QB A B : Type} (s : Strategies QA QB A B)
    (g : Game QA QB A B) (qa : QA) (qb : QB) : Prop :=
  g.accepts qa qb (s.first qa) (s.second qb)

end DFVSGames.Soundness.IncidenceExtraction

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

instance zeroBits (R : Type) : Zero (ZeroInformation.Bits R) :=
  ⟨ZeroInformation.zero⟩

def membershipBool {P : Type} [DecidableEq P] (J : Finset P) : P → Bool :=
  fun j => decide (j ∈ J)

end

end DFVSGames.Soundness.ConditionalIncidences

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_RepeatedGameBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Soundness.RepeatedGameBounds

open scoped BigOperators

noncomputable section

namespace Simulation

abbrev PredicateGame := IncidenceExtraction.Game

end Simulation

end
end DFVSGames.Soundness.RepeatedGameBounds

namespace DFVSGames.Soundness.ActualPointAnswers
open DFVSGames.Reduction
open PartnerProjection
open RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat}

def displayedRhs {Id Name : Type} (rhs : Id → Bool) (question : Fin k → Sum Id Name) :
    Fin k → Bool := fun j => match question j with
  | .inl o => rhs o
  | .inr _ => false

end
end DFVSGames.Soundness.ActualPointAnswers

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ProductLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean.WeightedPartition

open scoped BigOperators

noncomputable section

variable {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]

def fibre (observe : Ω → H) (h : H) : Ω → Bool :=
  fun x => decide (observe x = h)

end
end DFVSGames.Clean.WeightedPartition

namespace DFVSGames.Soundness.ConditionalSimulation

open ConditionalIncidences IncidenceExtraction
open RepeatedGameBounds

noncomputable section

instance firstInputFintype {P R O : Type} [Fintype P] [Fintype R] [Fintype O] :
    Fintype (ZeroInformation.FirstInput P R O) := by
  classical
  exact Fintype.ofEquiv ((P → O) × ZeroInformation.FirstRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

instance secondInputFintype {P R O N : Type}
    [Fintype P] [Fintype R] [Fintype O] [Fintype N] :
    Fintype (ZeroInformation.SecondInput P R O N) := by
  classical
  exact Fintype.ofEquiv ((P → Sum O N) × ZeroInformation.SecondRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

end
end DFVSGames.Soundness.ConditionalSimulation

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Mixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean

open scoped BigOperators

noncomputable section

def maskCount {k : ℕ} (mask : Fin k → Bool) : ℕ :=
  (Finset.univ.filter fun i => mask i = true).card

variable {E : Type*} [Fintype E] [Nonempty E]

def cleanProbability (β : ℝ) (E : Type*) [Fintype E] : ℝ :=
  β / (Fintype.card E : ℝ)

omit [Nonempty E] in
theorem cleanProbability_nonneg {β : ℝ} (hβ₀ : 0 ≤ β) :
    0 ≤ cleanProbability β E :=
  div_nonneg hβ₀ (Nat.cast_nonneg _)

theorem cleanProbability_le_one {β : ℝ} (hβ₁ : β ≤ 1) :
    cleanProbability β E ≤ 1 := by
  have hc : (1 : ℝ) ≤ Fintype.card E := by
    exact_mod_cast Fintype.card_pos (α := E)
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hc)).mpr
  simpa using hβ₁.trans hc

def cleanBit (origin : E) (sample : Bool × E) : Bool := by
  classical
  exact sample.1 && decide (sample.2 = origin)

end
end DFVSGames.Clean

namespace DFVSGames.Clean.Experiment

open scoped BigOperators
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation

noncomputable section

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

abbrev Coefficient (R : Type) := ZeroInformation.Bits R
abbrev Additional (k : ℕ) (R : Type) := Coefficient R × (Fin k → Coefficient R × Coefficient R)
abbrev SparseSeed (k : ℕ) (R : Type) := Fin k → Bool × Coefficient R

def singletonSet {k : ℕ} (seed : SparseSeed k R) : Finset (Fin k) :=
  Finset.univ.filter fun i => (seed i).1 = true

end
end DFVSGames.Clean.Experiment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PartnerFullSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Clean.NativeExperiment

open Soundness
open Soundness.ConditionalIncidences
open Experiment
open scoped BigOperators

noncomputable section

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def maskSet {k : ℕ} (mask : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => mask i = true

end
end DFVSGames.Clean.NativeExperiment


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Explicit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Decoder.PaddedLaw

open scoped BigOperators
open DFVSGames.Reduction
open DFVSGames.Soundness
open ConditionalIncidences PartnerProjection
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePushforward

variable {α B : Type*} [Fintype α]

def pushforwardWeight (p : α → ℝ) (f : α → B) (y : B) : ℝ :=
  ∑ x, if f x = y then p x else 0

end FinitePushforward


end
end DFVSGames.Decoder.PaddedLaw

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualAdviceUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.ActualCompleteness

open scoped BigOperators

section Source

theorem expect_function_apply {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (j : I) (f : Ω → ℚ) :
    (𝔼 U : I → Ω, f (U j)) = 𝔼 w : Ω, f w := by
  classical
  calc
    (𝔼 U : I → Ω, f (U j)) =
        𝔼 p : Ω × ({j' : I // j' ≠ j} → Ω), f p.1 := by
      apply Fintype.expect_equiv (Equiv.funSplitAt j Ω)
      intro U
      rfl
    _ = 𝔼 w : Ω, f w := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

end Source

section ActualLabeling
noncomputable section

theorem expect_pair_inline_ActualCompleteness {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℚ) :
    (𝔼 p : I × J, f p) = 𝔼 i : I, 𝔼 j : J, f (i, j) :=
  Finset.expect_product _ _ _

end
end ActualLabeling

end DFVSGames.Reduction.ActualCompleteness
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CanonicalAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Integration.VertexEmbedding

noncomputable def extendLabeling {n m q : Nat} (f : Fin n → Fin m)
    (labeling : Fin n → Fin q) (defaultLabel : Fin q) (v : Fin m) : Fin q := by
  classical
  exact if h : ∃ u, f u = v then labeling (Classical.choose h) else defaultLabel

end DFVSGames.Integration.VertexEmbedding
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ProfileCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealEndpoint (q : X × Y) (side : Bool) : X ⊕ Y :=
  if side then Sum.inr q.2 else Sum.inl q.1

end
end DFVSGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_GeneratorModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceHeaderAccumulate

open Turing DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

structure Layout (K : Type) where
  bits : K
  count : K
  accumulator : K
  bits_count : bits ≠ count
  bits_accumulator : bits ≠ accumulator
  count_accumulator : count ≠ accumulator

end DFVSGames.Foundations.Hastad.SourceHeaderAccumulate


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_ContextClear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceTupleTape

open Turing Complexity SourceRuntimeModel

structure Snapshot where
  rank : List Bool := []
  rightBase : List Bool := []
  leftBase : List Bool := []
  zero : List Bool := []
  emitted : List Bool := []
  deriving DecidableEq, Inhabited

end DFVSGames.Foundations.Hastad.SourceTupleTape

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP

structure ConstraintGraph (V E A : Type*) where
  reverse : E ≃ E
  reverse_involutive : Function.Involutive reverse
  tail : E → V
  accepts : E → A → A → Bool
  reverse_accepts : ∀ e a b, accepts (reverse e) b a = accepts e a b

namespace ConstraintGraph

variable {V E A : Type*}

def head (G : ConstraintGraph V E A) (e : E) : V := G.tail (G.reverse e)

@[simp] theorem head_reverse (G : ConstraintGraph V E A) (e : E) :
    G.head (G.reverse e) = G.tail e := by
  simp only [head, G.reverse_involutive e]

def edgeSatisfied (G : ConstraintGraph V E A) (labeling : V → A) (e : E) : Bool :=
  G.accepts e (labeling (G.tail e)) (labeling (G.head e))

@[simp] theorem edgeSatisfied_reverse (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    G.edgeSatisfied labeling (G.reverse e) = G.edgeSatisfied labeling e := by
  simpa only [edgeSatisfied, head, G.reverse_involutive e] using
    G.reverse_accepts e (labeling (G.tail e)) (labeling (G.tail (G.reverse e)))

def rejectedDarts [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) :
    Finset E := Finset.univ.filter (fun e => G.edgeSatisfied labeling e = false)

def rejectionCount [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) : Nat :=
  (G.rejectedDarts labeling).card

end ConstraintGraph

end DFVSGames.Foundations.PCP

namespace DFVSGames.Foundations.PCP.GraphTables

open DFVSGames.Foundations.Complexity

def bitWord (b : Bool) : Nat := if b then 1 else 0

def parseBit : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

end DFVSGames.Foundations.PCP.GraphTables

namespace DFVSGames.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

end DFVSGames.Foundations.PCP.PoweringWalks

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PortTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PortTables

open PoweringWalks

def rowIndex (vertices ports : Nat) :
    Fin vertices × Fin ports ≃ Fin (vertices * ports) := finProdFinEquiv

@[simp] theorem rowIndex_val (n d : Nat) (e : Fin n × Fin d) :
    (rowIndex n d e).val = e.2.val + d * e.1.val := rfl

end DFVSGames.Foundations.PCP.PortTables


noncomputable section

namespace DFVSGames.Foundations.PCP.AssignmentTester

open DFVSGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

variable {K : Type*} [Fintype K] [Nonempty K]

def eventAccepts (kind : Fin 4) (b : Fin 6 → Bool) : Bool :=
  if kind = 0 then decide ((b 0 ^^ b 1) = b 2)
  else if kind = 1 then decide ((b 0 ^^ b 1) = ((b 2 ^^ b 3) && (b 4 ^^ b 5)))
  else if kind = 2 then (b 0 ^^ b 1)
  else decide (b 0 = (b 1 ^^ b 2))

end DFVSGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CayleySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset
open DFVSGames.Foundations.Hastad

variable {V D : Type*}

abbrev FalseFiber (χ : V → Bool) := {x : V // χ x = false}

def falseRepresentative (χ : V → Bool) (flip : V → V)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) : FalseFiber χ :=
  if h : χ x = false then ⟨x, h⟩
  else ⟨flip x, by cases hx : χ x <;> simp_all⟩

def booleanSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    V ≃ Bool × FalseFiber χ where
  toFun x := (χ x, falseRepresentative χ flip hχ x)
  invFun p := if p.1 then flip p.2.val else p.2.val
  left_inv x := by
    cases hx : χ x <;> simp [falseRepresentative, hx]
    exact hflip x
  right_inv p := by
    rcases p with ⟨b, x⟩
    apply Prod.ext
    · cases b <;> simp [hχ, x.property]
    · cases b <;> apply Subtype.ext <;>
        simp [falseRepresentative, hχ, x.property]
      exact hflip x.val

@[simp] theorem booleanSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) :
    (booleanSplitEquiv χ flip hflip hχ x).1 = χ x := rfl

def sampleSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    (D → V) ≃ (D → Bool) × (D → FalseFiber χ) :=
  (Equiv.piCongrRight fun _ : D => booleanSplitEquiv χ flip hflip hχ).trans
    (Equiv.arrowProdEquivProdArrow D (fun _ => Bool) (fun _ => FalseFiber χ))

@[simp] theorem sampleSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (g : D → V) :
    (sampleSplitEquiv χ flip hflip hχ g).1 = fun d => χ (g d) := rfl

theorem expect_boolean_samples [Fintype V] [Nonempty V] [Fintype D] [DecidableEq D]
    (χ : V → Bool) (flip : V → V) (hflip : Function.Involutive flip)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (F : (D → Bool) → ℝ) :
    (𝔼 g : D → V, F (fun d => χ (g d))) = 𝔼 b : D → Bool, F b := by
  classical
  have : Nonempty (FalseFiber χ) :=
    ⟨falseRepresentative χ flip hχ (Classical.choice ‹Nonempty V›)⟩
  calc
    (𝔼 g : D → V, F (fun d => χ (g d))) =
        𝔼 p : (D → Bool) × (D → FalseFiber χ), F p.1 := by
      apply Fintype.expect_equiv (sampleSplitEquiv χ flip hflip hχ)
      intro g
      rfl
    _ = 𝔼 b : D → Bool, F b := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

end DFVSGames.Foundations.PCP.CayleySampling

end

namespace DFVSGames.Foundations.PCP.CayleyTailCount

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def upperMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => 3 * m ≤ t.card

def lowerMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ m

def badMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  lowerMasks s m ∪ upperMasks s m

omit [DecidableEq α] in

theorem upperMasks_weight (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    (upperMasks s m).card * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by
  calc
    _ = ∑ _t ∈ upperMasks s m, 3 ^ (3 * m) := by simp
    _ ≤ ∑ t ∈ upperMasks s m, 3 ^ t.card := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.pow_le_pow_right (by decide) (Finset.mem_filter.mp ht).2
    _ ≤ ∑ t ∈ s.powerset, 3 ^ t.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro t _ _
        exact Nat.zero_le _
    _ = 4 ^ s.card := by
      simpa using Finset.sum_pow_mul_eq_add_pow (3 : ℕ) 1 s
    _ = 4 ^ (4 * m) := by rw [hcard]

theorem lowerMasks_complement_image (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).image (fun t => s \ t) = upperMasks s m := by
  ext u
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hts, htlo⟩ := Finset.mem_filter.mp ht
    have hsub := Finset.mem_powerset.mp hts
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  · intro hu
    obtain ⟨hus, huhi⟩ := Finset.mem_filter.mp hu
    have hsub := Finset.mem_powerset.mp hus
    apply Finset.mem_image.mpr
    refine ⟨s \ u, ?_, Finset.sdiff_sdiff_eq_self hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega

theorem lowerMasks_card_eq_upperMasks (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).card = (upperMasks s m).card := by
  have hinj : Set.InjOn (fun t : Finset α => s \ t) (lowerMasks s m) := by
    intro a ha b hb hab
    have has := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
    have hbs := Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1
    have h := congrArg (fun t : Finset α => s \ t) hab
    simpa only [Finset.sdiff_sdiff_eq_self has, Finset.sdiff_sdiff_eq_self hbs] using h
  calc
    _ = ((lowerMasks s m).image (fun t => s \ t)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = _ := congrArg Finset.card (lowerMasks_complement_image s m hcard)

theorem ratio_le_of_weight_inline_CayleyTailCount (c m : ℕ)
    (h : c * 3 ^ (3 * m) ≤ 4 ^ (4 * m)) :
    (c : ℝ) / 2 ^ (4 * m) ≤ (16 / 27 : ℝ) ^ m := by
  have hc : (c : ℝ) * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by exact_mod_cast h
  have h3 : 0 < (3 : ℝ) ^ (3 * m) := by positivity
  have h2 : 0 < (2 : ℝ) ^ (4 * m) := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ (4 * m) / 3 ^ (3 * m)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ h3).mpr hc) h2.le
    _ = _ := by
      rw [pow_mul, pow_mul, pow_mul, ← div_pow, ← div_pow]
      norm_num

omit [DecidableEq α] in
theorem upperMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((upperMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [hcard]
  exact ratio_le_of_weight_inline_CayleyTailCount _ m (upperMasks_weight s m hcard)

theorem lowerMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((lowerMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [lowerMasks_card_eq_upperMasks s m hcard]
  exact upperMasks_ratio_le s m hcard

theorem badMasks_ratio_le_sharp (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (16 / 27 : ℝ) ^ m := by
  have hc : ((badMasks s m).card : ℝ) ≤
      (lowerMasks s m).card + (upperMasks s m).card := by
    exact_mod_cast (Finset.card_union_le (lowerMasks s m) (upperMasks s m))
  have hpos : 0 < (2 : ℝ) ^ s.card := by positivity
  calc
    _ ≤ ((lowerMasks s m).card + (upperMasks s m).card : ℝ) / 2 ^ s.card :=
      div_le_div_of_nonneg_right hc hpos.le
    _ = ((lowerMasks s m).card : ℝ) / 2 ^ s.card +
        ((upperMasks s m).card : ℝ) / 2 ^ s.card := add_div _ _ _
    _ ≤ (16 / 27 : ℝ) ^ m + (16 / 27 : ℝ) ^ m :=
      add_le_add (lowerMasks_ratio_le s m hcard) (upperMasks_ratio_le s m hcard)
    _ = _ := by ring

theorem badMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (2 / 3 : ℝ) ^ m := by
  apply (badMasks_ratio_le_sharp s m hcard).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by norm_num)

section Words

variable {D : Type*} [Fintype D]

def trueMask (word : D → Bool) : Finset D :=
  Finset.univ.filter fun i => word i = true

def countTrue (word : D → Bool) : ℕ := (trueMask word).card

def badWord (m : ℕ) (word : D → Bool) : Prop :=
  countTrue word ≤ m ∨ 3 * m ≤ countTrue word

instance instDecidableBadWord (m : ℕ) (word : D → Bool) : Decidable (badWord m word) :=
  inferInstanceAs (Decidable (countTrue word ≤ m ∨ 3 * m ≤ countTrue word))

def wordMaskEquiv [DecidableEq D] : (D → Bool) ≃ Finset D where
  toFun := trueMask
  invFun s i := decide (i ∈ s)
  left_inv word := by
    funext i
    cases h : word i <;> simp [trueMask, h]
  right_inv s := by
    ext i
    simp [trueMask]

theorem twoTail_probability [DecidableEq D] (m : ℕ) (hcard : Fintype.card D = 4 * m) :
    (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) ≤
      2 * (2 / 3 : ℝ) ^ m := by
  classical
  have he : (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) =
      (𝔼 s : Finset D, if s.card ≤ m ∨ 3 * m ≤ s.card then (1 : ℝ) else 0) := by
    apply Finset.expect_equiv (wordMaskEquiv (D := D))
    · intro word
      simp
    · intro word _
      rfl
  have hs : (Finset.univ.filter fun s : Finset D => s.card ≤ m ∨ 3 * m ≤ s.card) =
      badMasks (Finset.univ : Finset D) m := by
    ext s
    simp [badMasks, lowerMasks, upperMasks]
  rw [he, Fintype.expect_eq_sum_div_card, Finset.sum_boole, hs, Fintype.card_finset]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Finset.card_univ] using
    badMasks_ratio_le (Finset.univ : Finset D) m (by simpa using hcard)

end Words

theorem union_bound_le_half (n m : ℕ) (hm : 3 * (n + 2) ≤ m) :
    (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) ≤ 1 / 2 := by
  have hpow : (2 / 3 : ℝ) ^ m ≤ (2 / 3 : ℝ) ^ (3 * (n + 2)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbase : (2 / 3 : ℝ) ^ (3 * (n + 2)) ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) (n + 2)
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hpow.trans hbase) (by norm_num)) (by positivity)
    _ = 1 / 2 := by
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num

end DFVSGames.Foundations.PCP.CayleyTailCount

namespace DFVSGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := Finset.univ.expect f

def energy {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := mean (fun x => (f x) ^ 2)

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_prod (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simpa only [mean, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

@[simp] theorem mean_const [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c :=
  Fintype.expect_const c

end Averages

end

end DFVSGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CayleySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace DFVSGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open DFVSGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def splitPortWord (n : Nat) : (Fin (n + 1) → D) ≃ D × (Fin n → D) where
  toFun p := (p 0, fun j => p j.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv p := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl


end DFVSGames.Foundations.PCP.CayleySpectral
end


noncomputable section

namespace DFVSGames.Foundations.PCP.Expanders

open scoped BigOperators
open DFVSGames.Foundations.Hastad
open CayleySpectral

def baseDimension : Nat := 448
def initialDegree : Nat := 2 ^ 16
def initialQuarterDegree : Nat := 2 ^ 14
def basePower : Nat := 7

abbrev BasePort := Fin basePower → Fin (4 * initialQuarterDegree)
def baseDegree : Nat := initialDegree ^ basePower

end DFVSGames.Foundations.PCP.Expanders
end


namespace DFVSGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

end DFVSGames.Foundations.PCP.ZigzagGraphs


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

abbrev Port := BasePort × BasePort
abbrev CloudPort := Port × Port
def growth : Nat := baseDegree ^ 4

theorem growth_gt_one : 1 < growth := by
  norm_num [growth, baseDegree, initialDegree, basePower]

def Vertex : Nat → Type
  | 0 => Unit
  | n + 1 => Vertex n × CloudPort

instance vertexFintype (n : Nat) : Fintype (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI : Fintype (Vertex n) := ih
    change Fintype (Vertex n × CloudPort)
    infer_instance

def level (k : Nat) : Nat := Nat.clog growth k

def size (k : Nat) : Nat := growth ^ level k

theorem le_size (k : Nat) : k ≤ size k := Nat.le_pow_clog growth_gt_one k

end DFVSGames.Foundations.PCP.ExpanderFamily


namespace DFVSGames.Foundations.PCP.CloudPadding

open scoped BigOperators

variable {V E A : Type*}

def paddedSize (k : Nat) : Nat := if k = 0 then 0 else ExpanderFamily.size k

@[simp] theorem paddedSize_zero : paddedSize 0 = 0 := rfl

theorem paddedSize_of_pos {k : Nat} (hk : 0 < k) :
    paddedSize k = ExpanderFamily.size k := by
  simp only [paddedSize, ite_eq_right (Nat.ne_of_gt hk)]

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, ite_eq_right hk]
    exact ExpanderFamily.le_size k


end DFVSGames.Foundations.PCP.CloudPadding


namespace DFVSGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables

def listEquiv {α : Type*} [BEq α] [LawfulBEq α] (xs : List α)
    (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) : α ≃ Fin xs.length where
  toFun a := ⟨xs.idxOf a, List.idxOf_lt_length_of_mem (complete a)⟩
  invFun i := xs.get i
  left_inv a := List.idxOf_get _
  right_inv i := by
    apply Fin.ext
    exact List.get_idxOf nodup i

@[simp] theorem listEquiv_val {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) (a : α) :
    (listEquiv xs nodup complete a).val = xs.idxOf a := rfl

@[simp] theorem listEquiv_symm_apply {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs)
    (i : Fin xs.length) : (listEquiv xs nodup complete).symm i = xs.get i := rfl

end DFVSGames.Foundations.PCP.PreprocessingCloudIndex


namespace DFVSGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def vertexCount (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => vertexCount q n * (q * q)

end DFVSGames.Foundations.PCP.ExpanderTables


namespace DFVSGames.Foundations.PCP.PreprocessingLevels

def levelLoop (g k : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, e, s => (e, s)
  | fuel + 1, e, s =>
      if k ≤ s then (e, s)
      else levelLoop g k fuel (e + 1) (s * g)

def searchResult (k : Nat) : Nat × Nat :=
  levelLoop ExpanderFamily.growth k k 0 1

def boundedLevel (k : Nat) : Nat := (searchResult k).1

def paddedSize (k : Nat) : Nat := (searchResult k).2

end DFVSGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PreprocessingRegularTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks

def paddingList {n : Nat} (padding : Fin n → Nat) :
    List (Σ v : Fin n, Fin (padding v)) :=
  (List.finRange n).sigma (fun v => List.finRange (padding v))

theorem paddingList_nodup {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).Nodup :=
  (List.nodup_finRange n).sigma (fun v => List.nodup_finRange (padding v))

theorem mem_paddingList {n : Nat} (padding : Fin n → Nat)
    (z : Σ v : Fin n, Fin (padding v)) : z ∈ paddingList padding := by
  rcases z with ⟨v, k⟩
  simp only [paddingList, List.mem_sigma, List.mem_finRange, and_self]

def paddingListOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (paddingList padding).length :=
  PreprocessingCloudIndex.listEquiv (paddingList padding)
    (paddingList_nodup padding) (mem_paddingList padding)

theorem paddingList_length {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).length = ∑ v, padding v := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    (Fintype.card_congr (paddingListOrder padding)).symm

def paddingOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (∑ v, padding v) :=
  (paddingListOrder padding).trans (finCongr (paddingList_length padding))

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := ⟨0, Nat.zero_lt_one⟩
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv k := Subsingleton.elim _ _

def portOrder (q : Nat) : (Fin q ⊕ Unit) ≃ Fin (q + 1) :=
  (Equiv.sumCongr (Equiv.refl _) unitOrder).trans finSumFinEquiv

end DFVSGames.Foundations.PCP.PreprocessingRegularTables


namespace DFVSGames.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

def extendLabeling (extra : ℕ) (defaultA : A) (labeling : V → A) : V ⊕ Fin extra → A :=
  Sum.elim labeling (fun _ => defaultA)


variable (V : Type*) [Fintype V]

def extraVertices : ℕ := ExpanderFamily.size (Fintype.card V) - Fintype.card V

abbrev Vertex := V ⊕ Fin (extraVertices V)

theorem card_vertex : Fintype.card (Vertex V) = ExpanderFamily.size (Fintype.card V) := by
  rw [Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_sub_of_le (ExpanderFamily.le_size _)


end DFVSGames.Foundations.PCP.VertexPadding


namespace DFVSGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

def vertexEquiv (h : n ≤ m) : Fin n ⊕ Fin (m - n) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

end DFVSGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open DFVSGames.Foundations.PCP

inductive Label
  | init | fuelFirst | fuelSecond | guard | copyFirst | copySecond
  | compare | restore | decide | scale | transfer | cleanup
  deriving DecidableEq

instance instFintypeLabel : Fintype Label := derive_fintype% Label

abbrev State (σ : Type) := (σ × Bool) × Option Bool

end DFVSGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.PreprocessingPaddingOffsets

open PreprocessingRegularTables
open scoped BigOperators

theorem idxOf_map_injective_inline_PreprocessingPaddingOffsets {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = a
    · subst x; simp
    · simp [List.idxOf_cons_ne, h, hf.ne h, ih]

theorem sigma_idxOf {A : Type*} [DecidableEq A] (sizes : A → Nat)
    (xs : List A) (a : A) (ha : a ∈ xs) (j : Fin (sizes a)) :
    (xs.sigma (fun x => List.finRange (sizes x))).idxOf ⟨a, j⟩ =
      ((xs.take (xs.idxOf a)).map sizes).sum + j.val := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.sigma_cons]
    by_cases h : x = a
    · subst x
      have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∈
          (List.finRange (sizes a)).map (Sigma.mk a) := by
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
      rw [List.idxOf_append_of_mem hm,
        idxOf_map_injective_inline_PreprocessingPaddingOffsets (Sigma.mk a) (fun x y h => by cases h; rfl),
        List.idxOf_finRange]
      simp
    · have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∉
          (List.finRange (sizes x)).map (Sigma.mk x) := by
        intro hm
        rcases List.mem_map.mp hm with ⟨k, _, hk⟩
        exact h (congrArg Sigma.fst hk)
      rw [List.idxOf_append_of_notMem hm, List.length_map, List.length_finRange,
        ih (List.mem_of_ne_of_mem (Ne.symm h) ha), List.idxOf_cons_ne xs h]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

def offset {n : Nat} (padding : Fin n → Nat) (k : Nat) : Nat :=
  (((List.finRange n).take k).map padding).sum

@[simp] theorem offset_zero {n : Nat} (padding : Fin n → Nat) : offset padding 0 = 0 := by
  simp [offset]

end DFVSGames.Foundations.PCP.PreprocessingPaddingOffsets

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PreprocessingOverlayTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

def overlayPorts (d e : Nat) : (Fin d ⊕ Fin e) ≃ Fin (d + e) := finSumFinEquiv

@[simp] theorem overlayPorts_inl_val (d e : Nat) (i : Fin d) :
    (overlayPorts d e (Sum.inl i)).val = i.val := rfl

@[simp] theorem overlayPorts_inr_val (d e : Nat) (i : Fin e) :
    (overlayPorts d e (Sum.inr i)).val = d + i.val := rfl

def lazyPorts (d : Nat) : (Bool × Fin d) ≃ Fin (2 * d) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin d))).trans finProdFinEquiv

@[simp] theorem lazyPorts_false_val (d : Nat) (i : Fin d) :
    (lazyPorts d (false, i)).val = i.val := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

@[simp] theorem lazyPorts_true_val (d : Nat) (i : Fin d) :
    (lazyPorts d (true, i)).val = i.val + d := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

end DFVSGames.Foundations.PCP.PreprocessingOverlayTables


noncomputable section

namespace DFVSGames.Foundations.PCP.Regularization

open PoweringWalks

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

abbrev Port := ExpanderFamily.Port ⊕ Unit

end DFVSGames.Foundations.PCP.Regularization

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Preprocessing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

abbrev PortWords (D : Type*) (t : Nat) := (n : Fin (t + 1)) × (Fin n.val → D)

abbrev PaddedLabel (D : Type*) (t : Nat) (A : Type*) := PortWords D t → A

end DFVSGames.Foundations.PCP.PoweringLabels

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PoweringAddresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.PoweringAddresses

open PoweringWalks PoweringLabels
open scoped BigOperators

variable {V : Type*}

def allWords (d : Nat) : (n : Nat) → List (Fin n → Fin d)
  | 0 => [Fin.elim0]
  | n + 1 => (List.finRange d).flatMap fun a =>
      (allWords d n).map fun p => Fin.cases a p

theorem mem_allWords (d : Nat) :
    ∀ n (p : Fin n → Fin d), p ∈ allWords d n := by
  intro n
  induction n with
  | zero =>
    intro p
    simp only [allWords, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro p
    simp only [allWords, List.mem_flatMap, List.mem_map]
    refine ⟨p 0, List.mem_finRange (p 0), (fun j => p j.succ), ih _, ?_⟩
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

def allAddresses (d t : Nat) : List (PortWords (Fin d) t) :=
  (List.finRange (t + 1)).flatMap fun n =>
    (allWords d n.val).map fun p => Sigma.mk n p

theorem mem_allAddresses (d t : Nat) (w : PortWords (Fin d) t) :
    w ∈ allAddresses d t := by
  rcases w with ⟨n, p⟩
  unfold allAddresses
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_finRange n, ?_⟩
  exact List.mem_map.mpr ⟨p, mem_allWords d n.val p, rfl⟩

end DFVSGames.Foundations.PCP.PoweringAddresses

namespace DFVSGames.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

def addressCount (d t : Nat) : Nat := ∑ i : Fin (t + 1), d ^ i.val

def reverseWordEquiv (d n : Nat) : (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun p i := p i.rev
  invFun p i := p i.rev
  left_inv p := by funext i; simp only [Fin.rev_rev]
  right_inv p := by funext i; simp only [Fin.rev_rev]

def wordEquiv (d n : Nat) : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (reverseWordEquiv d n).trans finFunctionFinEquiv

def addressEquiv (d t : Nat) : PortWords (Fin d) t ≃ Fin (addressCount d t) :=
  (Equiv.sigmaCongrRight (fun i : Fin (t + 1) => wordEquiv d i.val)).trans
    finSigmaFinEquiv

def paddedLabelEquiv (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) ≃ Fin (q ^ addressCount d t) :=
  ((addressEquiv d t).arrowCongr (Equiv.refl (Fin q))).trans
    (wordEquiv q (addressCount d t))

def orientationEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem orientationEquiv_false : orientationEquiv false = 0 := rfl
@[simp] theorem orientationEquiv_true : orientationEquiv true = 1 := rfl

def dartBlockEquiv (d n : Nat) :
    ((Fin (n + 1) → Fin d) × Bool) ≃ Fin (2 * d ^ (n + 1)) :=
  ((wordEquiv d (n + 1)).prodCongr orientationEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm (d ^ (n + 1)) 2)))

def dartVertexEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      (Fin vertices × ((Fin (n + 1) → Fin d) × Bool)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv x := by rcases x with ⟨b, v, p⟩; rfl
  right_inv x := by rcases x with ⟨v, p, b⟩; rfl

def dartEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      Fin (2 * vertices * d ^ (n + 1)) :=
  (dartVertexEquiv vertices d n).trans
    (((Equiv.refl (Fin vertices)).prodCongr (dartBlockEquiv d n)).trans
      (finProdFinEquiv.trans
        (finCongr (show vertices * (2 * d ^ (n + 1)) =
          2 * vertices * d ^ (n + 1) by ac_rfl))))

def decodeWord (d n : Nat) : Fin (d ^ n) → (Fin n → Fin d) := (wordEquiv d n).symm

def encodeAddress (d t : Nat) : PortWords (Fin d) t → Fin (addressCount d t) :=
  addressEquiv d t

def encodeLabel (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) → Fin (q ^ addressCount d t) := paddedLabelEquiv d t q

def decodeLabel (d t q : Nat) :
    Fin (q ^ addressCount d t) → PaddedLabel (Fin d) t (Fin q) :=
  (paddedLabelEquiv d t q).symm

@[simp] theorem decodeLabel_encodeLabel (d t q : Nat) (a : PaddedLabel (Fin d) t (Fin q)) :
    decodeLabel d t q (encodeLabel d t q a) = a := (paddedLabelEquiv d t q).symm_apply_apply a

@[simp] theorem encodeLabel_decodeLabel (d t q : Nat) (i : Fin (q ^ addressCount d t)) :
    encodeLabel d t q (decodeLabel d t q i) = i := (paddedLabelEquiv d t q).apply_symm_apply i

@[simp] theorem decodeLabel_apply (d t q : Nat) (i : Fin (q ^ addressCount d t))
    (w : PortWords (Fin d) t) :
    decodeLabel d t q i w = decodeWord q (addressCount d t) i (encodeAddress d t w) := rfl

end DFVSGames.Foundations.PCP.PoweringEnumeration

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PoweringReach
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses
open scoped BigOperators

variable {X A : Type*}

theorem match_in_tail_inline_PoweringOpinionTables (p : X → Prop) {a : X} {xs : List X}
    (h : ∃ b ∈ a :: xs, p b) (ha : ¬p a) : ∃ b ∈ xs, p b := by
  obtain ⟨b, hb, hp⟩ := h
  rcases List.mem_cons.mp hb with he | hm
  · exact False.elim (ha (he ▸ hp))
  · exact ⟨b, hm, hp⟩

abbrev AddressIndex (d t : Nat) := Fin (allAddresses d t).length

variable {vertices d : Nat}

abbrev LabelTable (d t : Nat) (A : Type*) := Vector A (allAddresses d t).length

end DFVSGames.Foundations.PCP.PoweringOpinionTables

namespace DFVSGames.Foundations.PCP.GenericGraphTables

open DFVSGames.Foundations.Complexity

abbrev Label (q : Nat) := Fin q
abbrev RelationTable (q : Nat) := Vector Bool (q * q)

variable {q : Nat}

def relationIndex (q : Nat) : (Label q) × (Label q) ≃ Fin (q * q) := finProdFinEquiv

def relationAt (table : (RelationTable q)) (a b : (Label q)) : Bool :=
  table[(relationIndex q) (a, b)]

def relationOf (predicate : (Label q) → (Label q) → Bool) : (RelationTable q) :=
  Vector.ofFn (fun i => predicate ((relationIndex q).symm i).1 ((relationIndex q).symm i).2)

structure DartRow (q vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : (RelationTable q)

abbrev Rows (q vertices darts : Nat) := Vector (DartRow q vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows q n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def bitWord (b : Bool) : Nat := if b then 1 else 0

def relationWords (relation : (RelationTable q)) : List Nat := relation.toList.map bitWord

end DFVSGames.Foundations.PCP.GenericGraphTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PoweringTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

def labelCount (d n : Nat) : Nat := 64 ^ addressCount d (n + 1)

def dartCount (vertices d n : Nat) : Nat := 2 * vertices * d ^ (n + 1)

end DFVSGames.Foundations.PCP.PoweringTables


namespace DFVSGames.Foundations.PCP.QueryIncidence

structure Verifier (E X : Type*) (q : Nat) where
  query : E → Fin q → X
  accepts : E → (Fin q → Bool) → Bool

abbrev Label (q : Nat) := Fin q → Bool
abbrev Vertex (E X : Type*) := E ⊕ X
abbrev Dart (E : Type*) (q : Nat) := (E × Fin q) × Bool

variable {E X : Type*} {q : Nat}

def zeroSlot (positive : 0 < q) : Fin q := ⟨0, positive⟩

def decodeRight (positive : 0 < q) (label : Label q) : Bool := label (zeroSlot positive)

def encodeRight (bit : Bool) : Label q := fun _ => bit

def canonicalSlot [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) : Fin q :=
  Fin.find (fun j => T.query event j = T.query event i) ⟨i, rfl⟩

def RepeatedConsistent (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  ∀ i j, T.query event i = T.query event j → label i = label j

instance repeatedConsistentDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (RepeatedConsistent T event label) := by
  unfold RepeatedConsistent
  infer_instance

def LeftValid (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  T.accepts event label = true ∧ RepeatedConsistent T event label

instance leftValidDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (LeftValid T event label) := by
  unfold LeftValid
  infer_instance

def reverse : Dart E q → Dart E q := fun d => (d.1, !d.2)

theorem reverse_involutive : Function.Involutive (reverse : Dart E q → Dart E q) := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  cases orientation <;> rfl

def reverseEquiv : Dart E q ≃ Dart E q where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_involutive
  right_inv := reverse_involutive

def tail (T : Verifier E X q) : Dart E q → Vertex E X
  | ((event, _), false) => .inl event
  | ((event, slot), true) => .inr (T.query event slot)

end DFVSGames.Foundations.PCP.QueryIncidence


noncomputable section

namespace DFVSGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open DFVSGames.Foundations.Hastad

def pairWord {X : Type*} (left right : X → Bool) : Bool × X → Bool :=
  fun p => if p.1 then right p.2 else left p.2

end DFVSGames.Foundations.PCP.CodeComposition
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AlphabetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace DFVSGames.Foundations.PCP.AlphabetReduction

open DFVSGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev LegalPair (accepts : A → A → Bool) :=
  {p : A × A // accepts p.1 p.2 = true}

end DFVSGames.Foundations.PCP.AlphabetReduction
end


namespace DFVSGames.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

def restrict (f : B → Bool) : {b // p b} → Bool := fun b => f b.1

variable [DecidablePred p]

def extend (g : {b // p b} → Bool) : B → Bool :=
  fun b => if hb : p b then g ⟨b, hb⟩ else false

omit [DecidablePred p] in
@[simp] theorem restrict_apply (f : B → Bool) (b : {b // p b}) :
    restrict p f b = f b.1 := rfl

@[simp] theorem extend_apply_of_mem (g : {b // p b} → Bool) (b : B) (hb : p b) :
    extend p g b = g ⟨b, hb⟩ := by
  simp [extend, hb]

@[simp] theorem extend_apply_of_not_mem (g : {b // p b} → Bool) (b : B)
    (hb : ¬ p b) : extend p g b = false := by
  simp [extend, hb]

@[simp] theorem restrict_extend (g : {b // p b} → Bool) :
    restrict p (extend p g) = g := by
  funext b
  simp [restrict, extend, b.property]


end DFVSGames.Foundations.PCP.UniformRestriction


namespace DFVSGames.Foundations.PCP.AlphabetTable.Enumeration

open DFVSGames.Foundations.Hastad
open scoped BigOperators

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def boolEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

def productEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A × B ≃ Fin (a * b) :=
  (Equiv.prodCongr left right).trans finProdFinEquiv

def sumEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) :=
  (Equiv.sumCongr left right).trans finSumFinEquiv

def tapeCount (q : Nat) : Nat := 2 ^ q
def pairTapeCount (q : Nat) : Nat := 2 ^ (q * q)
def fiveTapeCount (q : Nat) : Nat := pairTapeCount q ^ 5
def localCount (q : Nat) : Nat := 4 * (2 * tapeCount q) * fiveTapeCount q
def eventCount (m q : Nat) : Nat := m * localCount q
def addressCount (n m q : Nat) : Nat := n * tapeCount q + m * pairTapeCount q
def vertexCount (n m q : Nat) : Nat := eventCount m q + addressCount n m q
def dartCount (m q : Nat) : Nat := eventCount m q * 12

def pairIndex (q : Nat) : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv

def ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) : List A :=
  List.ofFn order.symm

end DFVSGames.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_VerifierCNF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.VerifierToCNF

abbrev BoolTriple := Bool × Bool × Bool

def tripleValue (t : BoolTriple) : Bool := (t.1 || t.2.1) || t.2.2

def chainView : List Bool → List Bool → List BoolTriple
  | [a, b, c], [] => [(a, b, c)]
  | a :: b :: rest, y :: ys => (a, b, y) :: chainView ((!y) :: rest) ys
  | _, _ => []

def fillBits (bits : List Bool) : List Bool :=
  match bits with
  | a :: b :: c :: d :: rest =>
      (!(a || b)) :: fillBits ((a || b) :: c :: d :: rest)
  | _ => []
termination_by bits.length
decreasing_by simp_wf

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_length ((a || b) :: c :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: c :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

abbrev Pattern (q : Nat) := Fin q → Bool

def patterns : (q : Nat) → List (Pattern q)
  | 0 => [Fin.elim0]
  | q + 1 => (patterns q).flatMap (fun p => [Fin.cases false p, Fin.cases true p])

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem patterns_length (q : Nat) : (patterns q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [patterns, flatMap_pair_length, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

abbrev PatternIndex (q : Nat) := Fin (patterns q).length
def patternAt (q : Nat) (p : PatternIndex q) : Pattern q := (patterns q)[p.val]

structure FiniteVerifier (q : Nat) where
  «variables» : Nat
  events : Nat
  query : Fin events → Fin q → Fin «variables»
  accepts : Fin events → Pattern q → Bool

def auxiliaryCount {q : Nat} (V : FiniteVerifier q) : Nat :=
  V.events * (patterns q).length * (q - 3)

def outputVariables {q : Nat} (V : FiniteVerifier q) : Nat := V.«variables» + auxiliaryCount V

def oldIndex {q : Nat} (V : FiniteVerifier q) (v : Fin V.«variables») : Fin (outputVariables V) :=
  Fin.castAdd (auxiliaryCount V) v

def freshIndex {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) : Fin (outputVariables V) :=
  Fin.natAdd V.«variables» (finProdFinEquiv (finProdFinEquiv (e, p), j))

def auxiliaryNames {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Fin (outputVariables V)) :=
  List.ofFn (freshIndex V e p)

def restrictAssignment {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) : Fin V.«variables» → Bool :=
  fun v => B (oldIndex V v)

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

theorem twelve_query_factor : 2 ^ 12 * (12 - 2) = 40960 := by decide

end DFVSGames.Foundations.PCP.VerifierToCNF

namespace DFVSGames.Foundations.PCP.FinalBooleanVerifier

abbrev Label := Fin 6 → Bool

variable {V E : Type*} {n m : Nat}

def bitIndex (vertices : V ≃ Fin n) (v : V) (j : Fin 6) : Fin (n * 6) :=
  finProdFinEquiv (vertices v, j)

def labelsOfBits (vertices : V ≃ Fin n) (assignment : Fin (n * 6) → Bool) : V → Label :=
  fun v j => assignment (bitIndex vertices v j)

def bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) : Fin (n * 6) → Bool :=
  fun k =>
    let pair : Fin n × Fin 6 := finProdFinEquiv.symm k
    labeling (vertices.symm pair.1) pair.2

@[simp] theorem labelsOfBits_bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) :
    labelsOfBits vertices (bitsOfLabels vertices labeling) = labeling := by
  funext v j
  simp only [labelsOfBits, bitsOfLabels, bitIndex, Equiv.symm_apply_apply]

theorem twelve_query_auxiliary_factor : 2 ^ 12 * (12 - 3) = 36864 := by decide

end DFVSGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Queries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.AlphabetTable.Relations

open Hastad

variable {q : Nat}

def oldPredicate (old : Vector Bool (q * q)) (a b : Fin q) : Bool :=
  old[(finProdFinEquiv (a, b) : Fin (q * q))]


end DFVSGames.Foundations.PCP.AlphabetTable.Relations


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_InitialGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.InitialGraph

abbrev Label := Bool × Bool × Bool
@[simp] theorem card_label : Fintype.card Label = 8 := by
  simp [Label, Fintype.card_prod]

def variableValid (label : Label) : Bool :=
  decide (label.2.1 = false ∧ label.2.2 = false)

end DFVSGames.Foundations.PCP.InitialGraph

namespace DFVSGames.Foundations.PCP.RawInitialTables

open GraphTables

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

end DFVSGames.Foundations.PCP.RawInitialTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_FinalCNFPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev Label := FinalBooleanVerifier.Label

def leftHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.castAdd 6 j)

def rightHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.natAdd 6 j)

end DFVSGames.Foundations.Complexity.FinalCNFPattern

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Setup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.Setup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

abbrev Ports (K : Type) := Fin 7 → K

inductive Label
  | copyFirst | copySecond | verticesStart | verticesLoop
  | dartsStart | dartsLoop | counterFirst | counterSecond | initialize_
  deriving DecidableEq

instance instFintypeLabel : Fintype Label where
  elems := {.copyFirst, .copySecond, .verticesStart, .verticesLoop,
    .dartsStart, .dartsLoop, .counterFirst, .counterSecond, .initialize_}
  complete label := by cases label <;> simp

end DFVSGames.Foundations.PCP.AlphabetTable.Setup

namespace DFVSGames.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open DFVSGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

abbrev Alphabet (_ : K) := Bool

end DFVSGames.Foundations.PCP.AlphabetTable.ReadRelation

namespace DFVSGames.Foundations.Complexity.MachineFixedBlockMap

open Turing

abbrev Buffer (N : Nat) := Fin N → Bool

def emptyBuffer (N : Nat) : Buffer N := fun _ => false

section Chains

variable {K Λ σ : Type} {N : Nat}

def fill (slots : List (Fin N)) (bits buffer : Buffer N) : Buffer N :=
  slots.foldl (fun buffer i => Function.update buffer i (bits i)) buffer

theorem fill_apply (slots : List (Fin N)) (bits buffer : Buffer N) (i : Fin N) :
    fill slots bits buffer i = if i ∈ slots then bits i else buffer i := by
  induction slots generalizing buffer with
  | nil => simp [fill]
  | cons j slots ih =>
      change fill slots bits (Function.update buffer j (bits j)) i = _
      rw [ih]
      by_cases hm : i ∈ slots
      · simp [hm]
      · by_cases he : i = j <;> simp [hm, he]

@[simp] theorem fill_all (bits buffer : Buffer N) :
    fill (List.ofFn id) bits buffer = bits := by
  funext i
  simp [fill_apply, List.mem_ofFn]

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

def finishAt (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

end Block

end DFVSGames.Foundations.Complexity.MachineFixedBlockMap

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Lookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def skipBits (source : K) : Nat →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, next => .load (fun state => (state.1, none)) next
  | count + 1, next =>
      let rest := skipBits source count next
      .pop source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop source (fun state _ => (state.1, none)) rest)
          (.load (fun state => (state.1, none)) rest))

inductive Label
  | guard | skipTail | skipReverse | skipPredicate | select | copy
  deriving DecidableEq

instance instFintypeLabel : Fintype Label where
  elems := {.guard, .skipTail, .skipReverse, .skipPredicate, .select, .copy}
  complete label := by cases label <;> simp

abbrev HeadTapes (K : Type) := Fin 6 → K

end DFVSGames.Foundations.PCP.AlphabetTable.Lookup

namespace DFVSGames.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open DFVSGames.Foundations.Complexity

inductive Tape
  | original | cursor | scan | vertices | darts | counter | edge
  | tail | reverseIndex | head | scratch | indexScan
  | compareLeft | compareRight | reversed | output
  deriving DecidableEq

abbrev Alphabet (_ : Tape) := Bool

abbrev Flags := Bool × Bool × Option Bool

def setupPorts : Fin 7 → Tape :=
  ![.original, .cursor, .vertices, .darts, .counter, .scratch, .edge]

def rowSources : Fin 5 → Tape := ![.vertices, .darts, .edge, .tail, .head]
def headerSources : Fin 2 → Tape := ![.vertices, .darts]
def fieldPorts : Fin 3 → Tape := ![.tail, .reverseIndex, .head]

def cleanupPorts : Fin 15 → Tape :=
  ![.original, .cursor, .scan, .vertices, .darts, .counter, .edge,
    .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight, .reversed]

end DFVSGames.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_CompareLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open DFVSGames.Foundations.Complexity
open RuntimeModel

inductive Label
  | leftFirst | leftSecond | rightFirst | rightSecond | compare
  | equalStore | differentStore
  deriving DecidableEq

instance instFintypeLabel : Fintype Label where
  elems := {.leftFirst, .leftSecond, .rightFirst, .rightSecond, .compare,
    .equalStore, .differentStore}
  complete label := by cases label <;> simp

end DFVSGames.Foundations.PCP.AlphabetTable.CompareLoop

namespace DFVSGames.Foundations.PCP.AlphabetTable.Emitter

open Turing
open DFVSGames.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

inductive Command (h : Nat) (σ : Type) (bound : Nat)
  | literal (word : List Bool)
  | bit (value : σ → Bool)
  | bounded (value : σ → Fin bound)
  | scaled (source : Fin h) (coefficient : Nat)
  | scaledIf (source : Fin h) (coefficient : Nat) (active : σ → Bool)

inductive Phase (bound : Nat)
  | entry | emit (symbol : Bool) | restore | offset (value : Fin bound)
  | scanIf (active : Bool) | emitIf (active symbol : Bool)
  deriving DecidableEq, Fintype

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (coefficient : Nat) (_ : Unit) (symbol : Bool) : List Bool :=
  if symbol then List.replicate coefficient true else []

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

abbrev Label (count bound : Nat) := Fin (count + 1) × Phase bound

def labelAt (count bound r : Nat) (phase : Phase bound) : Label count bound :=
  (⟨min r count, by omega⟩, phase)

def commandAt {count : Nat} (commands : Fin count → Command h σ bound) (r : Nat) :
    Command h σ bound :=
  if hr : r < count then commands ⟨r, hr⟩ else .literal []

def listCommands (commands : List (Command h σ bound)) :
    Fin commands.length → Command h σ bound := fun i => commands[i]

def affineCommands (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    List (Command h σ bound) :=
  terms.map (fun term => .scaled term.1 term.2) ++ [.bounded offset, .literal [false]]

@[simp] theorem affineCommands_length (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    (affineCommands terms offset).length = terms.length + 2 := by
  simp [affineCommands]

def bitCommands (bits : List (σ → Bool)) : List (Command h σ bound) := bits.map .bit

end DFVSGames.Foundations.PCP.AlphabetTable.Emitter

namespace DFVSGames.Foundations.PCP.AlphabetTable.Addresses

open DFVSGames.Foundations.Hastad
open Enumeration

abbrev Terms := List (Fin 5 × Nat)

structure Field (bound : Nat) where
  terms : Terms
  offset : Fin bound

end DFVSGames.Foundations.PCP.AlphabetTable.Addresses

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_EmitRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open DFVSGames.Foundations.Complexity
open Emitter

abbrev Context (q : Nat) := Vector Bool (q * q) × Bool

end DFVSGames.Foundations.PCP.AlphabetTable.EmitRows


namespace DFVSGames.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (initial : σ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun _ => (initial, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

end DFVSGames.Foundations.PCP.AlphabetTable.Cleanup


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineStateEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

abbrev statement (e : σ ≃ τ) : Stmt Γ Λ σ → Stmt Γ Λ τ :=
  MachineControl.statement (id : Λ → Λ) e

@[simp] theorem statement_symm_statement (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    statement e.symm (statement e q) = q := by
  induction q <;>
    simp_all only [statement, MachineControl.statement, Equiv.symm_symm,
      Equiv.symm_apply_apply, id_eq]

def configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) : Cfg Γ Λ τ :=
  ⟨c.l, e c.var, c.stk⟩

@[simp] theorem configuration_label (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).l = c.l := rfl

@[simp] theorem configuration_state (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).var = e c.var := rfl

@[simp] theorem configuration_tapes (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).stk = c.stk := rfl

@[simp] theorem configuration_symm_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configuration e.symm (configuration e c) = c := by
  cases c
  simp only [configuration, Equiv.symm_apply_apply]

@[simp] theorem configuration_configuration_symm (e : σ ≃ τ) (c : Cfg Γ Λ τ) :
    configuration e (configuration e.symm c) = c := by
  cases c
  simp only [configuration, Equiv.apply_symm_apply]

def configurationEquiv (e : σ ≃ τ) : Cfg Γ Λ σ ≃ Cfg Γ Λ τ where
  toFun := configuration e
  invFun := configuration e.symm
  left_inv := configuration_symm_configuration e
  right_inv := configuration_configuration_symm e

@[simp] theorem configurationEquiv_apply (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configurationEquiv e c = configuration e c := rfl

@[simp] theorem control_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    MachineControl.configuration (id : Λ → Λ) e c = configuration e c := by
  cases c
  simp [MachineControl.configuration, configuration]

def program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Γ Λ τ :=
  fun l => statement e (source l)

@[simp] theorem program_symm_program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) :
    program e.symm (program e source) = source := by
  funext l
  exact statement_symm_statement e (source l)

variable [DecidableEq K]

theorem stepAux_transport (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) (e state) tapes =
      configuration e (stepAux q state tapes) := by
  simpa only [statement, control_configuration] using
    MachineControl.stepAux_simulation (id : Λ → Λ) e q state tapes

theorem step_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program e source) (configuration e c) =
      (step source c).map (configuration e) := by
  cases c with
  | mk l state tapes =>
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (statement e (source l)) (e state) tapes) = _
          rw [stepAux_transport]
          rfl

end DFVSGames.Foundations.Complexity.MachineStateEquiv

namespace DFVSGames.Foundations.Complexity.MachineUnaryEqualityBit

open Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

inductive Label
  | seedLeft | scanLeft | restoreLeft
  | seedRight | scanRight | restoreRight
  | compare | equal | different
  deriving DecidableEq

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def emit (destination : K) (bit : Bool) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (if bit then .push destination (fun _ => true) (exitAt exit) else exitAt exit)

end DFVSGames.Foundations.Complexity.MachineUnaryEqualityBit

namespace DFVSGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open DFVSGames.Foundations.PCP

def inputSize (t S : Nat) : Nat := t * (4096 + (S + S))

def firstMatch {S : Nat} (mask : Fin S → Bool) : Option (Fin S) :=
  (List.ofFn id).find? mask

end DFVSGames.Foundations.Complexity.PoweringMachineRow

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePreservingLookupClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end DFVSGames.Foundations.Complexity.MachinePreservingLookupClean


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ExpanderTableWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineFixedDivMod

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord )

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) (d : Nat) := (σ × Fin d) × Option Bool

def residue (d : Nat) (positive : 0 < d) (n : Nat) : Fin d :=
  ⟨n % d, Nat.mod_lt n positive⟩

def nextResidue (d : Nat) (positive : 0 < d) (r : Fin d) : Fin d :=
  residue d positive (r.val + 1)

def scanLoop (d : Nat) (positive : 0 < d) (source quotient : K)
    (scanLabel : Λ) (emitterLabel : Fin d → Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.branch (fun state => decide ((nextResidue d positive state.1.2).val = 0))
        (.push quotient (fun _ => true)
          (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
            (.goto fun _ => scanLabel)))
        (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
          (.goto fun _ => scanLabel)))
      (.push source (fun _ => false) (.goto fun state => emitterLabel state.1.2)))

end DFVSGames.Foundations.Complexity.MachineFixedDivMod

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRowDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables

inductive ExtraTape
  | vertexCount | result
  deriving DecidableEq

instance instFintypeExtraTape : Fintype ExtraTape := derive_fintype% ExtraTape

inductive OuterLabel
  | initialize_ | vertexGuard | prepareRow | afterRow | reverseOutput | done
  deriving DecidableEq

instance instFintypeOuterLabel : Fintype OuterLabel := derive_fintype% OuterLabel

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineAlphabetTransport

open Turing.TM2

variable {K Λ σ : Type} {Γ Δ : K → Type}

def tapes (h : Γ = Δ) (source : ∀ k, List (Γ k)) : ∀ k, List (Δ k) := h ▸ source

def statement (h : Γ = Δ) (source : Stmt Γ Λ σ) : Stmt Δ Λ σ := h ▸ source

def configuration (h : Γ = Δ) (source : Cfg Γ Λ σ) : Cfg Δ Λ σ := h ▸ source

def program (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Δ Λ σ :=
  fun label => statement h (source label)

end DFVSGames.Foundations.Complexity.MachineAlphabetTransport

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables

inductive ExtraTape
  | remainingLevel | currentSize | unaryScratch | tableReverse
  deriving DecidableEq

instance instFintypeExtraTape : Fintype ExtraTape := derive_fintype% ExtraTape

inductive AffinePhase
  | copyCount | multiplySize
  deriving DecidableEq

instance instFintypeAffinePhase : Fintype AffinePhase := derive_fintype% AffinePhase

inductive AffineLabel
  | seed | scan | restore
  deriving DecidableEq

instance instFintypeAffineLabel : Fintype AffineLabel := derive_fintype% AffineLabel

inductive OuterLabel
  | initialize_
  | levelGuard
  | affine (phase : AffinePhase) (label : AffineLabel)
  | clearOldTable | reverseResult | reverseTable | clearCurrentSize
  | drainInputVertex | drainVertexCount | done
  deriving DecidableEq, Fintype

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables
open DFVSGames.Foundations.Complexity

variable {v d : Nat}

theorem ofFn_cast_inline_ExpanderTableEnumeration {α : Type*} {n m : Nat} (h : n = m) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast h i)) = List.ofFn f := by
  cases h
  rfl

end DFVSGames.Foundations.PCP.ExpanderTableEnumeration

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderFamilyLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open PCP.ExpanderTables

abbrev fixedDegree := PCP.Expanders.baseDegree

end DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePaddedExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition

abbrev CoreTape := Fin 27

end DFVSGames.Foundations.Complexity.MachineRegularFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (slots 0) left) (slots 1) right) (slots 2) savedLeft) (slots 3) savedRight

end DFVSGames.Foundations.Complexity.MachineUnaryLessAt
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineRegularOriginalBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

variable {LabelType : Type}

def sumDecidableEq_inline_MachineRegularOwnerCleanup {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

end DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PreprocessingStageMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineTableSplit

open Turing MachineComposition

abbrev Tape := Fin 5

def tapes (original work vertices darts : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then original else if k = 1 then work
    else if k = 3 then vertices else if k = 4 then darts else []

end DFVSGames.Foundations.Complexity.MachineTableSplit

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_GraphCounterFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.PCPIterationMachine

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool
abbrev Labels (Λ : Type) := Bool ⊕ Λ

end DFVSGames.Foundations.Complexity.PCPIterationMachine

namespace DFVSGames.Foundations.PCP.RawInitialRows

open GraphTables RawInitialTables

abbrev Signs := Bool × Bool × Bool
abbrev Names := Nat × Nat × Nat

end DFVSGames.Foundations.PCP.RawInitialRows

namespace DFVSGames.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

inductive Tape
  | input | «variables» | counter | index | field (slot : Fin 6)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

def nameField (slot : Fin 3) : Fin 6 := ⟨2 * slot.val, by omega⟩

end DFVSGames.Foundations.PCP.RawInitialMachineModel

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RawInitialMachineFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

namespace Program

open PCP.AlphabetTable

def values (vertices darts tail head row : Nat) : Fin 5 → Nat :=
  Fin.cases vertices (Fin.cases darts (Fin.cases tail (Fin.cases head (fun _ => row))))

end Program

end DFVSGames.Foundations.Complexity.FinalCNFMachine
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineLoop

open Turing

inductive HeaderTape
  | source | counter | vertices | darts
  deriving DecidableEq

instance instFintypeHeaderTape : Fintype HeaderTape where
  elems := {.source, .counter, .vertices, .darts}
  complete tape := by cases tape <;> simp

inductive HeaderLabel
  | initialize_ | scan
  deriving DecidableEq

instance instFintypeHeaderLabel : Fintype HeaderLabel where
  elems := {.initialize_, .scan}
  complete label := by cases label <;> simp

abbrev HeaderAlphabet (_ : HeaderTape) := Bool
abbrev HeaderState (σ : Type) := σ × Option Bool

def pushTrue {K Λ σ : Type} (destination : K) : Nat →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, next => next
  | count + 1, next => pushTrue destination count (.push destination (fun _ => true) next)

def headerProgram {σ : Type} (B : Nat) :
    HeaderLabel → TM2.Stmt HeaderAlphabet HeaderLabel (HeaderState σ)
  | .initialize_ =>
      .push .counter (fun _ => false)
        (.push .vertices (fun _ => false)
          (.push .darts (fun _ => false)
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan))))
  | .scan =>
      .pop .source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.push .counter (fun _ => true)
            (.push .vertices (fun _ => true)
              (pushTrue .darts B
                (.load (fun state => (state.1, none)) (.goto fun _ => .scan)))))
          (.load (fun state => (state.1, none)) .halt))

end DFVSGames.Foundations.Complexity.PoweringMachineLoop
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def reverseRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 6

def endpointRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 5 else 6

def reverseTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ reverseRole
def endpointTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ endpointRole

end DFVSGames.Foundations.Complexity.PoweringMachineRotor
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape (t : Nat) := Fin 6 ⊕ Fin (t + 1)

def first (t : Nat) : Fin (t + 1) := ⟨0, by omega⟩

def shift (t : Nat) : Tape t → Tape (t + 1) := Sum.map id Fin.succ

def rotorRole (t : Nat) (i : Fin 7) : Tape (t + 1) :=
  if i = 0 then .inl 0 else if i = 1 then .inr (first (t + 1)) else
  if i = 2 then .inl 1 else if i = 3 then .inl 2 else
  if i = 4 then .inl 3 else if i = 5 then .inr (first t).succ else .inl 4

end DFVSGames.Foundations.Complexity.PoweringMachineWord
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineTapes

abbrev Tape (max : Nat) := Fin 11 ⊕ Fin max

def table (max : Nat) : Tape max := .inl 0
def start (max : Nat) : Tape max := .inl 1
def query (max : Nat) : Tape max := .inl 2
def scan (max : Nat) : Tape max := .inl 3
def reverse (max : Nat) : Tape max := .inl 4
def scratch (max : Nat) : Tape max := .inl 5
def leftEndpoint (max : Nat) : Tape max := .inl 6
def rightEndpoint (max : Nat) : Tape max := .inl 7
def leftCopy (max : Nat) : Tape max := .inl 8
def rightCopy (max : Nat) : Tape max := .inl 9
def rowOutput (max : Nat) : Tape max := .inl 10

def endpoint (max : Nat) (target : Bool) : Tape max :=
  if target then rightEndpoint max else leftEndpoint max

@[simp] theorem endpoint_false (max : Nat) : endpoint max false = leftEndpoint max := rfl
@[simp] theorem endpoint_true (max : Nat) : endpoint max true = rightEndpoint max := rfl

def wordSharedRole (target : Bool) (i : Fin 6) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else
  if i = 3 then 4 else if i = 4 then 5 else if target then 7 else 6

def trajectoryPlacement {t max : Nat} (h : t ≤ max) : Fin (t + 1) → Tape max :=
  Fin.cases (start max) (fun i => .inr (Fin.castLE h i))

def wordPlacement {t max : Nat} (h : t ≤ max) (target : Bool) :
    PoweringMachineWord.Tape t → Tape max
  | .inl i => .inl (wordSharedRole target i)
  | .inr i => trajectoryPlacement h i

@[simp] theorem wordPlacement_inl_zero {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 0) = table max := rfl
@[simp] theorem wordPlacement_inl_one {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 1) = query max := rfl
@[simp] theorem wordPlacement_inl_two {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 2) = scan max := rfl
@[simp] theorem wordPlacement_inl_three {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 3) = reverse max := rfl
@[simp] theorem wordPlacement_inl_four {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 4) = scratch max := rfl
@[simp] theorem wordPlacement_inl_five {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 5) = endpoint max target := by cases target <;> rfl
@[simp] theorem wordPlacement_first {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inr (PoweringMachineWord.first t)) = start max := rfl
@[simp] theorem wordPlacement_succ {t max : Nat} (h : t ≤ max) (target : Bool) (i : Fin t) :
    wordPlacement h target (.inr i.succ) = .inr (Fin.castLE h i) := rfl

def relationPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 2 else
    if i = 3 then 3 else if i = 4 then 10 else 5)

@[simp] theorem relationPlacement_zero (max : Nat) : relationPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem relationPlacement_one (max : Nat) : relationPlacement max 1 = table max := rfl
@[simp] theorem relationPlacement_two (max : Nat) : relationPlacement max 2 = query max := rfl
@[simp] theorem relationPlacement_three (max : Nat) : relationPlacement max 3 = scan max := rfl
@[simp] theorem relationPlacement_four (max : Nat) : relationPlacement max 4 = rowOutput max := rfl
@[simp] theorem relationPlacement_five (max : Nat) : relationPlacement max 5 = scratch max := rfl

def equalityPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else
    if i = 3 then 9 else if i = 4 then 5 else 10)

@[simp] theorem equalityPlacement_zero (max : Nat) : equalityPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem equalityPlacement_one (max : Nat) : equalityPlacement max 1 = rightEndpoint max := rfl
@[simp] theorem equalityPlacement_two (max : Nat) : equalityPlacement max 2 = leftCopy max := rfl
@[simp] theorem equalityPlacement_three (max : Nat) : equalityPlacement max 3 = rightCopy max := rfl
@[simp] theorem equalityPlacement_four (max : Nat) : equalityPlacement max 4 = scratch max := rfl
@[simp] theorem equalityPlacement_five (max : Nat) : equalityPlacement max 5 = rowOutput max := rfl

end DFVSGames.Foundations.Complexity.PoweringMachineTapes
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop

abbrev ExtraTape (max : Nat) := PoweringMachineTapes.Tape max ⊕ Unit
abbrev GlobalTape (max : Nat) := HeaderTape ⊕ ExtraTape max
abbrev Label := HeaderLabel ⊕ MachineUnaryAffineAt.Label

def finalOutput (max : Nat) : GlobalTape max := .inr (.inr ())

def commonPlacement (max : Nat) (tape : PoweringMachineTapes.Tape max) : GlobalTape max :=
  if tape = PoweringMachineTapes.start max then .inl .counter else .inr (.inl tape)

@[simp] theorem commonPlacement_start (max : Nat) :
    commonPlacement max (PoweringMachineTapes.start max) = .inl .counter := by
  simp [commonPlacement]

@[simp] theorem commonPlacement_table (max : Nat) :
    commonPlacement max (PoweringMachineTapes.table max) =
      .inr (.inl (PoweringMachineTapes.table max)) := by
  simp [commonPlacement, PoweringMachineTapes.table, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_scratch (max : Nat) :
    commonPlacement max (PoweringMachineTapes.scratch max) =
      .inr (.inl (PoweringMachineTapes.scratch max)) := by
  simp [commonPlacement, PoweringMachineTapes.scratch, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_rowOutput (max : Nat) :
    commonPlacement max (PoweringMachineTapes.rowOutput max) =
      .inr (.inl (PoweringMachineTapes.rowOutput max)) := by
  simp [commonPlacement, PoweringMachineTapes.rowOutput, PoweringMachineTapes.start]

def castStatement_inline_PoweringMachineInitialize {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Δ Λ σ := h ▸ q

def mergeTapes {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) : GlobalTape max → List Bool
  | .inl k => header k
  | .inr e => extra e

end DFVSGames.Foundations.Complexity.PoweringMachineInitialize
end

section

namespace DFVSGames.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

def unitTapeEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := (Fin.eq_zero i).symm

def sharedTapeEquiv (max : Nat) : PoweringMachineTapes.Tape max ≃ Fin (11 + max) :=
  finSumFinEquiv

end DFVSGames.Foundations.Complexity.PoweringGlobalEnumeration
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRelation

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

end DFVSGames.Foundations.Complexity.PoweringMachineRelation
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineRelationField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

abbrev Alphabet (_ : K) := Bool

def lookupTapes (placement : PoweringMachineTapes.Tape max → K) (i : Fin 5) : K :=
  placement (PoweringMachineTapes.relationPlacement max i.succ)

end DFVSGames.Foundations.Complexity.PoweringMachineRelationField
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape := PoweringMachineTapes.Tape

end DFVSGames.Foundations.Complexity.PoweringMachineEqualityField
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_PoweringFieldPlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses
open DFVSGames.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

def tailPorts : (n : Nat) → (Fin (n + 1) → D) → Fin (n + 1) → List D
  | 0, _, _ => []
  | n + 1, p, k => Fin.cases [] (fun j => p 0 :: tailPorts n (fun i => p i.succ) j) k

theorem tailPorts_length : ∀ (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
    (tailPorts n p k).length = k.val := by
  intro n
  induction n with
  | zero => intro p k; have hk := Fin.eq_zero k; subst k; rfl
  | succ n ih =>
      intro p k
      refine Fin.cases rfl (fun j => ?_) k
      simp only [tailPorts, Fin.cases_succ, List.length_cons, ih, Fin.val_succ]

def headPorts (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)) : List D :=
  tailPorts n p k ++ [p k]

inductive Instruction (d : Nat) where
  | relation (ports : List (Fin d)) (port : Fin d) (left right : Fin 64)
  | equal (left right : List (Fin d))

def Instruction.radius {d : Nat} : Instruction d → Nat
  | .relation ports _ _ _ => ports.length
  | .equal left right => max left.length right.length

end DFVSGames.Foundations.PCP.PoweringFieldPlan
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev Tape := PoweringMachineTapes.Tape

end DFVSGames.Foundations.Complexity.PoweringMachineField
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachinePlan

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

abbrev Command (d max : Nat) := {op : Instruction d // op.radius ≤ max}

end DFVSGames.Foundations.Complexity.PoweringMachinePlan
end

section

namespace DFVSGames.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open DFVSGames.Foundations.Complexity

variable {vertices d : Nat}

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

def reverseOffset (d n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  2 * (wordEquiv d (n + 1) ports).val + (if direction then 0 else 1)

end DFVSGames.Foundations.PCP.PoweringRowHeaderSemantics
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

def headerPlacement {t max : Nat} (h : t ≤ max) : PoweringMachineWord.Tape t → Tape max :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)) ∘ wordPlacement h false

@[simp] theorem headerPlacement_table {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 0) = table max := by
  simp [headerPlacement, table, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_query {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 1) = query max := by
  simp [headerPlacement, query, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scan {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 2) = scan max := by
  simp [headerPlacement, scan, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_reverse {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 3) = reverse max := by
  simp [headerPlacement, reverse, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scratch {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 4) = scratch max := by
  simp [headerPlacement, scratch, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_output {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 5) = rowOutput max := by
  simp [headerPlacement]

end DFVSGames.Foundations.Complexity.PoweringMachineRowHeaders
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineRowBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRowBody

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev capacity (n : Nat) := 2 * (n + 1)

end DFVSGames.Foundations.Complexity.PoweringMachineRowBody
end

section

namespace DFVSGames.Foundations.PCP.PoweringTableLayout

open DFVSGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

end DFVSGames.Foundations.PCP.PoweringTableLayout
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineOuterLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

abbrev Alphabet (_ : K) := Bool

abbrev Label (enumeration : Fin N ≃ K) (output : K) :=
  MachineUnaryAffineAt.Label ⊕ (MachineUnaryAffineAt.Label ⊕
    MachineDrainMany.Label (MachineDrainMany.workTapes enumeration output))

end DFVSGames.Foundations.Complexity.PoweringMachineFinish
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Clone100Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Outer.Clone100Triples

abbrev Index := Fin 100

end DFVSGames.Outer.Clone100Triples
end

section

namespace DFVSGames.Explicit.MachineClone100Model

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

def tripleField (t : Nat × Nat × Nat) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2
  | _ => 0

end DFVSGames.Explicit.MachineClone100Model
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_MachineClone100Finish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryValidatorMachine

inductive Mode
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3) (last : Bool)
  | digit (slot : Fin 3)
  | done
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Mode :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

def nextMode : Mode → Bool → Mode
  | .clause, true => .sign 0
  | .clause, false => .done
  | .sign slot, _ => .name slot true
  | .name slot _, true => .digit slot
  | .name slot last, false => if last then afterName slot else .reject
  | .digit slot, bit => .name slot bit
  | .done, _ => .reject
  | .reject, _ => .reject

def run : Mode → List Bool → Mode
  | mode, [] => mode
  | mode, bit :: rest => run (nextMode mode bit) rest

@[simp] theorem run_reject (input : List Bool) : run .reject input = .reject := by
  induction input with
  | nil => rfl
  | cons bit input ih => simpa only [run, nextMode] using ih

theorem run_done_iff (input : List Bool) : run .done input = .done ↔ input = [] := by
  cases input with
  | nil => simp [run]
  | cons bit rest => simp [run, nextMode]

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

end DFVSGames.BinaryValidatorMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryTotalInputMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryTotalInputMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer
open DFVSGames.Reduction.MachineSubstitution
open BinaryValidatorMachine (Mode nextMode run)

inductive Label
  | scan
  | restore
  | drain
  | rejectOutput
  deriving DecidableEq

instance instFintypeLabel : Fintype Label := derive_fintype% Label

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := Mode × Option Bool

def tapes (input output saved : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => output
  | _ => saved

@[simp] theorem tapes_input (input output saved : List Bool) :
    tapes input output saved 0 = input := rfl

@[simp] theorem tapes_output (input output saved : List Bool) :
    tapes input output saved 1 = output := rfl

@[simp] theorem tapes_saved (input output saved : List Bool) :
    tapes input output saved 2 = saved := rfl

theorem update_input_inline_MachineBinaryTotalInputMachine (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 0 replacement =
      tapes replacement output saved := by
  funext k
  fin_cases k <;> rfl

theorem update_output_inline_MachineBinaryTotalInputMachine (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 1 replacement =
      tapes input replacement saved := by
  funext k
  fin_cases k <;> rfl

theorem update_saved_inline_MachineBinaryTotalInputMachine (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 2 replacement =
      tapes input output replacement := by
  funext k
  fin_cases k <;> rfl

def afterScan (mode : Mode) : Label := if mode = .done then .restore else .drain

theorem joinTrace_inline_MachineBinaryTotalInputMachine {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def steps (input : List Bool) : Nat :=
  if run .clause input = .done then 2 * input.length + 2 else 2 * input.length + 3

theorem steps_le (input : List Bool) : steps input ≤ 2 * input.length + 3 := by
  unfold steps
  split <;> omega

end DFVSGames.BinaryTotalInputMachine

end

section

namespace DFVSGames.BinaryNameCompare

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

def scanStateEquiv (A : Type) : BinaryNameMachine.State (A × Bool) ≃ State A where
  toFun s := ((s.1.1, s.1.2, s.2.1), s.2.2)
  invFun s := ((s.1.1, s.1.2.1), s.1.2.2, s.2)
  left_inv := by rintro ⟨⟨a, b⟩, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

inductive Label
  | scan | copyOut | copyBack | compare
  deriving DecidableEq

instance instFintypeLabel : Fintype Label := derive_fintype% Label

def steps (payloadLength keyLength : Nat) : Nat :=
  (payloadLength + 1) + 2 * (keyLength + 1) + (max payloadLength keyLength + 1)

theorem steps_le (payloadLength keyLength : Nat) :
    steps payloadLength keyLength ≤ 2 * payloadLength + 3 * keyLength + 4 := by
  unfold steps
  omega

theorem joinTrace_inline_MachineBinaryNameCompare {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end DFVSGames.BinaryNameCompare

end

section

namespace DFVSGames.BinaryNameSearch

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

abbrev Token := Bool × List Bool

def tokenBits (token : Token) : List Bool :=
  token.1 :: BinaryNameMachine.frame token.2

def stream : List Token → List Bool
  | [] => []
  | token :: tokens => tokenBits token ++ stream tokens

def payloads (tokens : List Token) : List (List Bool) := tokens.map Prod.snd

def afterMatch : List Token → List Bool → List Token
  | [], _ => []
  | token :: tokens, key => if token.2 = key then tokens else afterMatch tokens key

def steps : List Token → List Bool → Nat
  | [], _ => 0
  | token :: tokens, key =>
      1 + BinaryNameCompare.steps token.2.length key.length +
        if token.2 = key then 0 else 1 + steps tokens key

def payloadSize (tokens : List Token) : Nat := (payloads tokens |>.map List.length).sum

@[simp] theorem stream_nil : stream [] = [] := rfl

@[simp] theorem stream_cons (token : Token) (tokens : List Token) :
    stream (token :: tokens) = tokenBits token ++ stream tokens := rfl

@[simp] theorem payloads_nil : payloads [] = [] := rfl

@[simp] theorem payloads_cons (token : Token) (tokens : List Token) :
    payloads (token :: tokens) = token.2 :: payloads tokens := rfl

@[simp] theorem payloadSize_nil : payloadSize [] = 0 := rfl

@[simp] theorem payloadSize_cons (token : Token) (tokens : List Token) :
    payloadSize (token :: tokens) = token.2.length + payloadSize tokens := rfl

@[simp] theorem stream_length (tokens : List Token) :
    (stream tokens).length = 2 * payloadSize tokens + 2 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [stream_cons, List.length_append, tokenBits, List.length_cons,
        BinaryNameMachine.frame_length, ih, payloadSize_cons]
      omega

theorem steps_le (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ 2 * payloadSize tokens + (3 * key.length + 6) * tokens.length := by
  induction tokens with
  | nil => simp [steps]
  | cons token tokens ih =>
      have h := BinaryNameCompare.steps_le token.2.length key.length
      simp only [steps, payloadSize_cons, List.length_cons]
      split <;> nlinarith

theorem steps_le_stream (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ (3 * key.length + 7) * (stream tokens).length := by
  have h := steps_le tokens key
  rw [stream_length]
  nlinarith

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State A

abbrev clean (ambient : A) : State A := BinaryNameCompare.clean ambient

inductive Label
  | sign
  | comparison (label : BinaryNameCompare.Label)
  | increment
  deriving DecidableEq, Fintype

def compareTapes (tape : Fin 6 → K) : Fin 5 → K := fun i => tape i.castSucc

omit [DecidableEq K] in
theorem compareTapes_injective (tape : Fin 6 → K) (distinct : Function.Injective tape) :
    Function.Injective (compareTapes tape) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 6 => i.val) (distinct h)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1) (exitAt exit)

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1.1, base⟩ := by
  cases exit <;> rfl

theorem joinTrace_inline_MachineBinaryNameSearch {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Program

end DFVSGames.BinaryNameSearch

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryLiteralMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryLiteralMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State (A × Bool)
abbrev clean (ambient : A) (sign : Bool := false) : State A :=
  BinaryNameCompare.clean (ambient, sign)

inductive Label
  | readSign | scanKey | copyOut | copyBack
  | search (label : BinaryNameSearch.Label)
  | drainSearch | drainKey | emitIndex | emitSign
  deriving DecidableEq, Fintype

def searchTapes (tape : Fin 9 → K) : Fin 6 → K
  | 0 => tape 3
  | 1 => tape 2
  | 2 => tape 4
  | 3 => tape 5
  | 4 => tape 6
  | 5 => tape 7

omit [DecidableEq K] in
theorem searchTapes_injective (tape : Fin 9 → K) (distinct : Function.Injective tape) :
    Function.Injective (searchTapes tape) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp only [searchTapes] at h
  all_goals first | rfl | have heq := congrArg Fin.val (distinct h); norm_num at heq

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def readSign (tape : Fin 9 → K) (next : Λ) (malformed : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push (tape 7) (fun _ => false)
    (.pop (tape 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.load (fun state => clean state.1.1.1 (state.2.getD false)) (.goto fun _ => next))
        (finish malformed)))

def emitSign (output : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .branch (fun state => state.1.1.2)
    (.push output (fun _ => true) (.push output (fun _ => false) (finish exit)))
    (.push output (fun _ => false) (finish exit))

def index (tokens : List BinaryNameSearch.Token) (bits : List Bool) : Nat :=
  (BinaryNameSearch.payloads tokens).idxOf bits

def steps (tokens : List BinaryNameSearch.Token) (bits : List Bool) : Nat :=
  1 + (bits.length + 1) + 2 * ((BinaryNameSearch.stream tokens).length + 1) +
    BinaryNameSearch.steps tokens bits +
    ((BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length + 1) +
    (bits.length + 1) + (index tokens bits + 2) + 1

theorem afterMatch_length_le (tokens : List BinaryNameSearch.Token) (bits : List Bool) :
    (BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length ≤
      (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp [BinaryNameSearch.afterMatch]
  | cons token tokens ih =>
      simp only [BinaryNameSearch.afterMatch, BinaryNameSearch.stream_cons, List.length_append]
      split <;> omega

theorem steps_le (tokens : List BinaryNameSearch.Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    steps tokens bits ≤
      3 * ((BinaryNameSearch.stream tokens).length + bits.length) ^ 2 +
        13 * ((BinaryNameSearch.stream tokens).length + bits.length) + 9 := by
  have search := BinaryNameSearch.steps_le_stream tokens bits
  have suffix := afterMatch_length_le tokens bits
  have idx : index tokens bits < tokens.length := by
    have h := List.idxOf_lt_length_iff.mpr present
    simpa [index, BinaryNameSearch.payloads] using h
  have count : tokens.length ≤ (BinaryNameSearch.stream tokens).length := by
    rw [BinaryNameSearch.stream_length]
    omega
  unfold steps
  nlinarith [Nat.zero_le ((BinaryNameSearch.stream tokens).length * bits.length)]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1.1.1, base⟩ := by
  cases exit <;> rfl

theorem joinTrace_inline_MachineBinaryLiteralMachine {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end DFVSGames.BinaryLiteralMachine

end

section

namespace DFVSGames.BinaryRenameLoop

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

abbrev Token := BinaryNameSearch.Token

def nextSlot (slot : Fin 3) : Fin 3 := if slot = 0 then 1 else if slot = 1 then 2 else 0

def clauseIncrement (slot : Fin 3) : Nat := if slot = 2 then 1 else 0

def finalSlot : Nat → Fin 3 → Fin 3
  | 0, slot => slot
  | n + 1, slot => finalSlot n (nextSlot slot)

def completedClauses : Nat → Fin 3 → Nat
  | 0, _ => 0
  | n + 1, slot => completedClauses n (nextSlot slot) + clauseIncrement slot

theorem finalSlot_three (n : Nat) : finalSlot (n + 3) 0 = finalSlot n 0 := by
  simp [finalSlot, nextSlot]

theorem completedClauses_three (n : Nat) :
    completedClauses (n + 3) 0 = completedClauses n 0 + 1 := by
  simp [completedClauses, nextSlot, clauseIncrement]

@[simp] theorem finalSlot_triples (n : Nat) : finalSlot (3 * n) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, finalSlot_three, ih]

@[simp] theorem completedClauses_triples (n : Nat) : completedClauses (3 * n) 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, completedClauses_three, ih]

def perLiteralBound (streamLength : Nat) : Nat :=
  12 * streamLength ^ 2 + 26 * streamLength + 11

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryLiteralMachine.State (A × Fin 3)
abbrev clean (ambient : A) (slot : Fin 3) : State A :=
  BinaryLiteralMachine.clean (ambient, slot)

inductive Label
  | entry
  | literal (label : BinaryLiteralMachine.Label)
  | tally
  deriving DecidableEq, Fintype

def literalTapes (tape : Fin 11 → K) : Fin 9 → K := fun i => tape i.castSucc.castSucc

omit [DecidableEq K] in
theorem literalTapes_injective (tape : Fin 11 → K) (distinct : Function.Injective tape) :
    Function.Injective (literalTapes tape) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 11 => i.val) (distinct h)

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1.1 state.1.1.1.2)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def next (again : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1.1 (nextSlot state.1.1.1.2))
    (.goto fun _ => again)

def loopTapes (tape : Fin 11 → K) (base : K → List Bool)
    (cursor output variableCounter clauses : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (tape 0) cursor) (tape 8) output) (tape 9) variableCounter) (tape 10) clauses

theorem joinTrace_inline_MachineBinaryRenameLoop {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Program

end DFVSGames.BinaryRenameLoop

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryTokenMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryTokenMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

abbrev Tape := Fin 3
abbrev Alphabet (_ : Tape) := Bool
abbrev State := Unit × Option Bool

inductive Label where
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3)
  | restore
  | accept
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Label :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

@[simp] theorem afterName_zero : afterName 0 = .sign 1 := rfl
@[simp] theorem afterName_one : afterName 1 = .sign 2 := rfl
@[simp] theorem afterName_two : afterName 2 = .clause := rfl

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => ((), none)) (.goto fun _ => label)

def clauseInstruction : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (jump (.sign 0)) (jump .restore)))

def signInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
      (jump .reject))

def nameInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (.push 1 (fun _ => true)
          (.pop 0 (fun state head => (state.1, head))
            (.branch (fun state => state.2.isSome)
              (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
              (jump .reject))))
        (.push 1 (fun _ => false) (jump (afterName slot)))))

def tapes (input reversed output : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then reversed else output

@[simp] theorem tapes_zero (input reversed output : List Bool) :
    tapes input reversed output 0 = input := rfl

@[simp] theorem tapes_one (input reversed output : List Bool) :
    tapes input reversed output 1 = reversed := rfl

@[simp] theorem tapes_two (input reversed output : List Bool) :
    tapes input reversed output 2 = output := rfl

theorem update_zero_inline_MachineBinaryTokenMachine (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 0 replacement =
      tapes replacement reversed output := by
  funext k
  fin_cases k <;> simp [tapes]

theorem update_one_inline_MachineBinaryTokenMachine (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 1 replacement =
      tapes input replacement output := by
  funext k
  fin_cases k <;> simp [tapes]

theorem joinTrace_inline_MachineBinaryTokenMachine {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end DFVSGames.BinaryTokenMachine

end

section

namespace DFVSGames.BinaryHeaderMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

def delimiter (destination : K) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

def tapes (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base variableTape variableCounter)
    clauses clauseCounter) destination output

variable (variableTape clauses destination : K)
variable (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
variable (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atClauseStart : program clauseStart = delimiter destination clauseLoop)
variable (atVariableStart : program variableStart = delimiter destination variableLoop)
variable (base : K → List Bool) (ambient : A)

theorem joinTrace_inline_MachineBinaryHeaderMachine {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Placement

end DFVSGames.BinaryHeaderMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryRenameMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryRenameMachine

open Turing DFVSGames.Foundations
open Complexity Complexity.MachineComposition
open DFVSGames.Reduction.MachineTransfer

abbrev Tape := Fin 12
abbrev Alphabet (_ : Tape) := Bool

inductive Label
  | copyOut | copyBack
  | loop (label : BinaryRenameLoop.Label)
  | restore | clauseStart | clauseLoop | variableStart | variableLoop
  | cleanup | reject
  deriving DecidableEq, Fintype

def loopTapes : Fin 11 → Tape := Fin.castSucc

theorem loopTapes_injective : Function.Injective loopTapes := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Tape => k.val) h

def tapes (permanent cursor reversed variableCounter clauseCounter output : List Bool) :
    Tape → List Bool := fun k =>
  if k = 0 then cursor
  else if k = 1 then permanent
  else if k = 8 then reversed
  else if k = 9 then variableCounter
  else if k = 10 then clauseCounter
  else if k = 11 then output
  else []

theorem joinTrace_inline_MachineBinaryRenameMachine {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 12 * Polynomial.X ^ 3 + Polynomial.C 35 * Polynomial.X ^ 2 +
    Polynomial.C 28 * Polynomial.X + Polynomial.C 11

end DFVSGames.BinaryRenameMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.SourceEquationLookup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition SourceMachine

inductive Tape
  | source | index | work | scratch | field (slot : Fin 4)
  deriving DecidableEq, Fintype

inductive Label
  | copyOut | copyBack | headerFirst | headerSecond | guard
  | skip (slot : Fin 4)
  | read (slot : Fin 5 × Bool)
  deriving DecidableEq, Fintype

def fieldDestination (r : Nat) : Tape := .field ⟨min r 3, by omega⟩
def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 4 r, false)
def skipLabel (r : Nat) : Label := if h : r < 4 then .skip ⟨r, h⟩ else .guard

end DFVSGames.Reduction.SourceEquationLookup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineSourceTuple

open Turing DFVSGames.Foundations.Complexity
open MachineComposition

inductive Tape (width : Nat) (Extra : Type)
  | source | index | work | scratch | copyScratch
  | savedIndex (coordinate : Fin width)
  | field (coordinate : Fin width) (slot : Fin 4)
  | extra (value : Extra)
  deriving DecidableEq, Fintype

inductive Label (width : Nat)
  | copyOut (coordinate : Fin width) | copyBack (coordinate : Fin width)
  | lookup (coordinate : Fin width) (localLabel : SourceEquationLookup.Label)
  | clearWork (coordinate : Fin width) | clearIndex (coordinate : Fin width)
  | done
  deriving DecidableEq, Fintype

variable {width : Nat} {Extra σ : Type}

variable [DecidableEq Extra]

def nextLabel (j : Fin width) : Label width :=
  if h : j.val + 1 < width then .copyOut ⟨j.val + 1, h⟩ else .done

def labelAt (r : Nat) : Label width :=
  if h : r < width then .copyOut ⟨r, h⟩ else .done

def nameSlot (s : Fin 3) : Fin 4 := ⟨s.val, by omega⟩

end DFVSGames.Reduction.MachineSourceTuple
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAddressHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineAddressHeaders

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition

namespace Prefix

inductive Label
  | copyOut | copyBack | read (slot : Fin 3 × Bool) | clear
  deriving DecidableEq, Fintype

def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 2 r, false)

variable {K Λ σ : Type} [DecidableEq K]

def destination (slots : Fin 5 ↪ K) (r : Nat) : K := if r = 0 then slots 2 else slots 3

end Prefix

def baseConstant (s d : Nat) : Nat := 2 ^ s + 2 ^ d + 4
def radix (s d n m : Nat) : Nat := n + m + baseConstant s d
def capacity (k s d n m : Nat) : Nat := (radix s d n m) ^ (1 + 9 * k)
def edgeFactor (k s d noiseCount : Nat) : Nat :=
  2 ^ ((2 * k + 1) * (s + d + 1)) * noiseCount
def edgeCount (k s d noiseCount m : Nat) : Nat := edgeFactor k s d noiseCount * m ^ k

noncomputable section

inductive Kind | capacity | edges
  deriving DecidableEq

instance instFintypeKind : Fintype Kind where
  elems := {.capacity, .edges}
  complete := by intro kind; cases kind <;> simp

def polynomial (k s d noiseCount : Nat) : Kind → Polynomial Nat
  | .capacity => Polynomial.X ^ (1 + 9 * k)
  | .edges => Polynomial.C (edgeFactor k s d noiseCount) * Polynomial.X ^ k

@[simp] theorem polynomial_capacity_eval (k s d noiseCount B : Nat) :
    (polynomial k s d noiseCount .capacity).eval B = B ^ (1 + 9 * k) := by
  simp [polynomial]

@[simp] theorem polynomial_edges_eval (k s d noiseCount m : Nat) :
    (polynomial k s d noiseCount .edges).eval m = edgeCount k s d noiseCount m := by
  simp [polynomial, edgeCount]

namespace Arithmetic

inductive Control
  | variableCount | occurrenceCount | baseValue | capacity | temporary | reversed
  | accA | accB | counter | scratch
  deriving DecidableEq

instance instFintypeControl : Fintype Control where
  elems := {.variableCount, .occurrenceCount, .baseValue, .capacity, .temporary,
    .reversed, .accA, .accB, .counter, .scratch}
  complete := by intro control; cases control <;> simp

def inputControl : Kind → Control
  | .capacity => .baseValue | .edges => .occurrenceCount

def outputControl : Kind → Control
  | .capacity => .capacity | .edges => .temporary

def controlSlots (kind : Kind) : Fin 6 ↪ Control where
  toFun i := match i.val with
    | 0 => inputControl kind | 1 => .accA | 2 => .accB
    | 3 => outputControl kind | 4 => .counter | _ => .scratch
  inj' := by
    intro i j h
    cases kind <;> fin_cases i <;> fin_cases j <;> cases h <;> rfl

end Arithmetic

end

end DFVSGames.Reduction.MachineAddressHeaders
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTemplateAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineTemplateAddress

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

inductive Tape (q width : Nat)
  | field (i : Fin q)
  | radix | output | reversed | forward | copyScratch
  | accA | accB | counter | hornerScratch
  | digit (i : Fin width)
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def chosen (slots : Tape q width ↪ K) : List K := List.ofFn (fun i => slots (.digit i))

omit [DecidableEq K] in
@[simp] theorem mem_chosen (slots : Tape q width ↪ K) (tape : K) :
    tape ∈ chosen slots ↔ ∃ i, slots (.digit i) = tape := by
  simp [chosen, List.mem_ofFn]

abbrev Label (m width : Nat) (cleanup : List K) :=
  MachineFieldTemplate.Label m ⊕ Unit ⊕ (Fin (width + 1) × Bool) ⊕
    MachineHorner.Label width ⊕ MachineDrainMany.Label cleanup

def emitLabel {m : Nat} {cleanup : List K} (l : MachineFieldTemplate.Label m) :
    Label m width cleanup := .inl l
def reverseLabel {m : Nat} {cleanup : List K} : Label m width cleanup := .inr (.inl ())
def parseLabel {m : Nat} {cleanup : List K} (l : Fin (width + 1) × Bool) :
    Label m width cleanup := .inr (.inr (.inl l))
def hornerLabel {m : Nat} {cleanup : List K} (l : MachineHorner.Label width) :
    Label m width cleanup := .inr (.inr (.inr (.inl l)))
def cleanupLabel {m : Nat} {cleanup : List K} (l : MachineDrainMany.Label cleanup) :
    Label m width cleanup := .inr (.inr (.inr (.inr l)))

def parseDestination (slots : Tape q width ↪ K) (i : Nat) : K :=
  if h : i < width then slots (.digit ⟨i, h⟩) else slots .forward

omit [DecidableEq K] in
@[simp] theorem parseDestination_below (slots : Tape q width ↪ K) (i : Nat) (hi : i < width) :
    parseDestination slots i = slots (.digit ⟨i, hi⟩) := by simp [parseDestination, hi]

end DFVSGames.Reduction.MachineTemplateAddress
end

section

namespace DFVSGames.Reduction.MachineAddressEdge

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

abbrev Label (leftLength rightLength width : Nat) (cleanup : List K) :=
  MachineTemplateAddress.Label leftLength width cleanup ⊕ MachineTemplateAddress.Label rightLength width cleanup ⊕ Fin 7

def leftLabel {ml mr : Nat} {cleanup : List K} (label : MachineTemplateAddress.Label ml width cleanup) :
    Label ml mr width cleanup := .inl label
def rightLabel {ml mr : Nat} {cleanup : List K} (label : MachineTemplateAddress.Label mr width cleanup) :
    Label ml mr width cleanup := .inr (.inl label)
def plumbing {ml mr : Nat} {cleanup : List K} (index : Fin 7) :
    Label ml mr width cleanup := .inr (.inr index)

end DFVSGames.Reduction.MachineAddressEdge
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_CanonicalWordTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.CanonicalWordTemplate

open Foundations.Complexity

inductive Token
  | literal (value : Nat)
  | name (index : Fin 3)
  | occurrence
  deriving DecidableEq, Repr

def evalToken (names : Fin 3 → Nat) (occurrence : Nat) : Token → Nat
  | .literal value => value
  | .name index => names index
  | .occurrence => occurrence

def evalTemplate (names : Fin 3 → Nat) (occurrence : Nat)
    (tokens : List Token) : List Nat :=
  tokens.map (evalToken names occurrence)

def isVariable : Token → Bool
  | .literal _ => false
  | .name _ => true
  | .occurrence => true

def variableTokens (tokens : List Token) : List Token := tokens.filter isVariable

def blankTemplate : List Token :=
  [.literal 0, .literal 0, .literal 0, .literal 0, .literal 0,
    .literal 0, .literal 0, .literal 0, .literal 0]

@[simp] theorem blankTemplate_length : blankTemplate.length = 9 := rfl

end DFVSGames.Reduction.CanonicalWordTemplate
end

section

namespace DFVSGames.Reduction.CanonicalBodyTemplate

open Foundations.Complexity
open scoped BigOperators

variable {k : Nat}

inductive Token (k : Nat)
  | literal (value : Nat)
  | field (position : Fin k) (index : Fin 4)
  deriving DecidableEq, Repr

def evalToken (fields : Fin k → Fin 4 → Nat) : Token k → Nat
  | .literal value => value
  | .field position index => fields position index

def evalTemplate (fields : Fin k → Fin 4 → Nat) (tokens : List (Token k)) : List Nat :=
  tokens.map (evalToken fields)

def nameField (j : Fin 3) : Fin 4 := ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

def recordFields (names : Fin 3 → Nat) (occurrence : Nat) (i : Fin 4) : Nat :=
  if h : i.val < 3 then names ⟨i.val, h⟩ else occurrence

end DFVSGames.Reduction.CanonicalBodyTemplate
end

section

namespace DFVSGames.Reduction.CanonicalBodyMachine

open Foundations.Complexity

variable {k : Nat}

def fieldEquiv (k : Nat) : (Fin k × Fin 4) ≃ Fin (4*k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k 4))

def fieldIndex (position : Fin k) (field : Fin 4) : Fin (4*k) :=
  fieldEquiv k (position, field)

end DFVSGames.Reduction.CanonicalBodyMachine
end

section

namespace DFVSGames.Reduction.AddressMachineSpace

open DFVSGames.Foundations.Complexity

abbrev Control (k : Nat) := ((Fin k → Bool) × Unit) × Unit
abbrev State (k : Nat) := Control k × Option Bool

def initialState (k : Nat) : State k := (((fun _ => false, ()), ()), none)

end DFVSGames.Reduction.AddressMachineSpace
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AddressTupleLoaded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineRhsLoad

open Turing
open DFVSGames.Foundations.Complexity

abbrev State (k : Nat) (σ : Type) := (((Fin k → Bool) × σ) × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

def rhs {k σ} (state : State k σ) : Fin k → Bool := state.1.1.1

def setRhs {k σ} (state : State k σ) (values : Fin k → Bool) : State k σ :=
  (((values, state.1.1.2), state.1.2), state.2)

@[simp] theorem rhs_setRhs {k σ} (state : State k σ) (values : Fin k → Bool) :
    rhs (setRhs state values) = values := rfl

@[simp] theorem setRhs_setRhs {k σ} (state : State k σ)
    (first second : Fin k → Bool) : setRhs (setRhs state first) second = setRhs state second := rfl

@[simp] theorem setRhs_same {k σ} (state : State k σ) : setRhs state (rhs state) = state := rfl

section Program

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State k σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def peekChain (field : Fin k → K) (exit : Option Λ) :
    List (Fin k) → TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | [] => finish exit
  | i :: rest =>
    .peek (field i) (fun state head =>
      setRhs state (Function.update (rhs state) i (head.getD false)))
      (peekChain field exit rest)

def statement (field : Fin k → K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State k σ) := peekChain field exit (List.finRange k)

end Program

end DFVSGames.Reduction.MachineRhsLoad
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineOutcomeRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineOutcomeRows

open Turing
open DFVSGames.Foundations.Complexity

structure Values (width : Nat) where
  left : List Nat
  right : List Nat
  left_length : left.length = width
  right_length : right.length = width

abbrev Rhs (k : Nat) := Fin k → Bool
abbrev State (k : Nat) (σ : Type) := MachineRhsLoad.State k σ
abbrev Alphabet {K : Type} (_ : K) := Bool

end DFVSGames.Reduction.MachineOutcomeRows
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_UniformReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.AddressOutcomeSpecs

open Foundations.Complexity
open Integration

abbrev Values (k : Nat) := MachineOutcomeRows.Values (1+9*k)

end DFVSGames.Reduction.AddressOutcomeSpecs
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AddressTupleBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

abbrev BodyState (k : Nat) := AddressMachineSpace.State k

end DFVSGames.Integration.AddressTupleBody
end

section

namespace DFVSGames.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration
open MachineComposition

noncomputable section

abbrev State (k : Nat) := AddressMachineSpace.State k

end
end DFVSGames.Reduction.AddressMachineProgram
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_AddressMachineInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.OccurrenceTupleOrder

open Turing
open DFVSGames.Foundations.Complexity
open MachineTupleOdometer

variable {α : Type*}

def readCoordinates {m k : Nat} (digits : Fin k → Fin m) : Fin k → Fin m :=
  digits ∘ Fin.rev

@[simp] theorem readCoordinates_apply {m k : Nat} (digits : Fin k → Fin m) (j : Fin k) :
    readCoordinates digits j = digits j.rev := rfl

@[simp] theorem readCoordinates_involutive {m k : Nat} (digits : Fin k → Fin m) :
    readCoordinates (readCoordinates digits) = digits := by
  funext j
  simp only [readCoordinates_apply, Fin.rev_rev]

theorem readCoordinates_snoc {m k : Nat} (tail : Fin k → Fin m) (d : Fin m) :
    readCoordinates (Fin.snoc tail d) = Fin.cons d (readCoordinates tail) :=
  Fin.snoc_comp_rev d tail

end DFVSGames.Reduction.OccurrenceTupleOrder
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse

theorem binary_kernel_finrank_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    ℓ - r ≤ Module.finrank (ZMod 2) A.ker := by
  have hnull : Module.finrank (ZMod 2) A.range +
      Module.finrank (ZMod 2) A.ker = ℓ := by
    simpa only [Module.finrank_fin_fun] using A.finrank_range_add_finrank_ker
  have hrange : Module.finrank (ZMod 2) A.range ≤ r := by
    simpa only [Module.finrank_fin_fun] using A.range.finrank_le
  apply Nat.sub_le_iff_le_add.mpr
  calc
    ℓ = Module.finrank (ZMod 2) A.ker +
        Module.finrank (ZMod 2) A.range := hnull.symm.trans (Nat.add_comm _ _)
    _ ≤ Module.finrank (ZMod 2) A.ker + r :=
      Nat.add_le_add_left hrange _

theorem binary_kernel_card_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    2 ^ (ℓ - r) ≤ Nat.card A.ker := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) (binary_kernel_finrank_lower A)

end DFVSGames.Inverse

noncomputable section
open scoped BigOperators Classical

namespace DFVSGames.Decoder.NoiseSampler

section FiniteLaw

variable {Noise V : Type*} [Fintype Noise] [Fintype V]

def samplerLaw (noise : Noise → V) (v : V) : ℝ := by
  classical
  exact ∑ n, if noise n = v then (Fintype.card Noise : ℝ)⁻¹ else 0

end FiniteLaw

end DFVSGames.Decoder.NoiseSampler
end

namespace DFVSGames.Appendix.RankAdditivity

open Module LinearMap

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

theorem ker_add_of_disjoint (f g : W →ₗ[K] V)
    (h : Disjoint (LinearMap.range f) (LinearMap.range g)) :
    LinearMap.ker (f + g) = LinearMap.ker f ⊓ LinearMap.ker g := by
  ext w
  constructor
  · intro hw
    have hsum : f w + g w = 0 := hw
    have hf : f w = 0 := by
      apply Submodule.disjoint_def.mp h (f w)
      · exact ⟨w, rfl⟩
      · exact ⟨-w, by simpa only [map_neg] using (eq_neg_of_add_eq_zero_left hsum).symm⟩
    have hg : g w = 0 := by simpa only [hf, zero_add] using hsum
    exact ⟨hf, hg⟩
  · rintro ⟨hf, hg⟩
    change f w + g w = 0
    change f w = 0 at hf
    change g w = 0 at hg
    rw [hf, hg, add_zero]

variable [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in

theorem finrank_add_eq_iff (f g : W →ₗ[K] V) :
    finrank K (LinearMap.range (f + g)) =
        finrank K (LinearMap.range f) + finrank K (LinearMap.range g) ↔
      Disjoint (LinearMap.range f) (LinearMap.range g) ∧
        LinearMap.ker f ⊔ LinearMap.ker g = ⊤ := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hfg := (f + g).finrank_range_add_finrank_ker
  have hker := (LinearMap.ker f).finrank_sup_add_finrank_inf_eq (LinearMap.ker g)
  constructor
  · intro hrank
    have hle := Submodule.finrank_mono (LinearMap.range_add_le f g)
    have himage := (LinearMap.range f).finrank_sup_add_finrank_inf_eq (LinearMap.range g)
    have hinf : finrank K (LinearMap.range f ⊓ LinearMap.range g : Submodule K V) = 0 := by
      omega
    have hd : Disjoint (LinearMap.range f) (LinearMap.range g) := by
      exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf)
    refine ⟨hd, ?_⟩
    have heq := ker_add_of_disjoint f g hd
    rw [heq] at hfg
    apply Submodule.eq_top_of_finrank_eq
    omega
  · rintro ⟨hd, htop⟩
    rw [ker_add_of_disjoint f g hd] at hfg
    rw [htop, finrank_top] at hker
    omega

omit [FiniteDimensional K V] in

theorem range_left_le_range_add (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.range f ≤ LinearMap.range (f + g) := by
  have hk := ((finrank_add_eq_iff f g).mp h).2
  intro v hv
  have hp : (v, (0 : V)) ∈ (LinearMap.range f).prod (LinearMap.range g) :=
    ⟨hv, Submodule.zero_mem _⟩
  rw [← LinearMap.range_prod_eq hk] at hp
  rcases hp with ⟨w, hw⟩
  have hwf : f w = v := congrArg Prod.fst hw
  have hwg : g w = 0 := congrArg Prod.snd hw
  refine ⟨w, ?_⟩
  change f w + g w = v
  rw [hwf, hwg, add_zero]

omit [FiniteDimensional K V] in

theorem ker_add_le_ker_left (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.ker (f + g) ≤ LinearMap.ker f := by
  rw [ker_add_of_disjoint f g ((finrank_add_eq_iff f g).mp h).1]
  exact inf_le_left

def RankBelow (X Y : W →ₗ[K] V) : Prop :=
  finrank K (LinearMap.range Y) =
    finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X))

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem add_remainder (X Y : W →ₗ[K] V) : X + (Y - X) = Y := by
  rw [add_comm X, sub_add_cancel]

omit [FiniteDimensional K V] in
theorem range_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range X ≤ LinearMap.range Y := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using range_left_le_range_add X (Y - X) h'

omit [FiniteDimensional K V] in
theorem ker_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.ker Y ≤ LinearMap.ker X := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using ker_add_le_ker_left X (Y - X) h'

end DFVSGames.Appendix.RankAdditivity

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PositiveMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace DFVSGames.Fourier.SplitMaps

variable {K E C D : Type*} [CommSemiring K]
    [AddCommMonoid E] [Module K E]
    [AddCommMonoid C] [Module K C]
    [AddCommMonoid D] [Module K D]

def codomainSplit : (E →ₗ[K] C × D) ≃ₗ[K] (E →ₗ[K] C) × (E →ₗ[K] D) :=
  (LinearMap.prodEquiv K).symm

def domainSplit : (C × D →ₗ[K] E) ≃ₗ[K] (C →ₗ[K] E) × (D →ₗ[K] E) :=
  (LinearMap.coprodEquiv K).symm

@[simp] theorem codomainSplit_symm_apply (X : E →ₗ[K] C) (Z : E →ₗ[K] D) :
    codomainSplit.symm (X, Z) = X.prod Z := rfl

@[simp] theorem domainSplit_symm_apply (S : C →ₗ[K] E) (T : D →ₗ[K] E) :
    domainSplit.symm (S, T) = S.coprod T := rfl

end DFVSGames.Fourier.SplitMaps
end

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Reduction

namespace DFVSGames.Decoder.ActualSpectral

open NoiseSampler

def eta (r : Nat) : ℝ := ((2 : ℝ) ^ r)⁻¹ / 16

end DFVSGames.Decoder.ActualSpectral
end

namespace DFVSGames.Inverse.RowErasure

open scoped BigOperators

noncomputable section

def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

@[simp] theorem indicator_true : indicator True = 1 := by simp [indicator]
@[simp] theorem indicator_false : indicator False = 0 := by simp [indicator]

def uniformMass {X : Type*} [Fintype X] (p : X → Prop) : ℝ :=
  Finset.univ.expect fun x => indicator (p x)

def adviceMass {A X : Type*} [Fintype A] [Fintype X]
    (good : A → X → Prop) : ℝ :=
  Finset.univ.expect fun x => uniformMass fun a => good a x

end
end DFVSGames.Inverse.RowErasure

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.RowErasure

open scoped BigOperators

noncomputable section

variable {X Y A S D : Type*}

structure SliceFamily (X Y A S D : Type*) where
  advice : A → X → S
  rowMap : D → A
  rowValue : D → S
  points : D → Finset X
  target : D → X → Y
  points_row : ∀ d x, x ∈ points d → advice (rowMap d) x = rowValue d

def SliceFamily.agreement (F : SliceFamily X Y A S D) (f : X → Y) (d : D) : ℝ :=
  (F.points d).expect fun x => indicator (f x = F.target d x)

def SliceFamily.GoodAdvice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Prop :=
  ∃ d, F.rowMap d = a ∧ F.rowValue d = s ∧ (F.points d).Nonempty ∧
    α / 2 ≤ F.agreement f d

def SliceFamily.goodAt (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  F.GoodAdvice f α a (F.advice a x)

end
end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

abbrev F2 := ZMod 2
abbrev Vector (n : ℕ) := Fin n → F2
abbrev Mat (ell m : ℕ) := Matrix (Fin ell) (Fin m) F2

def rankOne {ell m : ℕ} (a : Vector ell) (l : Vector m) : Mat ell m :=
  fun i j => a i * l j

def evaluate {ell m : ℕ} (M : Mat ell m) (z : Vector m) : Vector ell :=
  fun i => ∑ j, M i j * z j

@[simp] theorem evaluate_zero {ell m : ℕ} (M : Mat ell m) : evaluate M 0 = 0 := by
  ext i
  simp [evaluate]

@[simp] theorem rankOne_zero_left {ell m : ℕ} (l : Vector m) :
    rankOne (0 : Vector ell) l = 0 := by
  ext i j
  simp [rankOne]

@[simp] theorem rankOne_zero_right {ell m : ℕ} (a : Vector ell) :
    rankOne a (0 : Vector m) = 0 := by
  ext i j
  simp [rankOne]

def equalityAcceptance {ell m : ℕ} (f : Mat ell m → Vector ell) : ℝ :=
  𝔼 M, 𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0

structure Slice (ell m : ℕ) where
  rows : ℕ
  columns : ℕ
  rowCoefficient : Fin rows → Vector ell
  rowValue : Fin rows → Vector m
  columnCoefficient : Fin columns → Vector m
  columnValue : Fin columns → Vector ell

def Slice.Contains {ell m : ℕ} (S : Slice ell m) (M : Mat ell m) : Prop :=
  (∀ i j, (∑ a, S.rowCoefficient i a * M a j) = S.rowValue i j) ∧
    ∀ i, evaluate M (S.columnCoefficient i) = S.columnValue i

def Slice.points {ell m : ℕ} (S : Slice ell m) : Finset (Mat ell m) :=
  Finset.univ.filter S.Contains

def Slice.affineAgreement {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) : ℝ :=
  S.points.expect fun M => if f M = evaluate M z + u then 1 else 0

def HasAffineSlice {ell m : ℕ} (f : Mat ell m → Vector ell) (α : ℝ) (r : ℕ) : Prop :=
  ∃ S : Slice ell m, S.rows ≤ r ∧ S.columns ≤ r ∧ S.points.Nonempty ∧
    ∃ z : Vector m, ∃ u : Vector ell, α ≤ S.affineAgreement f z u

end
end DFVSGames.Inverse.Shortcode

namespace DFVSGames.Inverse.RowErasureDescriptions

open DFVSGames.Inverse.Shortcode
open scoped BigOperators

noncomputable section

abbrev RowMap (ell r : ℕ) := Fin r → Vector ell

abbrev Description (ell m r : ℕ) :=
  (Fin r → Vector ell) × (Fin r → Vector m) ×
    (Fin r → Vector m) × (Fin r → Vector ell) × Vector m × Vector ell

def Description.toSlice {ell m r : ℕ} (d : Description ell m r) : Slice ell m where
  rows := r
  columns := r
  rowCoefficient := d.1
  rowValue := d.2.1
  columnCoefficient := d.2.2.1
  columnValue := d.2.2.2.1

def Description.coefficient {ell m r : ℕ} (d : Description ell m r) : Vector m :=
  d.2.2.2.2.1

def Description.intercept {ell m r : ℕ} (d : Description ell m r) : Vector ell :=
  d.2.2.2.2.2

def padZero {n r : ℕ} {V : Type*} [Zero V] (f : Fin n → V) : Fin r → V :=
  fun i => if h : i.val < n then f ⟨i.val, h⟩ else 0

def padSlice {ell m : ℕ} (S : Slice ell m) (r : ℕ) : Slice ell m where
  rows := r
  columns := r
  rowCoefficient := padZero S.rowCoefficient
  rowValue := padZero S.rowValue
  columnCoefficient := padZero S.columnCoefficient
  columnValue := padZero S.columnValue

def describe {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (padZero S.rowCoefficient, padZero S.rowValue,
    padZero S.columnCoefficient, padZero S.columnValue, z, u)

@[simp] theorem describe_toSlice {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) :
    (describe (r := r) S z u).toSlice = padSlice S r := rfl

@[simp] theorem describe_coefficient {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : (describe (r := r) S z u).coefficient = z := rfl

@[simp] theorem describe_intercept {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : (describe (r := r) S z u).intercept = u := rfl

end
end DFVSGames.Inverse.RowErasureDescriptions

namespace DFVSGames.Inverse.RowErasureMatrix

open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions
open scoped BigOperators Classical

noncomputable section

def rowAdvice {ell m r : ℕ} (A : RowMap ell r) (M : Mat ell m) : Mat r m :=
  fun i j => ∑ a, A i a * M a j

def family (ell m r : ℕ) :
    SliceFamily (Mat ell m) (Vector ell) (RowMap ell r) (Mat r m)
      (Description ell m r) where
  advice := rowAdvice
  rowMap := fun d => d.1
  rowValue := fun d => d.2.1
  points := fun d => d.toSlice.points
  target := fun d M => evaluate M d.coefficient + d.intercept
  points_row := by
    intro d M hM
    have h : d.toSlice.Contains M := (Finset.mem_filter.mp hM).2
    funext i j
    exact h.1 i j

theorem family_agreement {ell m r : ℕ} (d : Description ell m r)
    (f : Mat ell m → Vector ell) :
    (family ell m r).agreement f d =
      d.toSlice.affineAgreement f d.coefficient d.intercept := by
  unfold SliceFamily.agreement Slice.affineAgreement
  apply Finset.expect_congr rfl
  intro M _
  change indicator (f M = evaluate M d.coefficient + d.intercept) = _
  by_cases h : f M = evaluate M d.coefficient + d.intercept
  · simp [indicator, h]
  · simp [indicator, h]

end
end DFVSGames.Inverse.RowErasureMatrix

namespace DFVSGames.Inverse.AffineWitness

abbrev F2 := ZMod 2

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem add_self_binary (c : C) : c + c = 0 := by
  have h : (1 : F2) + 1 = 0 := by decide
  calc
    c + c = (1 : F2) • c + (1 : F2) • c := by simp
    _ = ((1 : F2) + 1) • c := (add_smul _ _ _).symm
    _ = 0 := by rw [h, zero_smul]

def InSlice (A : C →ₗ[F2] R) (Z : Submodule F2 D)
    (M₀ M : D →ₗ[F2] C) : Prop :=
  A.comp M = A.comp M₀ ∧ ∀ w ∈ Z, M w = M₀ w

theorem translate_target (A : C →ₗ[F2] R) (Z : Submodule F2 D)
    (M₀ M : D →ₗ[F2] C) (hM : InSlice A Z M₀ M)
    (z w : D) (hw : w ∈ Z) (u : C) :
    M (z + w) + (u + M₀ w) = M z + u := by
  rw [map_add, hM.2 w hw]
  calc
    (M z + M₀ w) + (u + M₀ w) = (M z + u) + (M₀ w + M₀ w) := by
      ac_rfl
    _ = M z + u := by rw [add_self_binary, add_zero]

theorem no_affine_representative (e : D →ₗ[F2] F2) (Z : Submodule F2 D)
    (z : D) (h : ¬ ∃ w ∈ Z, e (z + w) = 1) :
    e z = 0 ∧ ∀ w ∈ Z, e w = 0 := by
  have scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide
  have hz : e z = 0 := by
    rcases scalar_cases (e z) with hz | hz
    · exact hz
    · exact False.elim (h ⟨0, Z.zero_mem, by simpa using hz⟩)
  refine ⟨hz, ?_⟩
  intro w hw
  rcases scalar_cases (e w) with hw0 | hw1
  · exact hw0
  · exact False.elim (h ⟨w, hw, by rw [map_add, hz, zero_add, hw1]⟩)

def shift (e : D →ₗ[F2] F2) (h : C) (M : D →ₗ[F2] C) : D →ₗ[F2] C :=
  M + e.smulRight h

@[simp] theorem shift_apply (e : D →ₗ[F2] F2) (h : C)
    (M : D →ₗ[F2] C) (x : D) : shift e h M x = M x + e x • h := rfl

@[simp] theorem shift_zero (e : D →ₗ[F2] F2) (M : D →ₗ[F2] C) :
    shift e 0 M = M := by
  ext x
  simp

theorem shift_add (e : D →ₗ[F2] F2) (h k : C) (M : D →ₗ[F2] C) :
    shift e (h + k) M = shift e h (shift e k M) := by
  ext x
  simp only [shift_apply, smul_add]
  ac_rfl

theorem shift_preserves_slice (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ M : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h : A.ker) (hM : InSlice A Z M₀ M) :
    InSlice A Z M₀ (shift e h M) := by
  constructor
  · ext x
    have hx := LinearMap.congr_fun hM.1 x
    have hh : A (h : C) = 0 := h.property
    simpa only [LinearMap.comp_apply, shift_apply, map_add, map_smul,
      hh, smul_zero, add_zero] using hx
  · intro w hw
    simp only [shift_apply, heZ w hw, zero_smul, add_zero]
    exact hM.2 w hw

theorem shift_preserves_target (e : D →ₗ[F2] F2) (z : D) (hz : e z = 0)
    (u h : C) (M : D →ₗ[F2] C) :
    shift e h M z + u = M z + u := by
  simp only [shift_apply, hz, zero_smul, add_zero]

theorem normalize (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (h : ∃ w ∈ Z, e (z + w) = 1) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  obtain ⟨w, hw, he⟩ := h
  exact ⟨z + w, u + M₀ w, he, fun M hM => translate_target A Z M₀ M hM z w hw u⟩

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse.AffineWitness

variable {D C R ι : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem columns_iff_span (q : ι → D) (t : ι → C)
    (M₀ M : D →ₗ[F2] C) (hM₀ : ∀ i, M₀ (q i) = t i) :
    (∀ i, M (q i) = t i) ↔
      ∀ w ∈ Submodule.span F2 (Set.range q), M w = M₀ w := by
  constructor
  · intro hM w hw

    apply LinearMap.eqOn_span (s := Set.range q) (x := w) ?_ hw
    rintro _ ⟨i, rfl⟩
    exact (hM i).trans (hM₀ i).symm
  · intro hM i
    exact (hM (q i) (Submodule.subset_span ⟨i, rfl⟩)).trans (hM₀ i)

theorem explicit_slice_iff (A : C →ₗ[F2] R) (S₀ : D →ₗ[F2] R)
    (q : ι → D) (t : ι → C) (M₀ M : D →ₗ[F2] C)
    (hrow : A.comp M₀ = S₀) (hcol : ∀ i, M₀ (q i) = t i) :
    (A.comp M = S₀ ∧ ∀ i, M (q i) = t i) ↔
      InSlice A (Submodule.span F2 (Set.range q)) M₀ M := by
  unfold InSlice
  rw [hrow, columns_iff_span q t M₀ M hcol]

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse

variable {H X Y : Type*} [AddGroup H] [AddGroup Y]

theorem folded_action_injective
    (shift : H → X → X)
    (shift_zero : ∀ x, shift 0 x = x)
    (shift_add : ∀ h k x, shift (h + k) x = shift h (shift k x))
    (embed : H → Y) (embed_injective : Function.Injective embed)
    (F target : X → Y)
    (folded : ∀ h x, F (shift h x) = F x + embed h)
    (target_invariant : ∀ h x, target (shift h x) = target x) :
    Function.Injective
      (fun a : H × {x : X // F x = target x} => shift a.1 a.2.val) := by
  intro a b hab
  have htarget : target a.2.val = target b.2.val := by
    calc
      target a.2.val = target (shift a.1 a.2.val) :=
        (target_invariant a.1 a.2.val).symm
      _ = target (shift b.1 b.2.val) := congrArg target hab
      _ = target b.2.val := target_invariant b.1 b.2.val
  have hfold : F a.2.val + embed a.1 = F b.2.val + embed b.1 := by
    calc
      F a.2.val + embed a.1 = F (shift a.1 a.2.val) :=
        (folded a.1 a.2.val).symm
      _ = F (shift b.1 b.2.val) := congrArg F hab
      _ = F b.2.val + embed b.1 := folded b.1 b.2.val
  rw [a.2.property, b.2.property, htarget] at hfold
  have hh : a.1 = b.1 := embed_injective (add_left_cancel hfold)
  have hx : a.2.val = b.2.val := by
    have hshift : shift a.1 a.2.val = shift a.1 b.2.val := by
      simpa only [hh] using hab
    have hinverse := congrArg (shift (-a.1)) hshift
    simpa only [← shift_add, neg_add_cancel, shift_zero] using hinverse
  exact Prod.ext hh (Subtype.ext hx)

theorem folded_action_card_mul_agreement_le
    [Fintype H] [Fintype X] [DecidableEq Y]
    (shift : H → X → X)
    (shift_zero : ∀ x, shift 0 x = x)
    (shift_add : ∀ h k x, shift (h + k) x = shift h (shift k x))
    (embed : H → Y) (embed_injective : Function.Injective embed)
    (F target : X → Y)
    (folded : ∀ h x, F (shift h x) = F x + embed h)
    (target_invariant : ∀ h x, target (shift h x) = target x) :
    Fintype.card H * Fintype.card {x : X // F x = target x} ≤
      Fintype.card X := by
  simpa only [Fintype.card_prod] using
    Fintype.card_le_of_injective
      (fun a : H × {x : X // F x = target x} => shift a.1 a.2.val)
      (folded_action_injective shift shift_zero shift_add embed embed_injective
        F target folded target_invariant)

end DFVSGames.Inverse

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AffineWitnessNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

abbrev Slice (A : C →ₗ[F2] R) (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) :=
  {M : D →ₗ[F2] C // InSlice A Z M₀ M}

def sliceShift (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h : A.ker) (M : Slice A Z M₀) :
    Slice A Z M₀ :=
  ⟨shift e h M, shift_preserves_slice e A Z M₀ M heZ h M.property⟩

theorem sliceShift_zero (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (M : Slice A Z M₀) :
    sliceShift e A Z M₀ heZ 0 M = M := by
  apply Subtype.ext
  exact shift_zero e M.val

theorem sliceShift_add (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h k : A.ker) (M : Slice A Z M₀) :
    sliceShift e A Z M₀ heZ (h + k) M =
      sliceShift e A Z M₀ heZ h (sliceShift e A Z M₀ heZ k M) := by
  apply Subtype.ext
  exact shift_add e (h : C) (k : C) M.val

theorem agreement_count_le [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (hno : ¬ ∃ w ∈ Z, e (z + w) = 1) :
    Nat.card A.ker * Nat.card {M : Slice A Z M₀ // F M = M.val z + u} ≤
      Nat.card (Slice A Z M₀) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype C := Fintype.ofFinite C
  let : Fintype (D →ₗ[F2] C) := Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  obtain ⟨hz, heZ⟩ := no_affine_representative e Z z hno
  have hcount := folded_action_card_mul_agreement_le
    (sliceShift e A Z M₀ heZ)
    (sliceShift_zero e A Z M₀ heZ)
    (sliceShift_add e A Z M₀ heZ)
    (fun h : A.ker => (h : C)) Subtype.val_injective
    (fun M : Slice A Z M₀ => F M)
    (fun M : Slice A Z M₀ => M.val z + u)
    (fun h M => hfold h M)
    (fun h M => shift_preserves_target e z hz u h M)
  simpa only [Nat.card_eq_fintype_card] using hcount

theorem normalize_of_good_count [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (hgood : Nat.card (Slice A Z M₀) <
      Nat.card A.ker * Nat.card {M : Slice A Z M₀ // F M = M.val z + u}) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  apply normalize e A Z M₀ z u
  by_contra hno
  exact (not_lt_of_ge (agreement_count_le e A Z M₀ z u F hfold hno)) hgood

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Matrix

namespace Slice

variable {ell m : ℕ}

def rowMap (S : Slice ell m) : Vector ell →ₗ[F2] Vector S.rows :=
  Matrix.mulVecLin S.rowCoefficient

def columnSpan (S : Slice ell m) : Submodule F2 (Vector m) :=
  Submodule.span F2 (Set.range S.columnCoefficient)

abbrev Directions (S : Slice ell m) :=
  (Vector m ⧸ S.columnSpan) →ₗ[F2] S.rowMap.ker

def directionMap (S : Slice ell m) (N : S.Directions) :
    Vector m →ₗ[F2] Vector ell :=
  S.rowMap.ker.subtype.comp (N.comp S.columnSpan.mkQ)

def directionMatrix (S : Slice ell m) (N : S.Directions) : Mat ell m :=
  LinearMap.toMatrix' (S.directionMap N)

theorem directionMatrix_injective (S : Slice ell m) :
    Function.Injective S.directionMatrix := by
  intro N P h
  have hmap : S.directionMap N = S.directionMap P :=
    LinearMap.toMatrix'.injective h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := S.columnSpan.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : Vector m →ₗ[F2] Vector ell => f v) hmap

theorem directionMatrix_row (S : Slice ell m) (N : S.Directions)
    (i : Fin S.rows) (j : Fin m) :
    (∑ a, S.rowCoefficient i a * S.directionMatrix N a j) = 0 := by
  have h := (N (S.columnSpan.mkQ (Pi.single j 1))).property
  have hi := congrFun h i
  change (∑ a, S.rowCoefficient i a *
    (N (S.columnSpan.mkQ (Pi.single j 1)) : Vector ell) a) = 0 at hi
  exact hi

theorem directionMatrix_column (S : Slice ell m) (N : S.Directions)
    (i : Fin S.columns) :
    evaluate (S.directionMatrix N) (S.columnCoefficient i) = 0 := by
  have hq : S.columnSpan.mkQ (S.columnCoefficient i) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero S.columnSpan).mpr
    exact Submodule.subset_span ⟨i, rfl⟩
  change (S.directionMatrix N) *ᵥ (S.columnCoefficient i) = 0
  rw [directionMatrix, LinearMap.toMatrix'_mulVec]
  simp [directionMap, hq]

theorem contains_add_direction (S : Slice ell m) (M : Mat ell m)
    (hM : S.Contains M) (N : S.Directions) :
    S.Contains (M + S.directionMatrix N) := by
  constructor
  · intro i j
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hM.1 i j, S.directionMatrix_row N i j, add_zero]
  · intro i
    have hd := S.directionMatrix_column N i
    change evaluate (M + S.directionMatrix N) (S.columnCoefficient i) = _
    have he : evaluate (M + S.directionMatrix N) (S.columnCoefficient i) =
        evaluate M (S.columnCoefficient i) +
          evaluate (S.directionMatrix N) (S.columnCoefficient i) := by
      ext a
      simp [evaluate, add_mul, Finset.sum_add_distrib]
    rw [he, hM.2 i, hd, add_zero]

def directionEmbedding (S : Slice ell m) (M : Mat ell m) (hM : S.Contains M) :
    S.Directions ↪ S.points where
  toFun N := ⟨M + S.directionMatrix N, by
    simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.contains_add_direction M hM N⟩
  inj' := by
    intro N P h
    apply S.directionMatrix_injective
    exact add_left_cancel (congrArg Subtype.val h)

end Slice
end
end DFVSGames.Inverse.Shortcode

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical Matrix

namespace Slice

variable {ell m : ℕ}

theorem row_equations_iff (S : Slice ell m) (M : Mat ell m) :
    (∀ i j, (∑ a, S.rowCoefficient i a * M a j) = S.rowValue i j) ↔
      S.rowMap.comp (Matrix.toLin' M) = Matrix.toLin' S.rowValue := by
  let A : Matrix (Fin S.rows) (Fin ell) F2 := S.rowCoefficient
  let B : Matrix (Fin S.rows) (Fin m) F2 := S.rowValue
  change (∀ i j, (∑ a, A i a * M a j) = B i j) ↔
    (Matrix.toLin' A).comp (Matrix.toLin' M) = Matrix.toLin' B
  constructor
  · intro h
    have hm : A * M = B := by
      ext i j
      exact h i j
    rw [← Matrix.toLin'_mul, hm]
  · intro h
    have hm : A * M = B := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul]
      exact h
    intro i j
    exact congrFun (congrFun hm i) j

theorem contains_iff_inSlice (S : Slice ell m) (M₀ : Mat ell m)
    (hM₀ : S.Contains M₀) (M : Mat ell m) :
    S.Contains M ↔
      AffineWitness.InSlice S.rowMap S.columnSpan
        (Matrix.toLin' M₀) (Matrix.toLin' M) := by
  have hrow₀ := (S.row_equations_iff M₀).mp hM₀.1
  have hcol₀ : ∀ i, Matrix.toLin' M₀ (S.columnCoefficient i) =
      S.columnValue i := hM₀.2
  have heq := AffineWitness.explicit_slice_iff S.rowMap
    (Matrix.toLin' S.rowValue) S.columnCoefficient S.columnValue
    (Matrix.toLin' M₀) (Matrix.toLin' M) hrow₀ hcol₀
  constructor
  · intro hM
    exact heq.mp ⟨(S.row_equations_iff M).mp hM.1, hM.2⟩
  · intro hM
    have h := heq.mpr hM
    exact ⟨(S.row_equations_iff M).mpr h.1, h.2⟩

def linearSliceEquiv (S : Slice ell m) (M₀ : Mat ell m)
    (hM₀ : S.Contains M₀) :
    S.points ≃ AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀) where
  toFun M := ⟨Matrix.toLin' M.val,
    (S.contains_iff_inSlice M₀ hM₀ M.val).mp (by
      simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using M.property)⟩
  invFun N := ⟨LinearMap.toMatrix' N.val, by
    simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]
    apply (S.contains_iff_inSlice M₀ hM₀ _).mpr
    simpa only [Matrix.toLin'_toMatrix'] using N.property⟩
  left_inv M := by
    apply Subtype.ext
    exact LinearMap.toMatrix'_toLin' M.val
  right_inv N := by
    apply Subtype.ext
    exact Matrix.toLin'_toMatrix' N.val

theorem affineAgreement_eq_of_target_eq (S : Slice ell m)
    (f : Mat ell m → Vector ell) (z z' : Vector m) (u u' : Vector ell)
    (htarget : ∀ M, S.Contains M → evaluate M z' + u' = evaluate M z + u) :
    S.affineAgreement f z' u' = S.affineAgreement f z u := by
  unfold affineAgreement
  apply Finset.expect_congr rfl
  intro M hM
  have hcontains : S.Contains M := by
    simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using hM
  rw [htarget M hcontains]

theorem affineAgreement_eq_of_linear_target_eq (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z z' : Vector m) (u u' : Vector ell)
    (htarget : ∀ M, AffineWitness.InSlice S.rowMap S.columnSpan
      (Matrix.toLin' M₀) M → M z' + u' = M z + u) :
    S.affineAgreement f z' u' = S.affineAgreement f z u := by
  apply S.affineAgreement_eq_of_target_eq f z z' u u'
  intro M hM
  exact htarget (Matrix.toLin' M) ((S.contains_iff_inSlice M₀ hM₀ M).mp hM)

end Slice
end
end DFVSGames.Inverse.Shortcode

namespace DFVSGames.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem normalize_of_density [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (η : ℝ)
    (hgood : η ≤
      (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) /
        (Nat.card (Slice A Z M₀) : ℝ))
    (hsize : 1 < η * (Nat.card A.ker : ℝ)) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype C := Fintype.ofFinite C
  let : Fintype (D →ₗ[F2] C) := Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  let : Nonempty (Slice A Z M₀) := ⟨⟨M₀, rfl, fun _ _ => rfl⟩⟩
  have hpos : (0 : ℝ) < (Nat.card (Slice A Z M₀) : ℝ) := by
    exact_mod_cast Nat.card_pos (α := Slice A Z M₀)
  have hmass := (le_div_iff₀ hpos).mp hgood
  have hmul := mul_le_mul_of_nonneg_right hmass
    (Nat.cast_nonneg (α := ℝ) (Nat.card A.ker))
  have hstrict := mul_lt_mul_of_pos_right hsize hpos
  apply normalize_of_good_count e A Z M₀ z u F hfold
  have hreal : (Nat.card (Slice A Z M₀) : ℝ) <
      (Nat.card A.ker : ℝ) *
        (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) := by
    nlinarith only [hmul, hstrict]
  exact_mod_cast hreal

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse.AffineWitness

theorem first_bit_witness {m ℓ r : ℕ}
    (e : (Fin m → F2) →ₗ[F2] F2)
    (A : (Fin ℓ → F2) →ₗ[F2] (Fin r → F2))
    (Z : Submodule F2 (Fin m → F2))
    (M₀ : (Fin m → F2) →ₗ[F2] (Fin ℓ → F2))
    (z : Fin m → F2) (u : Fin ℓ → F2)
    (F : ((Fin m → F2) →ₗ[F2] (Fin ℓ → F2)) → (Fin ℓ → F2))
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (α : ℝ) (hα : 0 < α)
    (hgood : α / 2 ≤
      (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) /
        (Nat.card (Slice A Z M₀) : ℝ))
    (hsmall : 1 / (2 : ℝ) ^ (ℓ - r) < α / 8) :
    ∃ z' : Fin m → F2, ∃ u' : Fin ℓ → F2, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  have hpow : (0 : ℝ) < 2 ^ (ℓ - r) := pow_pos (by norm_num) _
  have hsep := (div_lt_iff₀ hpow).mp hsmall
  have hk : (2 : ℝ) ^ (ℓ - r) ≤ (Nat.card A.ker : ℝ) := by
    exact_mod_cast binary_kernel_card_lower A
  have hscale := mul_le_mul_of_nonneg_left hk hα.le
  have hsize : 1 < (α / 2) * (Nat.card A.ker : ℝ) := by
    nlinarith only [hsep, hscale]
  exact normalize_of_density e A Z M₀ z u F hfold (α / 2) hgood hsize

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse

open scoped BigOperators

variable {X Y : Type*}

theorem card_finset_subtype_eq_filter_card (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    Nat.card {x : s // p x.val} = (s.filter p).card := by
  classical
  let e : {x : s // p x.val} ≃ ↥(s.filter p) :=
    { toFun := fun x =>
        ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
      invFun := fun x =>
        ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
          (Finset.mem_filter.mp x.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard _)

theorem finset_expect_indicator_eq_card_ratio (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {x : s // p x.val} : ℝ) / (Nat.card s : ℝ) := by
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole,
    card_finset_subtype_eq_filter_card, Nat.card_eq_finsetCard]

theorem nat_card_subtype_equiv (e : X ≃ Y) (p : X → Prop) (q : Y → Prop)
    (h : ∀ x, p x ↔ q (e x)) :
    Nat.card {x : X // p x} = Nat.card {y : Y // q y} :=
  Nat.card_congr (e.subtypeEquiv h)

theorem finset_expect_indicator_eq_card_ratio_of_equiv (s : Finset X)
    (p : X → Prop) [DecidablePred p] (e : ↥s ≃ Y) (q : Y → Prop)
    (h : ∀ x : s, p x.val ↔ q (e x)) :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {y : Y // q y} : ℝ) / (Nat.card Y : ℝ) := by
  rw [finset_expect_indicator_eq_card_ratio,
    nat_card_subtype_equiv e (fun x => p x.val) q h, Nat.card_congr e]

end DFVSGames.Inverse

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

variable {ell m : ℕ}

def functionalRow (e : Vector m →ₗ[F2] F2) : Vector m :=
  fun j => e (Pi.single j 1)

theorem toMatrix_shift (e : Vector m →ₗ[F2] F2) (h : Vector ell)
    (M : Mat ell m) :
    LinearMap.toMatrix' (AffineWitness.shift e h (Matrix.toLin' M)) =
      M + rankOne h (functionalRow e) := by
  rw [AffineWitness.shift, map_add, LinearMap.toMatrix'_toLin']
  congr 1
  ext i j
  simp only [LinearMap.toMatrix'_apply, LinearMap.smulRight_apply,
    Pi.smul_apply, smul_eq_mul, rankOne, functionalRow, mul_comm]

namespace Slice

theorem affineAgreement_eq_linear_ratio (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) :
    S.affineAgreement f z u =
      (Nat.card {N : AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀) //
        f (LinearMap.toMatrix' N.val) = N.val z + u} : ℝ) /
      (Nat.card (AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀)) : ℝ) := by
  unfold affineAgreement
  apply finset_expect_indicator_eq_card_ratio_of_equiv S.points
    (fun M => f M = evaluate M z + u) (S.linearSliceEquiv M₀ hM₀)
    (fun N => f (LinearMap.toMatrix' N.val) = N.val z + u)
  intro M
  change (f M.val = evaluate M.val z + u) ↔
    (f (LinearMap.toMatrix' (Matrix.toLin' M.val)) = Matrix.toLin' M.val z + u)
  rw [LinearMap.toMatrix'_toLin']
  rfl

theorem first_bit_normalization (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (e : Vector m →ₗ[F2] F2)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell)
    (hfold : ∀ (h : S.rowMap.ker) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (α : ℝ) (hα : 0 < α) (hgood : α / 2 ≤ S.affineAgreement f z u)
    (hsmall : 1 / (2 : ℝ) ^ (ell - S.rows) < α / 8) :
    ∃ z' : Vector m, ∃ u' : Vector ell, e z' = 1 ∧
      S.affineAgreement f z' u' = S.affineAgreement f z u ∧
      ∀ M, S.Contains M → evaluate M z' + u' = evaluate M z + u := by
  let F : (Vector m →ₗ[F2] Vector ell) → Vector ell :=
    fun N => f (LinearMap.toMatrix' N)
  have hfold' : ∀ (h : S.rowMap.ker) N,
      F (AffineWitness.shift e h N) = F N + h := by
    intro h N
    have hs : LinearMap.toMatrix' (AffineWitness.shift e h N) =
        LinearMap.toMatrix' N + rankOne h (functionalRow e) := by
      simpa only [Matrix.toLin'_toMatrix'] using toMatrix_shift e h (LinearMap.toMatrix' N)
    exact (congrArg f hs).trans (hfold h (LinearMap.toMatrix' N))
  have hgood' := hgood
  rw [S.affineAgreement_eq_linear_ratio M₀ hM₀ f z u] at hgood'
  obtain ⟨z', u', he, ht⟩ := AffineWitness.first_bit_witness e S.rowMap S.columnSpan
    (Matrix.toLin' M₀) z u F hfold' α hα hgood' hsmall
  refine ⟨z', u', he, S.affineAgreement_eq_of_linear_target_eq M₀ hM₀ f z z' u u' ht, ?_⟩
  intro M hM
  exact ht (Matrix.toLin' M) ((S.contains_iff_inSlice M₀ hM₀ M).mp hM)

end Slice
end
end DFVSGames.Inverse.Shortcode

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ActualGoodRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualGoodRows

open Reduction
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

def goodRowMass (rstar s r : ℕ) : ℝ :=
  10 * ActualSpectral.eta rstar ^ 2 / (2 : ℝ) ^ (s * r)

end
end DFVSGames.Decoder.ActualGoodRows

namespace DFVSGames.Decoder.ConstantSelection

open DFVSGames.Foundations.Information
open SparseLaw

noncomputable section

def visibleMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  α * g₀ / (8 * (2 : ℝ) ^ (ell * r))

def conditionalMass (α : ℝ) (ell r : ℕ) : ℝ :=
  (α / 8) ^ 2 / (2 : ℝ) ^ (ell * r) / (2 : ℝ) ^ r

def decodingMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r * conditionalMass α ell r

def variationBudget (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r / (1 + α / 4)

end
end DFVSGames.Decoder.ConstantSelection

namespace DFVSGames.Inverse.RowErasure

noncomputable section

variable {X Y A S D : Type*}

def SliceFamily.chosenDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) : D :=
  Classical.choose hgood

theorem SliceFamily.chosenDescription_spec (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.rowMap (F.chosenDescription f α a s hgood) = a ∧
      F.rowValue (F.chosenDescription f α a s hgood) = s ∧
      (F.points (F.chosenDescription f α a s hgood)).Nonempty ∧
      α / 2 ≤ F.agreement f (F.chosenDescription f α a s hgood) :=
  Classical.choose_spec hgood

def SliceFamily.selectedDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Option D := by
  classical
  exact if hgood : F.GoodAdvice f α a s then
    some (F.chosenDescription f α a s hgood) else none

def SliceFamily.selectedEvent (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧ x ∈ F.points d

def SliceFamily.selectedMatch (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧
    x ∈ F.points d ∧ f x = F.target d x

end
end DFVSGames.Inverse.RowErasure

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSliceUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.RowErasureDescriptions

open DFVSGames.Inverse.Shortcode

def Description.withTarget {ell m r : ℕ} (d : Description ell m r)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (d.1, d.2.1, d.2.2.1, d.2.2.2.1, z, u)

end DFVSGames.Inverse.RowErasureDescriptions

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_VisibleTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.VisibleTransfer

open scoped BigOperators

noncomputable section

variable {Ω D : Type*} [Fintype Ω] [Fintype D]

def fiberEvent (observe : Ω → D) (d : D) (event : Ω → Bool) : Ω → Bool := by
  classical
  exact fun x => decide (observe x = d) && event x

end
end DFVSGames.Decoder.VisibleTransfer

namespace DFVSGames.Decoder.UniformFibers

open scoped BigOperators Classical

noncomputable section

variable {Ω D Y : Type*}

def selectedFiberEquiv (observe : Ω → D) (d : D) (slice : Ω → Bool)
    (e : Y ≃ {x : Ω // observe x = d}) :
    {x : Ω // VisibleTransfer.fiberEvent observe d slice x = true} ≃
      {y : Y // slice (e y).val = true} where
  toFun x := by
    have hx : observe x.val = d ∧ slice x.val = true := by
      simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using x.property
    refine ⟨e.symm ⟨x.val, hx.1⟩, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hx.2
  invFun y := ⟨(e y.val).val, by
    simp only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(e y.val).property, y.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    simp only [Equiv.apply_symm_apply]
  right_inv y := by
    apply Subtype.ext
    exact e.symm_apply_apply y.val

end
end DFVSGames.Decoder.UniformFibers

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_StageData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

def compress (A : Submodule K V) (B : Submodule K W) (Y : W →ₗ[K] V) :
    B →ₗ[K] V ⧸ A := A.mkQ.comp (Y.comp B.subtype)

end DFVSGames.Appendix.Level.LinearRank

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_DegreeCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Appendix.DegreeCover

abbrev F2 := ZMod 2
variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

@[simp] theorem binary_add_self (v : V) : v + v = 0 := by
  have h : (1 + 1 : F2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : F2 => c • v) h

@[simp] theorem binary_neg (v : V) : -v = v := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact binary_add_self v

end DFVSGames.Appendix.DegreeCover

namespace DFVSGames.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

def Hybrid (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) : Prop :=
  A ≤ LinearMap.range Y ∧ A.comap Y ≤ B

def compress (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) :
    B →ₗ[K] (V ⧸ A) := A.mkQ.comp (Y.domRestrict B)

@[simp] theorem compress_apply (Y : W →ₗ[K] V) (A : Submodule K V)
    (B : Submodule K W) (b : B) : compress Y A B b = A.mkQ (Y b) := rfl

variable [FiniteDimensional K W] [FiniteDimensional K V]

def A5PairSurvives (X Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W)
    (p : Submodule K V × Submodule K W) : Prop :=
  Hybrid Y p.1 p.2 ∧ Disjoint p.1 (LinearMap.range X) ∧
  p.1 ⊔ LinearMap.range X = A ∧ p.2 ⊔ LinearMap.ker X = ⊤ ∧
  p.2 ⊓ LinearMap.ker X = B ∧
  RankAdditivity.RankBelow (compress X p.1 p.2) (compress Y p.1 p.2)

abbrev A4Index := Σ A₀ : Submodule K V, Σ B₀ : Submodule K W, B₀ →ₗ[K] (V ⧸ A₀)

def A4Survives (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W)
    (p : A4Index (K := K) (W := W) (V := V)) : Prop :=
  p.1 ≤ A ∧ B ≤ p.2.1 ∧ Hybrid Y p.1 p.2.1 ∧
    LinearMap.ker p.2.2 = B.comap p.2.1.subtype ∧
    LinearMap.range p.2.2 = A.map p.1.mkQ ∧
    RankAdditivity.RankBelow p.2.2 (compress Y p.1 p.2.1)

end DFVSGames.Appendix.LinearIdentities

namespace DFVSGames.Appendix.BinaryA4

open LinearIdentities

abbrev F2 := DegreeCover.F2

end DFVSGames.Appendix.BinaryA4

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CoordinateTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Appendix.CoordinateTransport

noncomputable section

variable {𝕜 E F : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

def complementRangeEquiv (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) : P ≃ₗ[𝕜] X.range :=
  (X.ker.quotientEquivOfIsCompl P hP).symm.trans X.quotKerEquivRange

@[simp] theorem complementRangeEquiv_apply (X : E →ₗ[𝕜] F)
    (P : Submodule 𝕜 E) (hP : IsCompl X.ker P) (p : P) :
    (complementRangeEquiv X P hP p : F) = X p := by
  rfl

def domainEquiv (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) : (X.range × X.ker) ≃ₗ[𝕜] E :=
  (LinearEquiv.prodCongr (complementRangeEquiv X P hP).symm
    (LinearEquiv.refl 𝕜 X.ker)).trans (P.prodEquivOfIsCompl X.ker hP.symm)

@[simp] theorem apply_domainEquiv (X : E →ₗ[𝕜] F)
    (P : Submodule 𝕜 E) (hP : IsCompl X.ker P) (u : X.range) (k : X.ker) :
    X (domainEquiv X P hP (u, k)) = (u : F) := by
  change X ((complementRangeEquiv X P hP).symm u + (k : E)) = (u : F)
  rw [map_add, show X (k : E) = 0 from k.property, add_zero]
  have h := congrArg (fun v : X.range => (v : F))
    ((complementRangeEquiv X P hP).apply_symm_apply u)
  simpa only [complementRangeEquiv_apply] using h

def codomainEquiv (X : E →ₗ[𝕜] F) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) : (X.range × C) ≃ₗ[𝕜] F :=
  X.range.prodEquivOfIsCompl C hC

theorem canonical_block (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) (u : X.range) (k : X.ker) :
    (codomainEquiv X C hC).symm (X (domainEquiv X P hP (u, k))) = (u, 0) := by
  rw [apply_domainEquiv]
  exact Submodule.prodEquivOfIsCompl_symm_apply_left X.range C hC u

@[simp] theorem domainEquiv_zero_left (X : E →ₗ[𝕜] F)
    (P : Submodule 𝕜 E) (hP : IsCompl X.ker P) (k : X.ker) :
    domainEquiv X P hP (0, k) = (k : E) := by
  change ((complementRangeEquiv X P hP).symm 0 : E) + (k : E) = (k : E)
  simp

theorem quotient_coordinates (X : E →ₗ[𝕜] F) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) (v : F) :
    X.range.quotientEquivOfIsCompl C hC (X.range.mkQ v) =
      ((codomainEquiv X C hC).symm v).2 := by
  simp [codomainEquiv, Submodule.prodEquivOfIsCompl_symm_apply]

def toBlocks (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C) :
    (E →ₗ[𝕜] F) ≃ₗ[𝕜] ((X.range × X.ker) →ₗ[𝕜] (X.range × C)) :=
  LinearEquiv.arrowCongr (domainEquiv X P hP).symm (codomainEquiv X C hC).symm

@[simp] theorem toBlocks_apply (X Y : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C)
    (u : X.range) (k : X.ker) :
    toBlocks X P hP C hC Y (u, k) =
      (codomainEquiv X C hC).symm (Y (domainEquiv X P hP (u, k))) := by
  rfl

theorem compressed_toBlocks (X Y : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C)
    (k : X.ker) :
    (toBlocks X P hP C hC Y (0, k)).2 =
      X.range.quotientEquivOfIsCompl C hC (X.range.mkQ (Y k)) := by
  rw [toBlocks_apply, domainEquiv_zero_left, quotient_coordinates]

theorem toBlocks_base (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C) :
    toBlocks X P hP C hC X =
      (LinearMap.inl 𝕜 X.range C).comp (LinearMap.fst 𝕜 X.range X.ker) := by
  apply LinearMap.ext
  intro p
  exact canonical_block X P hP C hC p.1 p.2

section RankTransport

variable {U V : Type*} [AddCommGroup U] [Module 𝕜 U]
  [AddCommGroup V] [Module 𝕜 V]

def rangeTransport (e : E ≃ₗ[𝕜] U) (f : F ≃ₗ[𝕜] V) (Y : E →ₗ[𝕜] F) :
    Y.range ≃ₗ[𝕜] (LinearEquiv.arrowCongr e f Y).range where
  toFun y := ⟨f y, by
    obtain ⟨w, hw⟩ := y.property
    exact ⟨e w, by simp [LinearEquiv.arrowCongr_apply, hw]⟩⟩
  invFun z := ⟨f.symm z, by
    obtain ⟨u, hu⟩ := z.property
    refine ⟨e.symm u, ?_⟩
    have h := congrArg f.symm hu
    simpa only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply] using h⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  map_add' y z := by apply Subtype.ext; simp
  map_smul' c y := by apply Subtype.ext; simp

theorem finrank_range_transport (e : E ≃ₗ[𝕜] U) (f : F ≃ₗ[𝕜] V)
    (Y : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (LinearEquiv.arrowCongr e f Y).range =
      Module.finrank 𝕜 Y.range :=
  (rangeTransport e f Y).finrank_eq.symm

end RankTransport

theorem finrank_toBlocks (X Y : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C) :
    Module.finrank 𝕜 (toBlocks X P hP C hC Y).range =
      Module.finrank 𝕜 Y.range :=
  finrank_range_transport (domainEquiv X P hP).symm (codomainEquiv X C hC).symm Y

end

end DFVSGames.Appendix.CoordinateTransport

namespace DFVSGames.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

noncomputable def generators (S : Submodule K V) (k : ℕ)
    (h : finrank K S = k) : Fin k → V :=
  fun i => (Module.finBasisOfFinrankEq K S h i : V)

variable {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]

def quotientImageMap (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) :
    (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y :=
  let f := (LinearMap.ker Y).liftQ X hker
  f.codRestrict (LinearMap.range Y) (fun q => himage (by
    rw [← Submodule.range_liftQ (LinearMap.ker Y) X hker]
    exact LinearMap.mem_range_self f q))

end DFVSGames.Appendix.SubspaceCounting

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix

section ProductEquivalences

variable {R A U B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup U] [Module R U]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

def leftRangeEquiv : B ≃ₗ[R] LinearMap.range (LinearMap.inl R B C) where
  toFun b := ⟨(b, 0), ⟨b, rfl⟩⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := hx
    rfl
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

@[simp] theorem leftRangeEquiv_coe (b : B) :
    (leftRangeEquiv (R := R) (C := C) b : B × C) = (b, 0) := rfl

def quotientRightMap :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) →ₗ[R] U :=
  (LinearMap.range (LinearMap.inl R A U)).liftQ (LinearMap.snd R A U) (by
    rintro x ⟨a, rfl⟩
    rfl)

@[simp] theorem quotientRightMap_mkQ (x : A × U) :
    quotientRightMap (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

def quotientRightEquiv :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) ≃ₗ[R] U where
  toLinearMap := quotientRightMap
  invFun u := (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u)
  left_inv := by
    intro q
    obtain ⟨⟨a, u⟩, rfl⟩ := (LinearMap.range (LinearMap.inl R A U)).mkQ_surjective q
    change (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) =
      (LinearMap.range (LinearMap.inl R A U)).mkQ (a, u)
    have hz : (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
    calc
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) +
          (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) := by rw [hz, zero_add]
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ ((a, 0) + (0, u)) :=
        (map_add _ _ _).symm
      _ = _ := by simp
  right_inv _ := rfl

@[simp] theorem quotientRightEquiv_mkQ (x : A × U) :
    quotientRightEquiv (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

def productFrequencyEquiv :
    ((LinearMap.range (LinearMap.inl R B C)) →ₗ[R]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U))) ≃ (B →ₗ[R] U) where
  toFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).toLinearMap)
  invFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).symm.toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).symm.toLinearMap)
  left_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  right_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

end ProductEquivalences

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_A4IndexCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Appendix.A4IndexCount

section Generic

variable {K : Type*} [Field K]

def factorViaRange {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) :
    X.range →ₗ[K] T :=
  (X.ker.liftQ P hker).comp X.quotKerEquivRange.symm.toLinearMap

variable {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def quotientRestriction (B B0 : Submodule K W) : B0 →ₗ[K] (W ⧸ B) :=
  B.mkQ.comp B0.subtype

theorem ker_quotientRestriction (B B0 : Submodule K W) :
    (quotientRestriction B B0).ker = B.comap B0.subtype := by
  ext b
  change B.mkQ (b : W) = 0 ↔ (b : W) ∈ B
  exact Submodule.Quotient.mk_eq_zero B

def aToRange (A A0 : Submodule K V) (B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hR : X.range = A.map A0.mkQ) : A →ₗ[K] X.range :=
  (A0.mkQ.comp A.subtype).codRestrict X.range (by
    intro a
    rw [hR]
    exact Submodule.mem_map.mpr ⟨a.val, a.property, rfl⟩)

def encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) : A →ₗ[K] (W ⧸ B) :=
  (factorViaRange X (quotientRestriction B B0)
    (hK.trans (ker_quotientRestriction B B0).symm).le).comp
      (aToRange A A0 B0 X hR)

def Valid (A : Submodule K V) (B : Submodule K W)
    (p : LinearIdentities.A4Index (K := K) (W := W) (V := V)) : Prop :=
  p.1 ≤ A ∧ B ≤ p.2.1 ∧ p.2.2.ker = B.comap p.2.1.subtype ∧
    p.2.2.range = A.map p.1.mkQ

abbrev Index (A : Submodule K V) (B : Submodule K W) :=
  {p : LinearIdentities.A4Index (K := K) (W := W) (V := V) // Valid A B p}

def encode (A : Submodule K V) (B : Submodule K W)
    (p : Index A B) : A →ₗ[K] (W ⧸ B) :=
  encodeFixed A p.val.1 B p.val.2.1 p.val.2.2
    p.property.2.2.1 p.property.2.2.2

end Generic

end DFVSGames.Appendix.A4IndexCount

end

noncomputable section

namespace DFVSGames.Appendix.RestrictionTransport

open scoped BigOperators

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

theorem exists_range_preimage_inline_RestrictionTransport (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (h : f.range ≤ g.range) (x : P) : ∃ y : Q, g y = f x := h ⟨x, rfl⟩

def sameRangeEquiv (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) : P ≃ₗ[K] Q := by
  let fw (x : P) := Classical.choose (exists_range_preimage_inline_RestrictionTransport f g (le_of_eq h) x)
  let bw (y : Q) := Classical.choose (exists_range_preimage_inline_RestrictionTransport g f (le_of_eq h.symm) y)
  have hfw (x : P) : g (fw x) = f x :=
    Classical.choose_spec (exists_range_preimage_inline_RestrictionTransport f g (le_of_eq h) x)
  have hbw (y : Q) : f (bw y) = g y :=
    Classical.choose_spec (exists_range_preimage_inline_RestrictionTransport g f (le_of_eq h.symm) y)
  exact
    { toFun := fw
      invFun := bw
      left_inv := by
        intro x
        apply hf
        rw [hbw, hfw]
      right_inv := by
        intro y
        apply hg
        rw [hfw, hbw]
      map_add' := by
        intro x y
        apply hg
        simp only [map_add, hfw]
      map_smul' := by
        intro c x
        change fw (c • x) = c • fw x
        apply hg
        simp only [map_smul, hfw] }

end SameRange

end DFVSGames.Appendix.RestrictionTransport

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_A5Scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace DFVSGames.Appendix.A5Scalar

def positiveSum (q : ℝ) (n m k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
    if 1 ≤ i + j + k then q ^ (i + j + k) else 0

end DFVSGames.Appendix.A5Scalar
end

namespace DFVSGames.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def horizontal (B : Submodule K V) : Submodule K (V × K) := B.prod ⊥
def hKernel (S : Submodule K (V × K)) : Submodule K V := S.comap (LinearMap.inl K V K)

def scalarMap {Q : Type*} [AddCommGroup Q] [Module K Q] (q : Q) : K →ₗ[K] Q where
  toFun t := t • q
  map_add' a b := add_smul a b q
  map_smul' a b := by change (a*b) • q = a • (b • q); exact mul_smul a b q

def extension (B : Submodule K V) (q : V ⧸ B) : Submodule K (V × K) :=
  LinearMap.ker (B.mkQ.comp (LinearMap.fst K V K) -
    (scalarMap q).comp (LinearMap.snd K V K))

theorem extension_mem (B : Submodule K V) (q : V ⧸ B) (x : V) (t : K) :
    (x,t) ∈ extension B q ↔ B.mkQ x = t • q := by
  change B.mkQ x - t • q = 0 ↔ _
  exact sub_eq_zero

theorem mkQ_eq_smul_iff (B : Submodule K V) (x v : V) (t : K) :
    B.mkQ x = t • B.mkQ v ↔ x - t • v ∈ B := by
  have he : B.mkQ (x-t•v) = B.mkQ x - t•B.mkQ v := by simp only [map_sub, map_smul]
  rw [← sub_eq_zero, ← he]
  change (x-t•v ∈ LinearMap.ker B.mkQ) ↔ _
  rw [Submodule.ker_mkQ]

local instance subspaceFintype [Finite V] : Fintype (Submodule K V) := by
  classical
  letI := Fintype.ofFinite V
  exact Fintype.ofInjective (fun B : Submodule K V => (B : Set V)) SetLike.coe_injective
local instance quotientFintype [Finite V] (B : Submodule K V) : Fintype (V ⧸ B) := by
  letI : Finite (V ⧸ B) := Finite.of_surjective B.mkQ B.mkQ_surjective
  exact Fintype.ofFinite _

def weightedTotal [Finite V] (w : Nat → ℤ) : ℤ := ∑ B : Submodule K V, w (Module.finrank K B)

def mobiusWeight (q : Nat) : Nat → ℤ
  | 0 => 1
  | n+1 => -(q:ℤ)^n * mobiusWeight q n

def mobiusTotal [Finite K] [Finite V] : ℤ :=
  weightedTotal (K:=K) (V:=V) (mobiusWeight (Nat.card K))

end
end DFVSGames.Appendix.SubspaceExtensions

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SubmoduleInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Appendix.SubmoduleInterval
open Module
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

def lowerIntervalEquiv (I : Submodule 𝕜 V) :
    {A : Submodule 𝕜 V // A ≤ I} ≃ Submodule 𝕜 I where
  toFun A := A.val.comap I.subtype
  invFun B := ⟨B.map I.subtype, by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
    exact b.property⟩
  left_inv A := by
    apply Subtype.ext
    change (A.val.comap I.subtype).map I.subtype = A.val
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
      exact hb
    · intro hx
      exact Submodule.mem_map.mpr ⟨⟨x, A.property hx⟩, hx, rfl⟩
  right_inv B := by
    change (B.map I.subtype).comap I.subtype = B
    ext b
    constructor
    · intro hb
      change (b : V) ∈ B.map I.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨c, hc, hcb⟩
      have h : c = b := Subtype.ext hcb
      simpa only [h] using hc
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩

def lowerIntervalSpaceEquiv (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    A.val ≃ₗ[𝕜] A.val.comap I.subtype where
  toFun a := ⟨⟨a.val, A.property a.property⟩, a.property⟩
  invFun b := ⟨b.val.val, b.property⟩
  left_inv _a := Subtype.ext rfl
  right_inv _b := Subtype.ext (Subtype.ext rfl)
  map_add' _a _b := Subtype.ext (Subtype.ext rfl)
  map_smul' _c _a := Subtype.ext (Subtype.ext rfl)

open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance submoduleFinite [Finite V] : Finite (Submodule 𝕜 V) :=
  Finite.of_injective (fun S : Submodule 𝕜 V => (S : Set V)) SetLike.coe_injective

noncomputable def lowerWeightedTotal [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) : ℤ := by
  classical
  letI := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  exact ∑ A : {A : Submodule 𝕜 V // A ≤ I}, w (finrank 𝕜 A.val)

end DFVSGames.Appendix.SubmoduleInterval

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_UpperMobius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace DFVSGames.Appendix.DyadicError

def quarterSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (1/4 : ℝ)^i

def quarterError (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    if i=0 ∧ j=0 then 0 else (1/4 : ℝ)^(i+j)

def dyadicError (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
    if i=0 ∧ j=0 then 0 else (1/2 : ℝ)^(3*d*(i+j))

end DFVSGames.Appendix.DyadicError
end

noncomputable section
namespace DFVSGames.Appendix.BadConvolution
open scoped BigOperators
open Module (finrank)
attribute [local instance] Classical.propDecidable

variable {W V : Type*}
  [AddCommGroup W]
  [AddCommGroup V]

def mobius (i : ℕ) : ℝ := (-1:ℝ)^i * 2^(i.choose 2)

end DFVSGames.Appendix.BadConvolution
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_A5ForwardIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace DFVSGames.Appendix.A5WeightedReindex

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [Fintype β]

def fiber (result : α → β) (i j : α → ℕ) (b : β) (r s : ℕ) : Finset α :=
  Finset.univ.filter (fun a => result a = b ∧ i a = r ∧ j a = s)

end DFVSGames.Appendix.A5WeightedReindex
end

end OAI
end


