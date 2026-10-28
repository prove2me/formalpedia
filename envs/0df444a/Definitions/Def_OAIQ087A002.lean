-- Prove2me | Definitions.Def_OAIQ087A002
-- name    : OAIQ087A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:16:26.614128+00:00
-- url     : https://prove2.me/theorems/384afa50-0027-4b11-8b9e-cdda9b7f0eb3
-- title:
--   Definitions bundle OAIQ087A002 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 317 declarations of OpenAI's Lean: 185 definitions, 20 inductive types or structures, 4 instances and 108 theorems. The definitions and types are `OAI.MaxCutGames.Decoder.ActualGoodRows.goodRowMass`, `OAI.MaxCutGames.Decoder.ActualSpectral.eta`, `OAI.MaxCutGames.Decoder.ConstantSelection.conditionalMass`, `OAI.MaxCutGames.Decoder.ConstantSelection.decodingMass`, `OAI.MaxCutGames.Decoder.ConstantSelection.variationBudget`, `OAI.MaxCutGames.Decoder.ConstantSelection.visibleMass`, `OAI.MaxCutGames.Decoder.NoiseSampler.samplerLaw`, `OAI.MaxCutGames.Decoder.PaddedLaw.pushforwardWeight`, `OAI.MaxCutGames.Decoder.SparseLaw.independentWeights`, `OAI.MaxCutGames.Decoder.SparseLaw.lineCount`, `OAI.MaxCutGames.Decoder.SparseLaw.mixture`, `OAI.MaxCutGames.Decoder.SparseLaw.singletonPairWeights`, `OAI.MaxCutGames.Decoder.SparseLaw.singletonSamplerWeights`, `OAI.MaxCutGames.Decoder.SparseLaw.uniformChiSquare`, `OAI.MaxCutGames.Decoder.SparseLaw.uniformWeights`, `OAI.MaxCutGames.Decoder.UniformFibers.selectedFiberEquiv`, `OAI.MaxCutGames.Decoder.VisibleTransfer.fiberEvent`, `OAI.MaxCutGames.Explicit.BipartiteGame`, `OAI.MaxCutGames.Explicit.BipartiteGame.Satisfied`, `OAI.MaxCutGames.Explicit.BipartiteGame.satisfiedCount`, `OAI.MaxCutGames.Explicit.MachineClone100.indices`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitProgram.Tape`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitStreams.tapes`, `OAI.MaxCutGames.Foundations.Complexity.CookLevin.PolynomialMachine.popN`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.Alphabet`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.Data`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.Label`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.LocalLabel`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.Tapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.cost`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.entry`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.finalRegister`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.finalTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.result`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.steps`, `OAI.MaxCutGames.Foundations.Complexity.MachineFiniteSequence.Label`, `OAI.MaxCutGames.Foundations.Complexity.MachineFiniteSequence.entry`, `OAI.MaxCutGames.Foundations.Complexity.MachineFiniteSequence.instruction`, `OAI.MaxCutGames.Foundations.Complexity.MachineFiniteSequence.resultOf`, `OAI.MaxCutGames.Foundations.Complexity.MachineFiniteSequence.steps` and 165 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_ActualGoodRows`, `MaxCut_Encoding_AffineWitnessFirstBit`, `MaxCut_Encoding_DimensionSelection`, `MaxCut_Encoding_Encoding`, `MaxCut_Encoding_PaddedLaw`, `MaxCut_Encoding_SparseLaw`, `MaxCut_Encoding_SurrogateFibers`, `MaxCut_Encoding_VisibleTransfer`, `MaxCut_Games_ActualCompleteness`, `MaxCut_Games_AddressGame`, `MaxCut_Games_AffineWitness`, `MaxCut_Games_AffineWitnessFiniteDensity`, `MaxCut_Games_CanonicalAddress`, `MaxCut_Games_CanonicalWordTemplate`, `MaxCut_Games_Clone100Counting`, `MaxCut_Games_EquationLookup`, `MaxCut_Games_LabelBound`, `MaxCut_Games_MatrixFourier`, `MaxCut_Games_MatrixGap`, `MaxCut_Games_OccurrenceTupleOrder`, `MaxCut_Games_RowErasure`, `MaxCut_Games_RowErasureSelection`, `MaxCut_Games_RowErasureSelectionNormalization`, `MaxCut_Games_RowErasureSliceQuotient`, `MaxCut_Games_Subdivision`, `MaxCut_Games_TranslationTarget`, `MaxCut_Machines_AddressMachineProgram`, `MaxCut_Machines_CanonicalBodyMachine`, `MaxCut_Machines_CloneMachineModel`, `MaxCut_Machines_Input`, `MaxCut_Machines_Machine`, `MaxCut_Machines_MachineClone100`, `MaxCut_Machines_MachineFieldTemplate`, `MaxCut_Machines_MachineHorner`, `MaxCut_Machines_MachineInitialHeaders`, `MaxCut_Machines_MachineRhsLoad`, `MaxCut_Machines_MachineSingleOrbitProgram`, `MaxCut_Machines_MachineTemplateAddress`, `MaxCut_Machines_MachineTuple`, `MaxCut_Machines_MachineTupleOdometer`, `MaxCut_Machines_MachineUnaryMultiply`, `MaxCut_Machines_MachineUniformCopyOrder`, `MaxCut_Machines_RuntimeModel`, `MaxCut_Model2`, `MaxCut_PCP_FieldArray`, `MaxCut_PCP_ProfileCorrection`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A008`, `OAIQ087A009`, `OAIQ087A010`, `OAIQ087A011` and `OAIQ087A012`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineUniformCopyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An exact ordering bridge for uniform copies.

Largest-remainder output groups copies of each occurrence together. A fixed
whole-word copying machine instead repeats the entire occurrence list. These
lists are permutations, not equal serializations. The permutation preserves
every selected occurrence count and the target's actual `countSatisfied`.
-/

namespace MaxCutGames.MachineUniformCopyOrder

def copyMajor {α : Type*} (C : Nat) (edges : List α) : List α :=
  (List.replicate C edges).flatten

end MaxCutGames.MachineUniformCopyOrder

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_TranslationTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.UniformTarget

open MachineUniformCopyOrder

theorem copy_length {α : Type*} (C : Nat) (xs : List α) :
    (copyMajor C xs).length = C * xs.length := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simp [copyMajor, List.replicate_succ, List.flatten_cons, Nat.add_mul,
      Nat.add_comm]

end MaxCutGames.Explicit.UniformTarget

end OAI
end

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

namespace MaxCutGames.Foundations.Complexity.MachineFiniteSequence

open Turing

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

end MaxCutGames.Foundations.Complexity.MachineFiniteSequence

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace MaxCutGames.Foundations.Complexity.MachineDrainMany

open Turing

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

/-- Selected tapes are empty; every other tape word is preserved. -/
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

end MaxCutGames.Foundations.Complexity.MachineDrainMany

namespace MaxCutGames.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (clearKeys : List K) := MachineDrainMany.Label clearKeys ⊕ Bool
abbrev Tapes (K : Type) := K → List Bool

def entry (clearKeys : List K) (labels : Label clearKeys → Λ) : Option Λ :=
  MachineDrainMany.entry clearKeys (fun l => labels (.inl l)) (some (labels (.inr false)))

def canonicalTapes (output : K) (word : List Bool) : Tapes K :=
  Function.update (fun _ => []) output word

open scoped BigOperators

end MaxCutGames.Foundations.Hastad.SourceRuntimeFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFieldTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.MachineFieldTemplate

open Turing
open MaxCutGames.Foundations.Complexity

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

end MaxCutGames.Reduction.MachineFieldTemplate

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Computable binary alphabet indexing and full translation permutation tables.
The labels are actual `Fin (2^s)` entries in the target instance format.
-/

namespace MaxCutGames.Reduction.Encoding

/-- Number the left side first and the right side second. -/
def sideEquiv (n : Nat) : Bool × Fin n ≃ Fin (2*n) :=
  (finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

@[simp] theorem sideEquiv_false_val {vertexCount : Nat} (i : Fin vertexCount) :
    (sideEquiv vertexCount (false, i)).val = i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv]

@[simp] theorem sideEquiv_true_val {vertexCount : Nat} (i : Fin vertexCount) :
    (sideEquiv vertexCount (true, i)).val = vertexCount + i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv, Nat.add_comm]

variable {Q V : Type*} [DecidableEq V]

/-- Canonical vertex bodies are compared using their actual decidable equality.
`List.dedup` fixes a deterministic order by retaining the last occurrence. -/
def imageVertices (queries : List Q) (body : Q → V) : List V :=
  (queries.map body).dedup

theorem mem_imageVertices {queries : List Q} {body : Q → V} {v : V} :
    v ∈ imageVertices queries body ↔ ∃ q ∈ queries, body q = v := by
  simp [imageVertices]

theorem imageVertices_nodup (queries : List Q) (body : Q → V) :
    (imageVertices queries body).Nodup := List.nodup_dedup _

abbrev ImageVertex (queries : List Q) (body : Q → V) :=
  {v : V // v ∈ imageVertices queries body}

/-- A computable numbering using `idxOf`; its inverse looks up that index.
It involves no chosen `Fintype.equivFin`. -/
def imageEquiv (queries : List Q) (body : Q → V) :
    ImageVertex queries body ≃ Fin (imageVertices queries body).length :=
  (List.Nodup.getEquiv _ (imageVertices_nodup queries body)).symm

theorem imageVertices_range (queries : List Q) (body : Q → V)
    (full : ∀ q, q ∈ queries) (v : V) :
    v ∈ imageVertices queries body ↔ v ∈ Set.range body := by
  simp [mem_imageVertices, full, Set.mem_range]

end MaxCutGames.Reduction.Encoding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_FieldArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceFieldArray

open Turing
open MaxCutGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

/-- Extend finite indices harmlessly outside the range used by the machine. -/
def boundedIndex (q j : Nat) : Fin (q + 1) := ⟨min j q, by omega⟩

@[simp] theorem boundedIndex_val {q j : Nat} (hj : j ≤ q) :
    (boundedIndex q j).val = j := Nat.min_eq_left hj

def startLabel (q j : Nat) : Fin (q + 1) × Bool := (boundedIndex q j, false)

end MaxCutGames.Foundations.Hastad.SourceFieldArray

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_LabelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Per-label diagonal lower bounds for the actual finite shared sampler.
These bounds retain the output label, which is necessary for comparing the
sampler's output distribution with a prescribed diagonal distribution. -/

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

namespace MaxCutGames.Foundations.Information

section

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

end

/-! Finite product-reference entropy decomposition, including zero-probability fibers. -/

open scoped BigOperators

/-!
Conditional laws on finite spaces, with a normalized default on null rows.
The default remains a probability law when a new input law charges a row
that had zero probability in the original joint distribution.
-/

end MaxCutGames.Foundations.Information

/-! Exact finite total variation and its event-probability bound. -/

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasureSliceQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Every nonempty affine row/column slice is an affine copy of the full space of
linear maps from the column quotient into the row kernel. This gives exact
uniform-law transport and preserves the affine evaluation offset.
-/

namespace MaxCutGames.Inverse.RowErasureSliceQuotient

noncomputable section

variable {R E K L : Type*} [Field R]
  [AddCommGroup E] [AddCommGroup K] [AddCommGroup L]
  [Module R E] [Module R K] [Module R L]

/-- The linear part of the affine parametrization. -/
def direction (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : E →ₗ[R] K :=
  A.ker.subtype.comp (N.comp Q.mkQ)

@[simp] theorem direction_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) (x : E) :
    direction A Q N x = (N (Q.mkQ x) : K) := rfl

/-- Quotient descent of a linear map which vanishes on the column span and
takes values in the common row kernel. -/
theorem exists_direction_of_row_and_column (A : K →ₗ[R] L)
    (Q : Submodule R E) (B : E →ₗ[R] K)
    (hQ : Q ≤ B.ker) (hA : LinearMap.range B ≤ A.ker) :
    ∃ N : (E ⧸ Q) →ₗ[R] A.ker, direction A Q N = B := by
  let B' : E →ₗ[R] A.ker := B.codRestrict A.ker
    (fun x => hA ⟨x, rfl⟩)
  have hQ' : Q ≤ B'.ker := by
    intro q hq
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change B q = 0
    exact hQ hq
  refine ⟨Q.liftQ B' hQ', ?_⟩
  ext x
  rfl

theorem direction_injective (A : K →ₗ[R] L) (Q : Submodule R E) :
    Function.Injective (direction A Q) := by
  intro N P h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Q.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : E →ₗ[R] K => f v) h

/-- The concrete affine slice around any one point satisfying its equations. -/
def AffineSlice (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :=
  {M : E →ₗ[R] K // A.comp M = A.comp M₀ ∧ ∀ q ∈ Q, M q = M₀ q}

def ofQuotient (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : AffineSlice A Q M₀ := by
  refine ⟨M₀ + direction A Q N, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change A (M₀ x + (N (Q.mkQ x) : K)) = A (M₀ x)
    rw [map_add, show A (N (Q.mkQ x) : K) = 0 from (N (Q.mkQ x)).property,
      add_zero]
  · intro q hq
    have hz : Q.mkQ q = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hq
    simp [direction, hz]

@[simp] theorem ofQuotient_val (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    (ofQuotient A Q M₀ N).val = M₀ + direction A Q N := rfl

theorem ofQuotient_bijective (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) : Function.Bijective (ofQuotient A Q M₀) := by
  constructor
  · intro N P h
    apply direction_injective A Q
    exact add_left_cancel (congrArg Subtype.val h)
  · intro M
    have hQ : Q ≤ (M.val - M₀).ker := by
      intro q hq
      change M.val q - M₀ q = 0
      exact sub_eq_zero.mpr (M.property.2 q hq)
    have hA : LinearMap.range (M.val - M₀) ≤ A.ker := by
      rintro y ⟨x, rfl⟩
      change A (M.val x - M₀ x) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      exact congrArg (fun f : E →ₗ[R] L => f x) M.property.1
    obtain ⟨N, hN⟩ := exists_direction_of_row_and_column A Q (M.val - M₀) hQ hA
    refine ⟨N, ?_⟩
    apply Subtype.ext
    rw [ofQuotient_val, hN]
    simpa only [← add_sub_assoc] using add_sub_cancel_left M₀ M.val

/-- Uniform free quotient maps parametrize exactly the original affine slice. -/
def equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :
    ((E ⧸ Q) →ₗ[R] A.ker) ≃ AffineSlice A Q M₀ :=
  Equiv.ofBijective (ofQuotient A Q M₀) (ofQuotient_bijective A Q M₀)

@[simp] theorem equiv_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    equiv A Q M₀ N = ofQuotient A Q M₀ N := rfl

end
end MaxCutGames.Inverse.RowErasureSliceQuotient

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ProfileCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Replacing the input marginal of an actual conditional profile. -/

/-! The actual single-coordinate dependency-breaking reveal distribution.
The tag records which endpoint of the question pair was revealed. -/

namespace MaxCutGames.Foundations.Repetition
open scoped BigOperators
open Information

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealEndpoint (q : X × Y) (side : Bool) : X ⊕ Y :=
  if side then Sum.inr q.2 else Sum.inl q.1

end MaxCutGames.Foundations.Repetition

end

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

inductive Label
  | copyDrain | copyFork | seed | guard | scan | emitFalse | emitTrue | restore | finish
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyDrain, .copyFork, .seed, .guard, .scan,
  .emitFalse, .emitTrue, .restore, .finish]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet {K : Type} (_ : K) := Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (_ : Unit) (bit : Bool) : List Bool := if bit then [true] else []

def emitterLabel {Λ : Type} (labels : Label → Λ) (_ : Unit) (bit : Bool) : Λ :=
  if bit then labels .emitTrue else labels .emitFalse

end MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

/-!
One actual Horner step on unary field stacks. Multiplication and addition are
executions of the same finite program. All three operands are preserved; only
the output stack receives a new field and both work stacks return empty.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRadixStep

open Turing

inductive Label
  | multiply (label : MachineUnaryMultiply.Label)
  | digitDrain | digitFork | add | finish
  deriving DecidableEq, Fintype

abbrev Alphabet {K : Type} (_ : K) := Bool

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

abbrev Alphabet (_ : K) := Bool

inductive Label (width : Nat)
  | start
  | radix (i : Fin width) (inner : MachineRadixStep.Label)
  | clear (i : Fin width)
  | finishDrain | finishRestore
  deriving DecidableEq, Fintype

def entryLabel (width n : Nat) : Label width :=
  if h : n < width then .radix ⟨n, h⟩ (.multiply .copyDrain) else .finishDrain

open scoped BigOperators

end MaxCutGames.Foundations.Complexity.MachineHorner

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RuntimeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed natural polynomials are represented by literal Horner coefficients.
The coefficient representation is independent of the machine input. The actual
machine wrapper is built from the shared physical unary Horner subroutine. -/

namespace MaxCutGames.Foundations.Complexity.CookLevin.PolynomialMachine

section LiteralFields

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def popN (k : K) : Nat → TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, continuation => continuation
  | n + 1, continuation => .pop k (fun state _ => state) (popN k n continuation)

end LiteralFields

end MaxCutGames.Foundations.Complexity.CookLevin.PolynomialMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTupleOdometer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineTupleOdometer

open Turing

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

end MaxCutGames.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Model2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite occurrence presentations used by the v2 rounding/subdivision construction.
An occurrence has its own identifier: its endpoints need not be distinct and
different occurrences may have the same endpoints. The bipartite target records
injectivity of the pair of endpoints, which is precisely the required simplicity.
No hardness or analytic premise enters these structures.
-/

namespace MaxCutGames.Explicit

structure BipartiteGame (L R E A : Type*) where
  left : E → L
  right : E → R
  permutation : E → Equiv.Perm A
  simple : Function.Injective (fun e => (left e, right e))

namespace BipartiteGame

def Satisfied {L R E A : Type*} (G : BipartiteGame L R E A)
    (leftLabeling : L → A) (rightLabeling : R → A) (e : E) : Prop :=
  rightLabeling (G.right e) = G.permutation e (leftLabeling (G.left e))

end BipartiteGame

end MaxCutGames.Explicit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The four-edge subdivision.
Every input occurrence has its own three interior vertices, even when
the original endpoints coincide or another occurrence has the same endpoints.
The left/right presentation inverts the permutation on the fourth edge.
-/

namespace MaxCutGames.Explicit

open scoped BigOperators

namespace BipartiteGame

variable {L R E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : BipartiteGame L R E A) (a : L → A) (b : R → A) : Nat :=
  ∑ e, if g.permutation e (a (g.left e)) = b (g.right e) then 1 else 0

end BipartiteGame

end MaxCutGames.Explicit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Input
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Serialization boundaries and direct row lookup for the shared executable
fixed-alphabet graph codec. The alphabet is a fixed parameter. Rows remain in
their stored order, including repeated darts and loops. Word offsets are fixed;
bit offsets are represented by actual encoded prefixes because unary fields
have data-dependent lengths. These are data identities, not runtime certificates.
-/

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

/-!
# An actual finite machine for a fixed-size Boolean block map

The program parameters `N`, `M`, and `F` are fixed. The local register has
exactly `N` bits. A syntactic chain of `N` pops fills that register, and a
syntactic chain of `M` pushes writes `F` of the register. No instruction
applies `F` to an unbounded word. An arbitrary ambient state is preserved,
and the local register is reset before the optional continuation.

TM2 executes a whole finite statement in one transition. The push bound
below separately records the exact `M` pushes in this statement.
-/

namespace MaxCutGames.Foundations.Complexity.MachineFixedBlockMap

open Turing

abbrev Buffer (N : Nat) := Fin N → Bool

end MaxCutGames.Foundations.Complexity.MachineFixedBlockMap

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

end MaxCutGames.Foundations.Complexity.MachineOdometerInit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Clone100Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete clone sample space. Global distinctness is a stronger
conditioning rule than distinctness only at repeated original «variables».
It retains the same 3/100 bound and makes the number of copies uniform. -/

namespace MaxCutGames.Outer.Clone100Triples

abbrev Index := Fin 100
abbrev Triple := Index × Index × Index

def good (t : Triple) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

abbrev GoodTriple := {t : Triple // good t}

end MaxCutGames.Outer.Clone100Triples

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineClone100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.MachineClone100

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations.Complexity

noncomputable section

def indices (t : Outer.Clone100Triples.GoodTriple) : Nat × Nat × Nat :=
  (t.val.1.val, t.val.2.1.val, t.val.2.2.val)

end

end MaxCutGames.Explicit.MachineClone100

/-!
A finite-state validator for the concrete ordinary-binary formula encoding.
It checks clause and literal framing, canonical name payloads, and the unique
terminal formula marker. The last-digit register starts at true for each name,
so the empty payload is accepted as zero while a nonempty payload must end in
one. Every bit following the terminal formula marker causes rejection.
-/

/-!
Total raw-input preprocessing for the ordinary binary formula codec. The
machine copies each input bit onto a reverse stack while running the finite
validator. Accepted words are restored verbatim; rejected words are drained
and replaced by the fixed contradictory formula. All three stack alphabets
and all control/register types are finite.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SparseLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite calculation behind v2 Lemma `projected-tv`. The three singleton
lines are averaged before the divergence is taken; projection choices are
not part of the compared sample space. Coordinates are independently sampled
occurrences, irrespective of whether their equation IDs coincide.
-/

namespace MaxCutGames.Decoder.SparseLaw

open scoped BigOperators
open MaxCutGames.Foundations.Information

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

/-- Pearson divergence against the uniform law, written with its constant
denominator cleared. `uniformChiSquare_eq_pearson` identifies the actual
likelihood-ratio definition. -/
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

/-- At the origin all three singleton lines contribute. -/
def lineCount (z : V × V) : ℝ :=
  (if z.2 = 0 then 1 else 0) + (if z.1 = 0 then 1 else 0) +
    (if z.1 = z.2 then 1 else 0)

/-- The average of the laws of `(a,0)`, `(0,a)`, and `(a,a)` for uniform `a`. -/
def singletonPairWeights (z : V × V) : ℝ := lineCount V z / (3 * Fintype.card V)

/-- Explicit finite pushforward of the three equally likely singleton choices.
The same uniform slope supplies both entries of the diagonal choice. -/
def singletonSamplerWeights (z : V × V) : ℝ :=
  ((∑ a : V, if (a, 0) = z then uniformWeights V a else 0) +
    (∑ a : V, if (0, a) = z then uniformWeights V a else 0) +
    (∑ a : V, if (a, a) = z then uniformWeights V a else 0)) / 3

end Singleton

end
end MaxCutGames.Decoder.SparseLaw

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_PaddedLaw
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
open MaxCutGames.Reduction
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePushforward

variable {α B : Type*} [Fintype α]

def pushforwardWeight (p : α → ℝ) (f : α → B) (y : B) : ℝ :=
  ∑ x, if f x = y then p x else 0

end FinitePushforward

end
end MaxCutGames.Decoder.PaddedLaw

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace MaxCutGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Uniformly normalized complex Fourier coefficient. -/
def fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  𝔼 x, f x * star (ψ x)

omit [AddCommGroup G] in
theorem star_expect (f : G → ℂ) :
    star (𝔼 x, f x) = 𝔼 x, star (f x) := by
  simp [Fintype.expect_eq_sum_div_card]

theorem star_fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) :
    star (fourierCoeff f ψ) = 𝔼 x, star (f x) * ψ x := by
  rw [fourierCoeff, star_expect]
  simp [star_mul, mul_comm]

end FiniteGroup

variable {E F : Type*}
variable [AddCommGroup E]
  [AddCommGroup F]

theorem complex_ofReal_expect {J : Type*} [Fintype J] (f : J → ℝ) :
    ((𝔼 j, f j : ℝ) : ℂ) = 𝔼 j, (f j : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  exact map_sum Complex.ofRealHom f Finset.univ

end MaxCutGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_ActualCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-distribution identities for completeness. -/
namespace MaxCutGames.Reduction.ActualCompleteness

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

noncomputable section

theorem expect_pair_inline_ActualCompleteness {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℚ) :
    (𝔼 p : I × J, f p) = 𝔼 i : I, 𝔼 j : J, f (i, j) :=
  Finset.expect_product _ _ _

end

end MaxCutGames.Reduction.ActualCompleteness

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CanonicalAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct canonical-body addresses. The fixed list of canonical words is
interpreted in big-endian order, matching forward Horner steps `B*acc+digit`.
Unused addresses represent isolated vertices. These are semantic encoding and
polynomial-size results, not an assumed machine implementation. -/

namespace MaxCutGames.Reduction.CanonicalAddress

/-- Most-significant-word first, with leading zero words retained in the
fixed-length domain. Mathlib's `ofDigits` uses the opposite list order. -/
def radix (B : Nat) (words : List Nat) : Nat := Nat.ofDigits B words.reverse

@[simp] theorem radix_nil (B : Nat) : radix B [] = 0 := rfl

theorem radix_lt_pow_length {B : Nat} (hB : 1 < B) (words : List Nat)
    (bounded : ∀ w ∈ words, w < B) : radix B words < B ^ words.length := by
  unfold radix
  simpa only [List.length_reverse] using
    Nat.ofDigits_lt_base_pow_length hB
      (fun w hw => bounded w (List.mem_reverse.mp hw))

/-- Fixed width makes leading zero words unambiguous. -/
theorem radix_injective_of_length_eq {B : Nat} (hB : 1 < B)
    {xs ys : List Nat} (sameLength : xs.length = ys.length)
    (xsBounded : ∀ w ∈ xs, w < B) (ysBounded : ∀ w ∈ ys, w < B)
    (sameAddress : radix B xs = radix B ys) : xs = ys := by
  have reversed : xs.reverse = ys.reverse :=
    Nat.ofDigits_inj_of_len_eq hB (by simpa only [List.length_reverse] using sameLength)
      (fun w hw => xsBounded w (List.mem_reverse.mp hw))
      (fun w hw => ysBounded w (List.mem_reverse.mp hw)) sameAddress
  have h := congrArg List.reverse reversed
  simpa only [List.reverse_reverse] using h

end MaxCutGames.Reduction.CanonicalAddress

/-! Finite noise tables for the executable outer reduction. Positions, including
positions containing equal vectors, remain distinct sample outcomes. -/

/-! Injective vertex addresses may leave unused output vertices. The actual
instance is obtained by mapping endpoints in the original constraint list;
constraint order, multiplicity, and permutation tables are retained exactly. -/

namespace MaxCutGames.Integration.VertexEmbedding

/-- The extension is only used as a semantic witness, not by the instance constructor. -/
noncomputable def extendLabeling {n m q : Nat} (f : Fin n → Fin m)
    (labeling : Fin n → Fin q) (defaultLabel : Fin q) (v : Fin m) : Fin q := by
  classical
  exact if h : ∃ u, f u = v then labeling (Classical.choose h) else defaultLabel

end MaxCutGames.Integration.VertexEmbedding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CanonicalWordTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.CanonicalWordTemplate

open Foundations.Complexity

/-- A literal word or a reference to one of the four saved input fields. -/
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

end MaxCutGames.Reduction.CanonicalWordTemplate

namespace MaxCutGames.Reduction.CanonicalBodyTemplate

open Foundations.Complexity
open scoped BigOperators

inductive Token (k : Nat)
  | literal (value : Nat)
  | field (position : Fin k) (index : Fin 4)
  deriving DecidableEq, Repr

variable {k : Nat}

def evalToken (fields : Fin k → Fin 4 → Nat) : Token k → Nat
  | .literal value => value
  | .field position index => fields position index

def evalTemplate (fields : Fin k → Fin 4 → Nat) (tokens : List (Token k)) : List Nat :=
  tokens.map (evalToken fields)

def nameField (j : Fin 3) : Fin 4 := ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

def recordFields (names : Fin 3 → Nat) (occurrence : Nat) (i : Fin 4) : Nat :=
  if h : i.val < 3 then names ⟨i.val, h⟩ else occurrence

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

namespace Arithmetic

inductive Control
  | variableCount | occurrenceCount | baseValue | capacity | temporary | reversed
  | accA | accB | counter | scratch
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.variableCount, .occurrenceCount,
  .baseValue, .capacity, .temporary, .reversed, .accA, .accB, .counter, .scratch]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

end Arithmetic

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

inductive Tape (q width : Nat)
  | field (i : Fin q)
  | radix | output | reversed | forward | copyScratch
  | accA | accB | counter | hornerScratch
  | digit (i : Fin width)
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet {K : Type*} (_ : K) := Bool

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

end MaxCutGames.Reduction.MachineTemplateAddress

/-! Actual edge emission from two fixed address templates. Capacity is copied
before unary addition, so the original capacity tape is preserved. All local
labels and literal instructions depend only on fixed templates and layout. -/

namespace MaxCutGames.Reduction.MachineAddressEdge

open Turing
open MaxCutGames.Foundations.Complexity
abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet {K : Type*} (_ : K) := Bool

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

abbrev Label (leftLength rightLength width : Nat) (cleanup : List K) :=
  MachineTemplateAddress.Label leftLength width cleanup ⊕ MachineTemplateAddress.Label rightLength width cleanup ⊕ Fin 7

def leftLabel {ml mr : Nat} {cleanup : List K} (label : MachineTemplateAddress.Label ml width cleanup) :
    Label ml mr width cleanup := .inl label
def rightLabel {ml mr : Nat} {cleanup : List K} (label : MachineTemplateAddress.Label mr width cleanup) :
    Label ml mr width cleanup := .inr (.inl label)
def plumbing {ml mr : Nat} {cleanup : List K} (index : Fin 7) :
    Label ml mr width cleanup := .inr (.inr index)

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

end MaxCutGames.Reduction.MachineSourceTuple

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CanonicalBodyMachine
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

open Foundations.Complexity

variable {k : Nat}

def fieldEquiv (k : Nat) : (Fin k × Fin 4) ≃ Fin (4*k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k 4))

def fieldIndex (position : Fin k) (field : Fin 4) : Fin (4*k) :=
  fieldEquiv k (position, field)

@[simp] theorem fieldIndex_val (position : Fin k) (field : Fin 4) :
    (fieldIndex position field).val = field.val + 4 * position.val := rfl

end MaxCutGames.Reduction.CanonicalBodyMachine

namespace MaxCutGames.Reduction.AddressMachineSpace

open MaxCutGames.Foundations.Complexity

abbrev Control (k : Nat) := ((Fin k → Bool) × Unit) × Unit
abbrev State (k : Nat) := Control k × Option Bool

def initialState (k : Nat) : State k := (((fun _ => false, ()), ()), none)

end MaxCutGames.Reduction.AddressMachineSpace

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRhsLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.MachineRhsLoad

open Turing
open MaxCutGames.Foundations.Complexity

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

end MaxCutGames.Reduction.MachineRhsLoad

/-! Execute all fixed outcome rows after the existing RHS loader. A single
dispatcher freezes the loaded finite RHS vector into labels. Every row is an
actual address-edge phase; no row-run or whole-loop execution is assumed.
Program definitions contain only fixed templates, literal permutations, and
tape/label placement. Numeric names, radix, and capacity occur only in tapes
and the semantic correctness hypotheses. -/

namespace MaxCutGames.Reduction.MachineOutcomeRows

open Turing
open MaxCutGames.Foundations.Complexity

/-- Numeric interpretations are proof-side data, separate from the program. -/
structure Values (width : Nat) where
  left : List Nat
  right : List Nat
  left_length : left.length = width
  right_length : right.length = width

abbrev Rhs (k : Nat) := Fin k → Bool
abbrev State (k : Nat) (σ : Type) := MachineRhsLoad.State k σ
abbrev Alphabet {K : Type} (_ : K) := Bool

end MaxCutGames.Reduction.MachineOutcomeRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressGame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Executable direct addresses for the actual canonical game. Every original
edge occurrence and its translation table is retained, in the same order.
Addresses not representing realized bodies are isolated vertices. No vertex
list, duplicate removal, or inverse enumeration is evaluated by the output. -/

namespace MaxCutGames.Reduction.AddressOutcomeSpecs

open Foundations.Complexity
open Integration

variable {s d : Nat} {α : Type*}

abbrev Values (k : Nat) := MachineOutcomeRows.Values (1+9*k)

end MaxCutGames.Reduction.AddressOutcomeSpecs

namespace MaxCutGames.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

abbrev BodyState (k : Nat) := AddressMachineSpace.State k

end MaxCutGames.Integration.AddressTupleBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OccurrenceTupleOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate-order bridge from the checked tuple odometer to the
outer reduction's occurrence enumeration. The odometer changes coordinate zero
fastest; `ActualEnumeration.functions` changes it slowest. Reading saved digit
`j.rev` as query coordinate `j` matches the complete ordered list. No primitive
machine or assumed whole-loop runtime is introduced here. -/

namespace MaxCutGames.Reduction.OccurrenceTupleOrder

open Turing
open MaxCutGames.Foundations.Complexity
open MachineTupleOdometer

variable {α : Type*}

/-- Read the physical saved digit positions in reverse coordinate order. -/
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

end MaxCutGames.Reduction.OccurrenceTupleOrder

/-!
# Polynomial encoded length of the actual output

The encoder uses a unary, delimited forward-permutation
format. The instance is the actual list-based reduction, including canonical
body deduplication and every repeated edge occurrence. The polynomial's
coefficients depend only on the fixed gadget table and tuple dimensions.

These are output-length theorems. They do not assert a machine running-time
certificate for canonicalization, enumeration, or serialization.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration

noncomputable section

abbrev State (k : Nat) := AddressMachineSpace.State k

end
end MaxCutGames.Reduction.AddressMachineProgram

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

namespace MaxCutGames.Explicit.MachineSingleOrbitProgram

open Turing
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction

inductive Tape
  | input | capacity | saved | remaining | accumulator | output
  deriving DecidableEq

end MaxCutGames.Explicit.MachineSingleOrbitProgram

/-! Exact streaming traces in the single-orbit postprocessor. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitStreams

open Turing MaxCutGames.Foundations.Complexity
open MachineSingleOrbitProgram

def tapes (input capacity saved remaining accumulator output : List Bool) : Tape → List Bool
  | .input => input
  | .capacity => capacity
  | .saved => saved
  | .remaining => remaining
  | .accumulator => accumulator
  | .output => output

@[simp] theorem tapes_input (i c s r a o : List Bool) : tapes i c s r a o .input = i := rfl
@[simp] theorem tapes_capacity (i c s r a o : List Bool) : tapes i c s r a o .capacity = c := rfl
@[simp] theorem tapes_saved (i c s r a o : List Bool) : tapes i c s r a o .saved = s := rfl
@[simp] theorem tapes_remaining (i c s r a o : List Bool) : tapes i c s r a o .remaining = r := rfl
@[simp] theorem tapes_accumulator (i c s r a o : List Bool) : tapes i c s r a o .accumulator = a := rfl
@[simp] theorem tapes_output (i c s r a o : List Bool) : tapes i c s r a o .output = o := rfl

end MaxCutGames.Explicit.MachineSingleOrbitStreams

/-! Physical unary header conversion, with an exact TM2 transition count. -/

/-! Actual subtraction of the right-side address offset, preserving the unary
capacity tape for every later edge. -/

/-! The exact input/output codec of the one-orbit postprocessor. Doubling is
only an encoding adapter: no equality of game values under independent labels
on the two copies is asserted. -/

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
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Size of a binary row kernel

An `r`-row linear constraint on `ℓ` binary coordinates leaves a kernel with at
least `2^(ℓ-r)` elements.  This does not require independent constraint rows.
The exponent uses natural subtraction, so the assertion also covers `r > ℓ`.
The argument is rank--nullity followed by the exact finite-field cardinality
formula; it does not use any inverse theorem or rank-level inequality.
-/

namespace MaxCutGames.Inverse

/-- Even dependent binary row constraints remove at most one dimension per
row. -/
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

/-- The cardinality of the binary row kernel is at least `2^(ℓ-r)`. -/
theorem binary_kernel_card_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    2 ^ (ℓ - r) ≤ Nat.card A.ker := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) (binary_kernel_finrank_lower A)

end MaxCutGames.Inverse

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_DimensionSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logical dimension is chosen after the inverse density and row bound,
and before the tuple length. All row maps, including deficient-rank maps,
satisfy the resulting small trivial-character bound. -/

/-!
# Finite latent samplers and their actual spectral law

This bridge counts all sampler outcomes, including repeated vectors and the
zero vector.  Uniform sampler detection is exactly the complement of the
matrix operator's annihilation multiplier.
-/

noncomputable section
open scoped BigOperators Classical

namespace MaxCutGames.Decoder.NoiseSampler

section FiniteLaw

variable {Noise V : Type*} [Fintype Noise] [Fintype V]

/-- The real pushforward of the uniform law on sampler outcomes. -/
def samplerLaw (noise : Noise → V) (v : V) : ℝ := by
  classical
  exact ∑ n, if noise n = v then (Fintype.card Noise : ℝ)⁻¹ else 0

end FiniteLaw

end MaxCutGames.Decoder.NoiseSampler
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SurrogateFibers
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

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Reduction

namespace MaxCutGames.Decoder.ActualSpectral

open NoiseSampler

def eta (r : Nat) : ℝ := ((2 : ℝ) ^ r)⁻¹ / 16

end MaxCutGames.Decoder.ActualSpectral
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Inverse.RowErasure

section

open scoped BigOperators

def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

@[simp] theorem indicator_true : indicator True = 1 := by simp [indicator]
@[simp] theorem indicator_false : indicator False = 0 := by simp [indicator]

def uniformMass {X : Type*} [Fintype X] (p : X → Prop) : ℝ :=
  Finset.univ.expect fun x => indicator (p x)

/-- Sample a uniform matrix, then an independent uniform row map. -/
def adviceMass {A X : Type*} [Fintype A] [Fintype X]
    (good : A → X → Prop) : ℝ :=
  Finset.univ.expect fun x => uniformMass fun a => good a x

open scoped BigOperators

variable {X Y A S D : Type*}

/-- Each description includes its row map, row value, column equations and
affine target. `points_row` is the necessary relationship to actual row advice. -/
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

open scoped BigOperators Classical

end MaxCutGames.Inverse.RowErasure

/-!
`InversePrinciple` concerns an arbitrary table function, full uniform factor
sampling, and an affine intercept.
-/

namespace MaxCutGames.Inverse.Shortcode

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

/-- Both perturbation factors are independent uniform vectors, including zero.
The matrix is sampled independently as well. -/
def equalityAcceptance {ell m : ℕ} (f : Mat ell m → Vector ell) : ℝ :=
  𝔼 M, 𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0

/-- A description includes possibly dependent equations; the row and column
counts need not equal their ranks. -/
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

end MaxCutGames.Inverse.Shortcode

/-!
Fixed-length descriptions for the row-erasure union bound. Row and column
equation lists are padded with zero equations. Targets retain both the linear
coefficient and the affine intercept. Thus the finite description count is
exactly `2^((2r+1)(ell+m))`, including descriptions with empty solution sets.
-/

namespace MaxCutGames.Inverse.RowErasureDescriptions

open MaxCutGames.Inverse.Shortcode
open scoped BigOperators

/-- A row map is represented by all its binary matrix coefficients. -/
abbrev RowMap (ell r : ℕ) := Fin r → Vector ell

/-- Ordered padded row coefficients, row values, column coefficients, column
values, affine coefficient, and affine intercept. Redundant descriptions are
intentional: counting descriptions provides an upper bound on distinct slices. -/
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

/-- Add vacuous equations after the original finite list. -/
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

end MaxCutGames.Inverse.RowErasureDescriptions

namespace MaxCutGames.Inverse.RowErasureMatrix

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasure
open MaxCutGames.Inverse.RowErasureDescriptions
open scoped BigOperators Classical

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

end MaxCutGames.Inverse.RowErasureMatrix

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AffineWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Inverse.AffineWitness

section

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

/-- A simultaneous row fiber and column slice, based at `M₀`. Agreement on
`Z` is exactly agreement with all column specifications spanning `Z`. -/
def InSlice (A : C →ₗ[F2] R) (Z : Submodule F2 D)
    (M₀ M : D →ₗ[F2] C) : Prop :=
  A.comp M = A.comp M₀ ∧ ∀ w ∈ Z, M w = M₀ w

/-- Changing the representative also changes the affine intercept. -/
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

/-- Rank-one translation in the row kernel. -/
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

/-- Normalization preserves every affine target value on the complete slice. -/
theorem normalize (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (h : ∃ w ∈ Z, e (z + w) = 1) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  obtain ⟨w, hw, he⟩ := h
  exact ⟨z + w, u + M₀ w, he, fun M hM => translate_target A Z M₀ M hM z w hw u⟩

end

/-! Conversion between explicitly listed affine column specifications and the
span-based slice used in first-bit normalization. -/

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

/-- A nonempty explicit affine row/column system is precisely the based slice.
The right-hand sides `S₀` and `t` are retained without homogenization. -/
theorem explicit_slice_iff (A : C →ₗ[F2] R) (S₀ : D →ₗ[F2] R)
    (q : ι → D) (t : ι → C) (M₀ M : D →ₗ[F2] C)
    (hrow : A.comp M₀ = S₀) (hcol : ∀ i, M₀ (q i) = t i) :
    (A.comp M = S₀ ∧ ∀ i, M (q i) = t i) ↔
      InSlice A (Submodule.span F2 (Set.range q)) M₀ M := by
  unfold InSlice
  rw [hrow, columns_iff_span q t M₀ M hcol]

end MaxCutGames.Inverse.AffineWitness

/-!
# Agreement counting for a folded action

A function that changes by an injectively encoded group element under a group
action can agree with an invariant target on at most one point per orbit.  The
proof injects the product of the acting group and the agreement set into the
underlying finite space.  Freeness of the action is not an additional premise:
the folding law and injectivity of the encoding force the needed freeness.

Only elementary group and finite-cardinality infrastructure is used here.
-/

namespace MaxCutGames.Inverse

variable {H X Y : Type*} [AddGroup H] [AddGroup Y]

/-- Translates of distinct agreement witnesses are distinct.  The encoding need
not be given as a homomorphism: only its injectivity and the displayed folding
identity are needed for this conclusion. -/
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

/-- The agreement set of a folded function with an invariant target occupies
at most the reciprocal of the size of the acting group, in denominator-free
finite-cardinality form. -/
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

end MaxCutGames.Inverse

/-!
The finite orbit count completing the first-bit witness normalization in v2.
The assumption in `normalize_of_good_count` is precisely that agreement is
strictly greater than the reciprocal of the row-kernel cardinality, expressed
without division. It is a quantitative goodness hypothesis, not an inverse
theorem or a nonlinear rank premise.
-/

namespace MaxCutGames.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

/-- The actual simultaneous row/column slice, including its affine offsets. -/
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

/-- If the affine coset misses first bit one, folding limits agreement to one
point per row-kernel orbit. No rank-level inequality is used. -/
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

/-- A good affine witness has a first-bit-one representative with an adjusted
intercept, agreeing with the original target on every matrix of its slice. -/
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

end MaxCutGames.Inverse.AffineWitness

/-!
The size bound for the actual simultaneous row/column slices in v2, Section 4.
Starting at any point of a nonempty slice, maps from the quotient by its column
span into the common row kernel give distinct points of that same affine slice.
Rank-nullity gives the dimension lower bound even when equations are dependent.
This argument uses only finite-dimensional linear algebra.
-/

namespace MaxCutGames.Inverse.Shortcode

section

open scoped BigOperators Matrix

namespace Slice

variable {ell m : ℕ}

/-- The simultaneous row functionals, allowing dependent and zero rows. -/
def rowMap (S : Slice ell m) : Vector ell →ₗ[F2] Vector S.rows :=
  Matrix.mulVecLin S.rowCoefficient

/-- Column specifications fix the matrix on this entire subspace. -/
def columnSpan (S : Slice ell m) : Submodule F2 (Vector m) :=
  Submodule.span F2 (Set.range S.columnCoefficient)

/-- Free directions of a row/column slice, intrinsically as quotient maps. -/
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

/-! Exact connection between the v2 finite-array shortcode slices and the
linear-map slices used by affine witness normalization. -/

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

/-- This is an equivalence of the actual equations, not merely a cardinality
comparison or a homogeneous approximation of the affine slice. -/
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

/-- Exact finite sample-space equivalence between the matrix representation
and the linear-map representation of a nonempty affine slice. -/
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

/-- Pointwise preservation on the genuine slice preserves its exact uniform
affine agreement, including the empty-slice convention. -/
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
end MaxCutGames.Inverse.Shortcode

/-! The probability form of first-bit witness normalization. -/

namespace MaxCutGames.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

/-- An agreement lower bound above the inverse row-kernel size produces a
first-bit-one representative while preserving the entire affine target. -/
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

end MaxCutGames.Inverse.AffineWitness

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_AffineWitnessFirstBit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Inverse.AffineWitness

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

end MaxCutGames.Inverse.AffineWitness

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AffineWitnessFiniteDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite indicator expectations as conditional cardinality ratios

These identities use the complete finite sample set in the denominator.  They
also cover the empty set, for which both the expectation and the ratio are zero.
The equivalence variant transfers both the event and the sample space, so no
conditioning factor is lost when changing representations of a slice.
-/

namespace MaxCutGames.Inverse

open scoped BigOperators

variable {X Y : Type*}

/-- Filtering a finite sample set counts the same objects as first restricting
to the sample set and then imposing the event predicate. -/
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

/-- An indicator's expectation on a finite set is its agreement count divided
by the cardinality of that same finite set. -/
theorem finset_expect_indicator_eq_card_ratio (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {x : s // p x.val} : ℝ) / (Nat.card s : ℝ) := by
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole,
    card_finset_subtype_eq_filter_card, Nat.card_eq_finsetCard]

/-- A bijection preserving the event preserves its count. No choice of a
`Fintype` enumeration is involved in this identity. -/
theorem nat_card_subtype_equiv (e : X ≃ Y) (p : X → Prop) (q : Y → Prop)
    (h : ∀ x, p x ↔ q (e x)) :
    Nat.card {x : X // p x} = Nat.card {y : Y // q y} :=
  Nat.card_congr (e.subtypeEquiv h)

/-- Transfer the indicator expectation through an equivalence of the complete
finite sample space, including the denominator of the conditional law. -/
theorem finset_expect_indicator_eq_card_ratio_of_equiv (s : Finset X)
    (p : X → Prop) [DecidablePred p] (e : ↥s ≃ Y) (q : Y → Prop)
    (h : ∀ x : s, p x.val ↔ q (e x)) :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {y : Y // q y} : ℝ) / (Nat.card Y : ℝ) := by
  rw [finset_expect_indicator_eq_card_ratio,
    nat_card_subtype_equiv e (fun x => p x.val) q h, Nat.card_congr e]

end MaxCutGames.Inverse

/-! First-bit normalization in the actual finite-array shortcode API. The
sample space, event count, affine intercept, and folding law are transported
exactly; no inverse result is assumed by the representation bridge. -/

namespace MaxCutGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

variable {ell m : ℕ}

/-- The coordinate row of a binary linear functional. -/
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

/-- Exact density identity on the complete nonempty affine slice, with no
lost conditioning factor in the change from matrices to linear maps. -/
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

/-- First-bit normalization for the exact selected shortcode slice.
The original affine agreement is preserved, not merely bounded below. -/
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
end MaxCutGames.Inverse.Shortcode

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualGoodRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.ActualGoodRows

open Reduction
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

def goodRowMass (rstar s r : ℕ) : ℝ :=
  10 * ActualSpectral.eta rstar ^ 2 / (2 : ℝ) ^ (s * r)

end
end MaxCutGames.Decoder.ActualGoodRows

namespace MaxCutGames.Decoder.ConstantSelection

open MaxCutGames.Foundations.Information
open SparseLaw

noncomputable section

/-- Probability of actual visible data carrying a transferred witness. -/
def visibleMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  α * g₀ / (8 * (2 : ℝ) ^ (ell * r))

/-- Independent private decoding success on a transferred witness. -/
def conditionalMass (α : ℝ) (ell r : ℕ) : ℝ :=
  (α / 8) ^ 2 / (2 : ℝ) ^ (ell * r) / (2 : ℝ) ^ r

def decodingMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r * conditionalMass α ell r

/-- The whole-table TV budget includes the coefficient of both compared
events in the witness-margin inequality. -/
def variationBudget (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r / (1 + α / 4)

end
end MaxCutGames.Decoder.ConstantSelection

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasureSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Visible selection of a row-erasure witness. The selected description depends
only on the fixed table function, the row map, and the observed row value.
The full sampled matrix enters only the later event testing its membership in
the already selected slice. Classical choice fixes one witness once and for all;
proof irrelevance makes the choice independent of the goodness proof.
-/

namespace MaxCutGames.Inverse.RowErasure

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

/-- A total visible selector. Bad advice has no selected witness. -/
def SliceFamily.selectedDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Option D := by
  classical
  exact if hgood : F.GoodAdvice f α a s then
    some (F.chosenDescription f α a s hgood) else none

/-- Good visible advice and the selected column restrictions on the hidden
matrix. The selector receives only its observed row value. -/
def SliceFamily.selectedEvent (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧ x ∈ F.points d

def SliceFamily.selectedMatch (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧
    x ∈ F.points d ∧ f x = F.target d x

end MaxCutGames.Inverse.RowErasure

/-!
Finite partition estimates for a selector fixed by visible data. The observation
fibers need not have equal sizes. Each local counting inequality is summed over
the actual fibers, then divided by the size of the hidden sample space.
-/

/-!
Exact mass of a nonempty column slice within a fixed row-advice fiber. A
column span of dimension at most `r` costs at most `ell*r` binary degrees of
freedom. All inhomogeneous values are represented by the chosen base point.
-/

/-!
Exact uniform parametrization of the concrete row/column slice.  The quotient
parameter describes every point, not only a lower-bounding subfamily.  Affine
targets retain the base-point contribution and their original intercept.
-/

namespace MaxCutGames.Inverse.Shortcode.Slice

open scoped BigOperators Matrix

variable {ell m : ℕ}

theorem difference_row_zero (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.rowMap.comp (Matrix.toLin' (M - M₀)) = 0 := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have hrow : LinearMap.toMatrix' S.rowMap = S.rowCoefficient :=
    LinearMap.toMatrix'_toLin' S.rowCoefficient
  rw [hrow]
  ext i j
  change (∑ a, S.rowCoefficient i a * (M - M₀) a j) = 0
  simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hM.1 i j, h₀.1 i j, sub_self]

theorem difference_range_le (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    LinearMap.range (Matrix.toLin' (M - M₀)) ≤ S.rowMap.ker := by
  rintro _ ⟨v, rfl⟩
  have h := LinearMap.congr_fun (S.difference_row_zero hM h₀) v
  exact h

theorem difference_vanishes_columns (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.columnSpan ≤ LinearMap.ker (Matrix.toLin' (M - M₀)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change Matrix.toLin' (M - M₀) (S.columnCoefficient i) = 0
  have he : Matrix.toLin' (M - M₀) (S.columnCoefficient i) =
      evaluate M (S.columnCoefficient i) - evaluate M₀ (S.columnCoefficient i) := by
    rw [map_sub, LinearMap.sub_apply]
    rfl
  rw [he, hM.2 i, h₀.2 i, sub_self]

/-- Every actual slice point differs from the base by a unique quotient map. -/
theorem directionEmbedding_surjective (S : Slice ell m)
    (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    Function.Surjective (S.directionEmbedding M₀ h₀) := by
  intro M
  have hM : S.Contains M.val := by
    simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using M.property
  obtain ⟨N, hN⟩ :=
    RowErasureSliceQuotient.exists_direction_of_row_and_column
      S.rowMap S.columnSpan (Matrix.toLin' (M.val - M₀))
      (S.difference_vanishes_columns hM h₀) (S.difference_range_le hM h₀)
  have hdir : S.directionMap N = Matrix.toLin' (M.val - M₀) := hN
  have hmat : S.directionMatrix N = M.val - M₀ := by
    unfold directionMatrix
    rw [hdir, LinearMap.toMatrix'_toLin']
  refine ⟨N, ?_⟩
  apply Subtype.ext
  change M₀ + S.directionMatrix N = M.val
  rw [hmat]
  abel

/-- The concrete simultaneous slice is exactly an affine copy of
`Hom(domain / columnSpan, commonRowKernel)`. -/
def directionEquiv (S : Slice ell m) (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    S.Directions ≃ S.points :=
  Equiv.ofBijective (S.directionEmbedding M₀ h₀)
    ⟨(S.directionEmbedding M₀ h₀).injective, S.directionEmbedding_surjective M₀ h₀⟩

@[simp] theorem directionEquiv_val (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) (N : S.Directions) :
    (S.directionEquiv M₀ h₀ N).val = M₀ + S.directionMatrix N := rfl

end MaxCutGames.Inverse.Shortcode.Slice

/-!
The actual finite matrix column event occupies at least `2^(-ell*r)` of its
row-advice fiber. This connects the intrinsic quotient-map count to the padded
descriptions used by the selector, without assuming independent equations.
-/

namespace MaxCutGames.Inverse.RowErasureDescriptionColumnMass

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasureDescriptions
open MaxCutGames.Inverse.RowErasureMatrix
open scoped BigOperators Classical

def rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m) :
    Finset (Mat ell m) :=
  Finset.univ.filter fun M => rowAdvice A M = s

@[simp] theorem mem_rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m)
    (M : Mat ell m) : M ∈ rowFiber A s ↔ rowAdvice A M = s := by
  simp [rowFiber]

end MaxCutGames.Inverse.RowErasureDescriptionColumnMass

/-!
The selected column event under the actual uniform matrix and row-map samples.
The witness is fixed by visible row advice before testing the hidden matrix.
Fiber sizes are retained explicitly; no uniformity of row values is assumed.
The final averaging lemmas also allow arbitrary nonnegative context weights.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasureSelectionNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Normalize the affine target chosen from visible row advice. The selected row
and column equations are unchanged. Only the target coefficient and intercept
are replaced, with exact target equality on the entire selected slice.
-/

namespace MaxCutGames.Inverse.RowErasureDescriptions

open MaxCutGames.Inverse.Shortcode

/-- Replace the affine target while retaining all row and column data. -/
def Description.withTarget {ell m r : ℕ} (d : Description ell m r)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (d.1, d.2.1, d.2.2.1, d.2.2.2.1, z, u)

@[simp] theorem Description.withTarget_toSlice {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).toSlice = d.toSlice := rfl

@[simp] theorem Description.withTarget_coefficient {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).coefficient = z := rfl

@[simp] theorem Description.withTarget_intercept {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).intercept = u := rfl

end MaxCutGames.Inverse.RowErasureDescriptions

namespace MaxCutGames.Inverse.RowErasureMatrix

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasure
open MaxCutGames.Inverse.RowErasureDescriptions

noncomputable section

variable {ell m r : ℕ}

/-- Normalization of the already chosen description. The sampled matrix is
absent from the selector's inputs; pointwise target equality holds afterward
for every matrix in the selected slice. -/
theorem exists_normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    ∃ d : Description ell m r,
      (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M := by
  classical
  let d₀ := (family ell m r).chosenDescription f α A S hgood
  obtain ⟨hrow, hvalue, hnonempty, hagree⟩ :=
    (family ell m r).chosenDescription_spec f α A S hgood
  obtain ⟨M₀, hM₀⟩ := hnonempty
  have hcontains : d₀.toSlice.Contains M₀ := by
    exact (Finset.mem_filter.mp hM₀).2
  have hagree' : α / 2 ≤ d₀.toSlice.affineAgreement f d₀.coefficient d₀.intercept := by
    exact (family_agreement d₀ f) ▸ hagree
  obtain ⟨z, u, hfirst, heq, htarget⟩ :=
    d₀.toSlice.first_bit_normalization M₀ hcontains e f d₀.coefficient d₀.intercept
      (fun h M => hfold h M) α hα hagree' hsmall
  have heq' : (family ell m r).agreement f (d₀.withTarget z u) =
      (family ell m r).agreement f d₀ := by
    rw [family_agreement, family_agreement]
    exact heq
  refine ⟨d₀.withTarget z u, hrow, hvalue, ⟨M₀, hM₀⟩, ?_, hfirst, rfl, heq', ?_⟩
  · exact heq'.symm ▸ hagree
  · intro M hM
    exact htarget M (Finset.mem_filter.mp hM).2

/-- A fixed normalized witness determined by the visible table and row advice.
All remaining inputs are the fixed normalization functional and proofs. -/
def normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    Description ell m r :=
  Classical.choose (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

theorem normalizedChosenDescription_spec
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    let d := normalizedChosenDescription f α A S hgood e hfold hα hsmall
    (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M :=
  Classical.choose_spec
    (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

end
end MaxCutGames.Inverse.RowErasureMatrix

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_VisibleTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.VisibleTransfer

open scoped BigOperators

noncomputable section

variable {Ω D : Type*} [Fintype Ω] [Fintype D]

/-- The part of an event in one actual visible-data fiber. -/
def fiberEvent (observe : Ω → D) (d : D) (event : Ω → Bool) : Ω → Bool := by
  classical
  exact fun x => decide (observe x = d) && event x

end
end MaxCutGames.Decoder.VisibleTransfer

namespace MaxCutGames.Decoder.UniformFibers

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
end MaxCutGames.Decoder.UniformFibers

/-! The complete-data conditional law of the actual projected experiment.
The residual private matrix is uniform even when the occurrence law is
weighted and the public row map has deficient rank. -/

/-!
# Actual conditional selected-fiber agreement

The selected event is the full-table event used by the total-variation
comparison. On a positive complete-data fiber it becomes the uniform actual
affine row/column slice. The selector is fixed by the left observation; the
extra complete data and a supporting matrix occur only in this analysis.
-/

/-! The full selected-witness argument on the actual projected experiment.
The variation comparison precedes all conditioning. Its visible event then
pays the independent private decoder success on every selected datum. -/

end OAI
end


