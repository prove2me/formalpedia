-- Prove2me | Definitions.Def_OAIQ081S022
-- name    : OAIQ081S022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:25:07.544117+00:00
-- url     : https://prove2.me/theorems/916559c5-59e2-4f5a-af1c-9c90701f3727
-- title:
--   Definitions bundle OAIQ081S022 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 39 definitions, 2 inductive types or structures, 9 instances and 49 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.decodeBasePort`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace.portIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.finishEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum.portIndex`, `OAI.Algorithms.SubexponentialSAT.SubexpCeilingProgram.Regs`, `OAI.Algorithms.SubexponentialSAT.SubexpCeilingProgram.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.SubexpChunkRecordMap.regs`, `OAI.Algorithms.SubexponentialSAT.SubexpChunkRecordMap.tapes`, `OAI.Algorithms.SubexponentialSAT.SubexpClauseRowProgram.regs`, `OAI.Algorithms.SubexponentialSAT.SubexpClauseRowProgram.tapes`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.encodeArray`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.unaryBudget`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionEncoding.encodeArray`, `OAI.Algorithms.SubexponentialSAT.SubexpFlatCount.budget`, `OAI.Algorithms.SubexponentialSAT.SubexpHornerProgram.triple`, `OAI.Algorithms.SubexponentialSAT.SubexpIncidenceSlotProgram.unary`, `OAI.Algorithms.SubexponentialSAT.SubexpIntervalCoreProgram.width`, `OAI.Algorithms.SubexponentialSAT.SubexpIntervalStartProgram.value`, `OAI.Algorithms.SubexponentialSAT.SubexpLayoutConstructionBounds.Word`, `OAI.Algorithms.SubexponentialSAT.SubexpLiteralChunkProgram.tapes`, `OAI.Algorithms.SubexponentialSAT.SubexpLocalCorrectionAlgebra.padded`, `OAI.Algorithms.SubexponentialSAT.SubexpNegatedQueryProgram.slots`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram.Internal.callbackCost`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram.Internal.normalized`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram.Internal.store`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.Cursor`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.marker`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.negativeAfter`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.next`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.run`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.words`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram.negateSteps`, `OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl.operandDepth`, `OAI.Algorithms.SubexponentialSAT.SubexpProjectedInterpreter.Validity`, `OAI.Algorithms.SubexponentialSAT.SubexpSetupProgram.storageOverhead`, `OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity.NegativeLabels`, `OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity.PositiveLabels`, `OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity.positiveSigmaEquiv`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.perClauseCost`, `OAI.Algorithms.SubexponentialSAT.SubexpUnaryRangeProgram.unary` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_FourWordPrograms`, `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace`, `SubexponentialSAT_SqrtLogSpace_QueryStreamBudgets`, `SubexponentialSAT_SqrtLogSpace_QueryTupleSum`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramLowMask`, `SubexponentialSAT_SqrtLog_SquarefreeSupportCount`, `SubexponentialSAT_SubexpCeilingProgram`, `SubexponentialSAT_SubexpChunkRecordMap`, `SubexponentialSAT_SubexpClauseRowProgram`, `SubexponentialSAT_SubexpConvolutionEncoding`, `SubexponentialSAT_SubexpConvolutionIteration`, `SubexponentialSAT_SubexpConvolutionRows`, `SubexponentialSAT_SubexpDenseProgram`, `SubexponentialSAT_SubexpFlatCount`, `SubexponentialSAT_SubexpHornerProgram`, `SubexponentialSAT_SubexpIncidenceSlotProgram`, `SubexponentialSAT_SubexpIntervalCoreProgram`, `SubexponentialSAT_SubexpIntervalStartProgram`, `SubexponentialSAT_SubexpLayoutFactorBounds`, `SubexponentialSAT_SubexpLiteralChunkProgram`, `SubexponentialSAT_SubexpLocalCorrectionAlgebra`, `SubexponentialSAT_SubexpNegatedQueryProgram`, `SubexponentialSAT_SubexpNodeIndexProgram`, `SubexponentialSAT_SubexpNodeScanControl`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpProjectedExecution`, `SubexponentialSAT_SubexpSetupStorageCost`, `SubexponentialSAT_SubexpSwapMultiplicity`, `SubexponentialSAT_SubexpTautologyFilterProgram`, `SubexponentialSAT_SubexpTaylorCode`, `SubexponentialSAT_SubexpUnaryRangeProgram`, `SubexponentialSAT_Subexp_BlockZeroProgram`, `SubexponentialSAT_TypeDistribution`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S043`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor`, `OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_ProductCallback_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Multiplier_prepareMultiplier_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.stageCost_linear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ081_SAT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_FourWordPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Four runtime-width words in flat and bank representations

Eight distinct caller ports hold a flat record, unary field width, counter,
temporary stack, and four bank words. The number four is fixed in the control;
the field width is exclusively stack data.
-/

namespace SubexponentialSAT.FourWordPrograms

@[simp] theorem ports_eq {s : ℕ} (ports : Fin 8 ↪ Fin s) (i j : Fin 8) :
    ports i = ports j ↔ i = j := ports.injective.eq_iff

end SubexponentialSAT.FourWordPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TypeDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform words induce uniform local types

The outcome space consists of all assignments of words to distinct factor,
head, and padding indices. Local read maps are injective. Read maps at
distinct coordinates sharing no factor have disjoint ranges. Finite product
counting then supplies the actual marginals and pair moments needed by
SubexponentialSAT.Variance; these probabilistic properties are conclusions, not hypotheses.
-/

namespace SubexponentialSAT.TypeDistribution

open scoped BigOperators

section FiniteMeans

variable {A B I J W : Type*}

/-- Combine two disjoint injective sets of reads into a single injection. -/
def jointReads (e : A ↪ I) (f : B ↪ I) (h : ∀ a b, e a ≠ f b) : A ⊕ B ↪ I where
  toFun := Sum.elim e f
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (e.injective hab)
      | inr b => exact (h a b hab).elim
    | inr a =>
      cases b with
      | inl b => exact (h b a hab.symm).elim
      | inr b => exact congrArg Sum.inr (f.injective hab)

end FiniteMeans

end SubexponentialSAT.TypeDistribution

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalCorrectionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Semantic invariants for the fixed-width local CRT preparation. Every
intermediate polynomial product may be truncated to D coefficients. The
constant coefficient is inverted once by the executable residue algorithm. -/

namespace SubexponentialSAT.SubexpLocalCorrectionAlgebra

open Polynomial
open scoped BigOperators

def padded {C : Type*} (zero low high : C) : ℕ → List C
  | 0 => []
  | 1 => [low]
  | n + 2 => low :: high :: List.replicate n zero

@[simp] theorem padded_length {C : Type*} (zero low high : C) (D : ℕ) :
    (padded zero low high D).length = D := by
  cases D with
  | zero => rfl
  | succ D => cases D <;> simp [padded]

end SubexponentialSAT.SubexpLocalCorrectionAlgebra

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Unary runtime-loop execution used by both convolution loops. The body
obligation contains actual executions; the loop invariant concerns physical
stacks and may include decoded coefficient arrays and their lengths. -/

namespace SubexponentialSAT.SubexpConvolutionControl

/-- One branch test per iteration plus the final failing branch. -/
def unaryBudget (cost : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | fuel + 1 => cost (fuel + 1) + unaryBudget cost fuel + 2

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed traversal of flat node cells, skipping one unary-indexed node.
The included-node service is an actual command with an actual execution
contract. This file accounts for all reads, guards, index pops, and cleanup.
-/

namespace SubexponentialSAT.SubexpNodeScanControl

open SubexpConvolutionControl

structure Cursor (A : Type*) where
  value : A
  skip : List Bool
  pending : Bool

def next {A C : Type*} (f : A → C → A) (c : C) (x : Cursor A) : Cursor A :=
  match x.skip with
  | _ :: rest => ⟨f x.value c, rest, x.pending⟩
  | [] => if x.pending then ⟨x.value, [], false⟩ else ⟨f x.value c, [], false⟩

def run {A C : Type*} (f : A → C → A) : List C → Cursor A → Cursor A
  | [], x => x
  | c :: cs, x => run f cs (next f c x)

def marker (pending : Bool) : List Bool := if pending then [true] else []

def words {A C : Type*} (encode : C → List Bool) (encodeA : A → List Bool)
    (cs : List C) (x : Cursor A) (current negative : List Bool) : Fin 6 → List Bool :=
  ![cs.flatMap encode, x.skip, marker x.pending, encodeA x.value, current, negative]

variable {A C : Type*}

def negativeAfter (negative : C → List Bool) (c : C) (x : Cursor A) : List Bool :=
  match x.skip with
  | _ :: _ => negative c
  | [] => if x.pending then [] else negative c

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The triangular convolution controller charges actual fixed-width reads,
copies, and cell writes. The local pair contract is a contract for a fixed
finite command and is instantiated by the concrete quartic/jet service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

variable {C : Type*}

def encodeArray (encode : C → List Bool) (xs : List C) : List Bool :=
  (xs.map encode).flatten

@[simp] theorem encodeArray_nil (encode : C → List Bool) : encodeArray encode [] = [] := rfl
@[simp] theorem encodeArray_cons (encode : C → List Bool) (a : C) (xs : List C) :
    encodeArray encode (a :: xs) = encode a ++ encodeArray encode xs := by simp [encodeArray]

@[simp] theorem encodeArray_append (encode : C → List Bool) (xs ys : List C) :
    encodeArray encode (xs ++ ys) = encodeArray encode xs ++ encodeArray encode ys := by
  simp [encodeArray]

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The encoded-array decomposition used by the actual convolution
product-and-update command. No scalar algebra or execution cost is assumed. -/

namespace SubexponentialSAT.SubexpConvolutionEncoding

def encodeArray {C : Type*} (encode : C → List Bool) (acc : List C) : List Bool :=
  (acc.map encode).flatten

end SubexponentialSAT.SubexpConvolutionEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete postfix instruction dispatch and literal push

The fixed prefix tags are push `0`, add `10`, and multiply `11`.
A push tag is followed by an `Encoding.frame` coefficient payload. End of
the code stack ends the instruction stream. The base dispatcher exposes
explicit service exits. The linked program implements literal push through
the actual frame parser and a Boolean-stack encoding loop; scalar arithmetic
remains at explicit service boundaries.

Registers: 0 last bit, 1 successful-pop flag, 2 binary-operation flag.
Stacks: 0 serialized code, 1 unary operand depth, 2 framed operand data.
The operand data stack is preserved throughout dispatch. On a successful
dispatch the depth stack has already been adjusted for the pending service.
The linked literal service uses stack 3 as initially empty scratch and returns
to dispatch with that scratch empty and the framed operand list updated.
-/

namespace SubexponentialSAT.SubexpPostfixControl

/-! ## Serialization of the existing postfix instruction type -/

def operandDepth {R : Type*} (xs : List R) : List Bool :=
  List.replicate xs.length true

/-! ## Literal-push service with the framed-list operand ABI -/

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

/-- The exact running time depends only on the scanned code length and parity. -/
def negateSteps (c : ℕ) : ℕ := 8 * (c / 2) + 10 + c % 2

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeIndexProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical lookup of the current field node

The fixed program copies the framed node table, parses its records in order,
compares their actual bits with the current node, and counts rejected records.
Its only visible stack change is the unary first matching index at port 116.
The source table at 125 and query at 78 are preserved.
-/

namespace SubexponentialSAT.SubexpNodeIndexProgram

namespace Internal

def store (query master source payload work tmp count : List Bool) : Fin 7 → List Bool :=
  ![query, master, source, payload, work, tmp, count]

def normalized (regs : Fin 5 → Bool) (v pr f : Bool) : Fin 5 → Bool :=
  Function.update (Function.update (Function.update regs 0 v) 1 pr) 4 f

@[simp] theorem normalized_self (regs : Fin 5 → Bool) :
    normalized regs (regs 0) (regs 1) (regs 4) = regs := by
  funext i; fin_cases i <;> simp [normalized]

@[simp] theorem normalized_normalized (regs : Fin 5 → Bool)
    (v pr f v' pr' f' : Bool) :
    normalized (normalized regs v pr f) v' pr' f' = normalized regs v' pr' f' := by
  funext i; fin_cases i <;> simp [normalized]

def callbackCost (query key : List Bool) : ℕ := 20 * key.length + 9 * query.length + 32

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpUnaryRangeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

abbrev unary (n : ℕ) := List.replicate n true

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite control for dense coefficient projection

The controller below is an actual finite instruction table. Its local callback
contract is deliberately an actual `StructuredCalls.Eval` of a fixed program:
it must be discharged by the concrete lookup and record-emission programs.
It is not an assumption that an abstract ring operation takes one machine step.
The concrete callback integration and product-pair builder are separate stages.
-/

namespace SubexponentialSAT.SubexpDenseProgram.KeyWidth

@[simp] theorem update_zero {α : Type*} (a b c x : α) :
    Function.update (![a,b,c] : Fin 3 → α) 0 x = ![x,b,c] := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))
@[simp] theorem update_one {α : Type*} (a b c x : α) :
    Function.update (![a,b,c] : Fin 3 → α) 1 x = ![a,x,c] := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))
@[simp] theorem update_two {α : Type*} (a b c x : α) :
    Function.update (![a,b,c] : Fin 3 → α) 2 x = ![a,b,x] := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

end SubexponentialSAT.SubexpDenseProgram.KeyWidth

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpProjectedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Projected postfix execution

The compiled source contains the original raw literals. Each complete push
calls the finite projection table; the resulting value is therefore
`(e.map project).eval`. The induction tracks the entire remaining source and
operand list, and charges actual service trace bounds at every node.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open SubexpPostfixControl (operandDepth)

variable {r s a b c : ℕ}

/-- Pure closure facts for the values accepted by the arithmetic tables. -/
structure Validity {R : Type*} [Add R] [Mul R] (valid : R → Prop) (project : R → R) : Prop where
  load_valid : ∀ x, valid (project x)
  add_valid : ∀ x y, valid x → valid y → valid (x + y)
  mul_valid : ∀ x y, valid x → valid y → valid (x * y)

end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockZeroProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program testing whether all payload bits in a sequence of
frames are zero. Frame delimiters are ignored; no scalar arithmetic is hidden
inside this program. -/

namespace SubexponentialSAT.Subexp.BlockZeroProgram

@[simp] theorem update1 {A : Type*} (a x : A) :
    Function.update (fun _ : Fin 1 => a) 0 x = fun _ => x := by
  funext i; fin_cases i; simp

@[simp] theorem update5_4 {A : Type*} (a b c d e x : A) :
    Function.update ![a,b,c,d,e] (4 : Fin 5) x = ![a,b,c,d,x] := by
  first | done | (funext i; fin_cases i <;> simp)

end SubexponentialSAT.Subexp.BlockZeroProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHornerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control source generation for factored Horner expressions

Input payloads are coefficient representations, never precomputed instruction
streams. The emitter writes the actual serialized postfix tags and frames.
-/

namespace SubexponentialSAT.SubexpHornerProgram

def triple {α : Type*} (a b c : α) : Fin 3 → α :=
  fun i => if i = 0 then a else if i = 1 then b else c

@[simp] theorem update_triple_zero {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 0 d = triple d b c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_one {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 1 d = triple a d c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_two {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 2 d = triple a b d := by
  funext i
  fin_cases i <;> simp [triple]

end SubexponentialSAT.SubexpHornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSwapMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multiplicities of register-swap eigenvalue labels

The negative local labels are strictly below the diagonal and the positive
labels are on or above it. Counting these labels and their tensor words is
independent of the characteristic of the coefficient field.
-/

namespace SubexponentialSAT.SubexpSwapMultiplicity

open scoped BigOperators

abbrev PositiveLabels (r : ℕ) := {x : Fin r × Fin r // x.1 ≤ x.2}
abbrev NegativeLabels (r : ℕ) := {x : Fin r × Fin r // x.2 < x.1}

def positiveSigmaEquiv (r : ℕ) :
    PositiveLabels r ≃ Σ b : Fin r, {a : Fin r // a ≤ b} where
  toFun x := ⟨x.1.2, x.1.1, x.2⟩
  invFun x := ⟨(x.2.1, x.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## General binomial second moment and the interval tail -/

end SubexponentialSAT.SubexpSwapMultiplicity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTaylorCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable Taylor coefficient caches for incidence-argument compilation

Input paths are dense coefficient lists. Each path is shifted once by the
existing Horner loop, then its first q+1 coefficients are read into a real
array cache. Mathematical polynomials occur only in semantic theorems.
-/

namespace SubexponentialSAT.SubexpTaylorCode

open scoped BigOperators

@[simp] theorem getD_ofFn {B : Type*} {n : ℕ}
    (f : Fin n → B) (i : Fin n) (fallback : B) :
    (Array.ofFn f).getD i.val fallback = f i := by
  simp [Array.getD, i.isLt]

@[simp] theorem getD_map_ofFn {B C : Type*} {n : ℕ}
    (f : Fin n → B) (g : B → C) (i : Fin n) (fallback : C) :
    ((Array.ofFn f).map g).getD i.val fallback = g (f i) := by
  simp [Array.getD, i.isLt]

end SubexponentialSAT.SubexpTaylorCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCeilingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual binary program for the packed dimension

Binary long division yields quotient and remainder. A finite zero test and
conditional increment then produce the ceiling. The input-dependent values are
stack words throughout; the control table is fixed.
-/

namespace SubexponentialSAT.SubexpCeilingProgram

abbrev Regs := Fin 8 → Bool

def runtimeBound (modulus input : List Bool) : ℕ :=
  100 * (modulus.length + input.length + 1) ^ 2 +
    8 * (modulus.length + 2 * input.length) + 16

end SubexponentialSAT.SubexpCeilingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupProgram

/-- The allocation and copy-list lengths are fixed when the setup program is
fixed, so this overhead is linear in the runtime word bound. -/
def storageOverhead (ports inputs outputs B : ℕ) : ℕ :=
  (2 * ports + outputs + 1) * (2 * B + 3) + (inputs + outputs) * (7 * B + 5) + 18

end SubexponentialSAT.SubexpSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI SubexpConvolutionControl

attribute [local simp] Fin.coe_ofNat_eq_mod

def decodeBasePort (i : Fin 896) : ℕ :=
  if i = 885 then 640 else if i = 886 then 641 else
  if i = 887 then 642 else if i = 888 then 647 else
  if i = 889 then 650 else if i = 890 then 651 else
  if i = 891 then 670 else if i = 892 then 671 else i.val

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI

def portIndex (j : ℕ) : ℕ :=
  if j = 862 then 0 else if j = 5 then 5 else if j = 12 then 12
  else if j = 850 then 15 else if j = 39 then 24 else if j = 280 then 27
  else if j = 212 then 28 else if j = 243 then 29 else if j = 128 then 36
  else j - 88

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

abbrev unary (n : ℕ) : List Bool := List.replicate n true

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSupportCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem powersetCard_pairwiseDisjoint (vars : Finset V) (J : ℕ) :
    (↑(Finset.range J) : Set ℕ).PairwiseDisjoint (fun j => vars.powersetCard j) := by
  intro i _ j _ hij
  exact vars.pairwise_disjoint_powersetCard hij

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalCoreProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The multiplication and predecessor prefix of the actual interval-start
initializer. All widths refer to physical input words, including padding. -/

namespace SubexponentialSAT.SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def width (r Q R : List Bool) : ℕ := r.length + Q.length + R.length + 1

end SubexponentialSAT.SubexpIntervalCoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalStartProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical binary initialization of the centered interval start

Three preserved input words encode r, Q, and R on ports 0, 1, and 2.
The fixed program computes ((Q-1)*(r-1)-R*r)/(2*r) using saturated
predecessors, products, saturated subtraction, and binary long division.
Only output port 3 differs on return; ports 4 through 31 are empty again.
-/

namespace SubexponentialSAT.SubexpIntervalStartProgram

open SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def value (r Q R : ℕ) : ℕ := ((Q - 1) * (r - 1) - R * r) / (2 * r)

end SubexponentialSAT.SubexpIntervalStartProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramLowMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit order conversion between the reverse high-incidence mask and the
forward low-variable mask consumed by head-identifier selection. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram.LowMask
open SubexponentialSAT

@[simp] theorem stacks_update0 (a b c : List Bool) :
    Function.update ![a,b] (0 : Fin 2) c = ![c,b] := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))
@[simp] theorem stacks_update1 (a b c : List Bool) :
    Function.update ![a,b] (1 : Fin 2) c = ![a,c] := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram.LowMask

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseRowProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An actual clause-row program

The input clause uses `Encoding.encodeList Encoding.encodeNat`. The stored
assignment is an explicit word of the declared length, one bit per variable.
The program parses each literal, decodes its unary index and polarity, performs
a preserving indexed read, and accumulates the disjunction. No semantic test is
an instruction. All auxiliary ports and all input requirements are explicit.
-/

namespace SubexponentialSAT.SubexpClauseRowProgram

def regs (value present sign acc : Bool) : Fin 4 → Bool :=
  fun i => if i = 0 then value else if i = 1 then present else if i = 2 then sign else acc

@[simp] theorem regs_0 (v p s a : Bool) : regs v p s a 0 = v := rfl
@[simp] theorem regs_1 (v p s a : Bool) : regs v p s a 1 = p := rfl
@[simp] theorem regs_2 (v p s a : Bool) : regs v p s a 2 = s := rfl
@[simp] theorem regs_3 (v p s a : Bool) : regs v p s a 3 = a := rfl
@[simp] theorem regs_update_0 (v p s a b : Bool) :
    Function.update (regs v p s a) 0 b = regs b p s a := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem regs_update_1 (v p s a b : Bool) :
    Function.update (regs v p s a) 1 b = regs v b s a := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem regs_update_2 (v p s a b : Bool) :
    Function.update (regs v p s a) 2 b = regs v p b a := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem regs_update_3 (v p s a b : Bool) :
    Function.update (regs v p s a) 3 b = regs v p s b := by
  funext i; fin_cases i <;> simp [regs]

/-- Array 0; temporary value 1; unary index 2; width 3; array scratch 4--7;
clause source 8; reversed literal payload 9. -/
def tapes (assignment output index width source payload : List Bool) : Fin 10 → List Bool :=
  fun i => if i = 0 then assignment else if i = 1 then output else if i = 2 then index
    else if i = 3 then width else if i = 8 then source else if i = 9 then payload else []

@[simp] theorem stacks_0 (a o i w s p : List Bool) : tapes a o i w s p 0 = a := rfl
@[simp] theorem stacks_1 (a o i w s p : List Bool) : tapes a o i w s p 1 = o := rfl
@[simp] theorem stacks_2 (a o i w s p : List Bool) : tapes a o i w s p 2 = i := rfl
@[simp] theorem stacks_3 (a o i w s p : List Bool) : tapes a o i w s p 3 = w := rfl
@[simp] theorem stacks_8 (a o i w s p : List Bool) : tapes a o i w s p 8 = s := rfl
@[simp] theorem stacks_9 (a o i w s p : List Bool) : tapes a o i w s p 9 = p := rfl
@[simp] theorem stacks_update_1 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 1 x = tapes a x i w s p := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem stacks_update_2 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 2 x = tapes a o x w s p := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem stacks_update_3 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 3 x = tapes a o i x s p := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem stacks_update_8 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 8 x = tapes a o i w x p := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem stacks_update_9 (a o i w s p x : List Bool) :
    Function.update (tapes a o i w s p) 9 x = tapes a o i w s x := by
  funext j; fin_cases j <;> simp [tapes]

end SubexponentialSAT.SubexpClauseRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiteralChunkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual literal-index to chunk-index conversion

The input is one reversed canonical unary literal field and a binary chunk
width. The fixed program decodes the variable index, counts it into binary,
divides by the chunk width, and constructs the reversed canonical chunk field.
-/

namespace SubexponentialSAT.SubexpLiteralChunkProgram

def tapes (ell unary binary remainder quotient payload encoded : List Bool) : Fin 19 → List Bool :=
  ![remainder, [], unary, [], binary, [], [], quotient, [], payload, encoded,
    [], [], [], [], [], [], [], ell]

end SubexponentialSAT.SubexpLiteralChunkProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpChunkRecordMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual map from literal records to chunk records

The input is the canonical encoded list of literal codes and a preserved binary
chunk width. Each parsed record passes through the actual index decoder,
counter, division program, and record writer. The accumulator is reversed, as
required by the separately checked record-reversal and stable-deduplication
passes. No semantic map is installed as a machine instruction.
-/

namespace SubexponentialSAT.SubexpChunkRecordMap

def regs (v pr found : Bool) : Fin 11 → Bool := fun i =>
  if i = 8 then v else if i = 9 then pr else if i = 10 then found else false

def tapes (ell source output payload : List Bool) : Fin 22 → List Bool := fun i =>
  if i = 9 then payload else if i = 18 then ell else if i = 19 then source
  else if i = 20 then output else []

end SubexponentialSAT.SubexpChunkRecordMap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLayoutFactorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical bounds for the actual clause-factor calls.  All envelopes are
polynomials in a common bound on the represented sizes and word lengths. -/

namespace SubexponentialSAT.SubexpLayoutConstructionBounds

abbrev Word := List Bool

end SubexponentialSAT.SubexpLayoutConstructionBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFlatCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Count decisions from the actual flat coefficient representation

Coefficients are stored constant-first, with four consecutive little-endian
words per coefficient. Width and modulus are runtime data. This adapter reads
the first word, discards the unused polynomial suffix, and executes the checked
remainder-and-positivity program. It does not serialize the array into records.
-/

namespace SubexponentialSAT.SubexpFlatCount

def budget (B : ℕ) (modulus input : List Bool) : ℕ :=
  16 * (input.length + B + 1) + 105 * (modulus.length + B + 1)^2 + 1

end SubexponentialSAT.SubexpFlatCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete unsigned tuple accumulation. The complete head product on852
is normalized into the pair accumulator851. Physical caches are copied from
retained masters and every native peripheral scratch word is paid for. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum

open OAI SqrtLog

def portIndex (j : ℕ) : ℕ :=
  if j = 5 then 5 else if j = 12 then 12 else if j = 39 then 24
  else if j = 851 then 15 else if j = 852 then 27 else j-100

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNegatedQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving complemented-literal queries

The clause iterator supplies a literal's unary word in reverse order. This
fixed program preserves that query on stack 0 and writes the reversed unary
word for the opposite literal on stack 1. Stacks 2 and 3 are empty workspaces
on entry and return. All costs below count actual finite-program transitions.
-/

namespace SubexponentialSAT.SubexpNegatedQueryProgram

/-- The four ports are original query, result, work, and scratch. -/
def slots (query result work scratch : List Bool) : Fin 4 → List Bool :=
  fun i => if i = 0 then query else if i = 1 then result else if i = 2 then work else scratch

@[simp] theorem slots_zero (a b c d : List Bool) : slots a b c d 0 = a := rfl
@[simp] theorem slots_one (a b c d : List Bool) : slots a b c d 1 = b := rfl
@[simp] theorem slots_two (a b c d : List Bool) : slots a b c d 2 = c := rfl
@[simp] theorem slots_three (a b c d : List Bool) : slots a b c d 3 = d := rfl

@[simp] theorem update_slots_one (a b c d e : List Bool) :
    Function.update (slots a b c d) 1 e = slots a e c d := by
  funext i
  fin_cases i <;> simp [slots]

@[simp] theorem update_slots_two (a b c d e : List Bool) :
    Function.update (slots a b c d) 2 e = slots a b e d := by
  funext i
  fin_cases i <;> simp [slots]

end SubexponentialSAT.SubexpNegatedQueryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyFilterProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual tautological-clause filtering

The outer record loop runs the checked clause-tautology machine on each clause,
emits exactly the clauses that it rejects as tautologies, and restores their
original list order. The Boolean predicates below specify this concrete code;
they are not instructions available to the machine.
-/

namespace SubexponentialSAT.SubexpTautologyFilterProgram

def perClauseCost (bits : List Bool) : ℕ := 250 * (bits.length + 1) ^ 2

end SubexponentialSAT.SubexpTautologyFilterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial time envelopes for the actual conditioned stream. The
same original assembled resource pays the support/tuple work; all remaining
scalars and retained words enter only fixed polynomial coefficients. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
open SqrtLog

def finishEnvelope (X : ℕ) : ℕ :=
  29*X+27+(41*(2*X+3)+30000*(X+2*X+X+X+X+1)^6+1)+
    6*(X+X*(X*(2*X)))+9+4*X+10


open SqrtLog



open Filter SqrtLog


open SqrtLog

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
end


