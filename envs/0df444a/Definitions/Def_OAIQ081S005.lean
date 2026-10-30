-- Prove2me | Definitions.Def_OAIQ081S005
-- name    : OAIQ081S005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:22:57.757602+00:00
-- url     : https://prove2.me/theorems/c777d50d-84a1-4bcf-b0d1-29bacd60d69c
-- title:
--   Definitions bundle OAIQ081S005 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 139 declarations of OpenAI's Lean: 85 definitions, 8 inductive types or structures and 46 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.defectValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.SmallWalsh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.adjacency`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.bitSign`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.character`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.fourier`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.graph`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.indicator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.walsh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.parameterValues`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.setupInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.unaryPairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.unaryPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell.frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.edge`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.QuotientPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.SqrtPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.quotientStackMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.sqrtBlock`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.sqrtStackMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.port`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.smallRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.work`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Instr`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.iterMajorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.lengthBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.majorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.workPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.lowWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter.nativeStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.ServiceStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.addTapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractTapes` and 53 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CRTLocalProgramExecution`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInverseTrace`, `SubexponentialSAT_SqrtLog_CRTLocalProgramLoops`, `SubexponentialSAT_SqrtLog_CayleyCharacters`, `SubexponentialSAT_SqrtLog_CayleyFourier`, `SubexponentialSAT_SqrtLog_CayleyGraph`, `SubexponentialSAT_SqrtLog_CodeParametersProgramBudget`, `SubexponentialSAT_SqrtLog_CodeParametersProgramUnary`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCell`, `SubexponentialSAT_SqrtLog_CodeRowsProgramSlots`, `SubexponentialSAT_SqrtLog_CodeRowsProgramVertex`, `SubexponentialSAT_SqrtLog_HornerProgramServices`, `SubexponentialSAT_SqrtLog_LeafParameterArithmetic`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBank`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnary`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LocalCodeWeight`, `SubexponentialSAT_SqrtLog_ReconstructionProgramRing`, `SubexponentialSAT_SqrtLog_RingScanAdd`, `SubexponentialSAT_SqrtLog_RingScanAddLoop`, `SubexponentialSAT_SqrtLog_RingScanContract`, `SubexponentialSAT_SqrtLog_RingScanContractLoop`, `SubexponentialSAT_SqrtLog_RingScanCount`, `SubexponentialSAT_SqrtLog_RingScanLoad`, `SubexponentialSAT_SqrtLog_RingScanServiceBasic`, `SubexponentialSAT_SqrtLog_RingTripleBasic`, `SubexponentialSAT_SqrtLog_RingTripleBridge`, `SubexponentialSAT_SqrtLog_SetupGuard`, `SubexponentialSAT_SqrtLog_SetupPrimitives`, `SubexponentialSAT_SqrtLog_SetupSearch`, `SubexponentialSAT_SqrtLog_SparseCodeBasic`, `SubexponentialSAT_SqrtLog_SparseCodeBounds`, `SubexponentialSAT_SqrtLog_SparseCodeMatrix`, `SubexponentialSAT_SqrtLog_SparseCodeParameters`, `SubexponentialSAT_SqrtLog_SparseCodeShorten`, `SubexponentialSAT_SqrtLog_SparseCodeTanner`, `SubexponentialSAT_SqrtLog_WalshExistence`, `SubexponentialSAT_SubexpBlockParameterProgram`, `SubexponentialSAT_SubexpConvolutionStore`, `SubexponentialSAT_SubexpEvaluationProgram`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_GatherProgram`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_PaddedCompletion`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_TupleProgram`, `SubexponentialSAT_Subexp_UnaryCompare`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S041`, `OAIQ081S042` and `OAIQ081S043`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionStore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

def bufferPorts : Fin 11 ↪ Fin 256 :=
  ⟨![100, 101, 102, 103, 105, 106, 108, 109, 110, 198, 199], by decide⟩

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramLoops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native loops used by independent-precision local Hermite CRT.

The arithmetic argument is a finite `Cmd`, never a semantic instruction.
`ServiceSpec` is the exact trace contract discharged by the native represented
ring/array callbacks. All iteration counts remain on runtime stack 246.
-/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.SubexpConvolutionControl

theorem iterate_mul_decode {C A : Type*} [Monoid A] (encode : C → A)
    (mul : C → C → C) (h : ∀ a b, encode (mul a b) = encode a * encode b)
    (a seed : C) (n : ℕ) :
    encode ((fun x => mul x a)^[n] seed) = encode seed * encode a ^ n := by
  induction n generalizing seed with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, h, pow_succ']
      simp only [mul_assoc]

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverseTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.SubexpConvolutionControl

def defectValue {C : Type*} (mulOp addOp : C → C → C) (a b minusOne one : C) : C :=
  addOp (mulOp (mulOp b a) minusOne) one

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition of the native local CRT scan, scalar inversion, and
polynomial correction. Service hypotheses refer to fixed finite commands;
they are instantiated by the concrete scalar and array service modules. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.SubexpConvolutionControl

def localWork : List (Fin 256) :=
  [100,101,102,107,108,120,121,122,205,208,215,217,218,219,220,222,223,
   224,227,228,229,240,241,242,244,245,246,247]

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CayleyCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Real Walsh characters of the Boolean cube, with unnormalized Fourier sums. -/
namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators

abbrev Cube (r : ℕ) := Fin r → ZMod 2

noncomputable def bitSign (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

@[simp] theorem bitSign_zero : bitSign 0 = 1 := by simp [bitSign]
@[simp] theorem bitSign_one : bitSign 1 = -1 := by norm_num [bitSign]

@[simp] theorem bitSign_sq (a : ZMod 2) : bitSign a ^ 2 = 1 := by
  simp only [bitSign]
  split_ifs <;> norm_num

noncomputable def character {r : ℕ} (a x : Cube r) : ℝ :=
  ∏ j, bitSign (a j * x j)

@[simp] theorem character_zero_left {r : ℕ} (x : Cube r) : character 0 x = 1 := by
  simp [character]

@[simp] theorem character_zero_right {r : ℕ} (a : Cube r) : character a 0 = 1 := by
  simp [character]

@[simp] theorem character_sq {r : ℕ} (a x : Cube r) : character a x ^ 2 = 1 := by
  rw [character, ← Finset.prod_pow]
  simp

@[simp] theorem cube_add_self {r : ℕ} (x : Cube r) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

@[simp] theorem cube_card (r : ℕ) : Fintype.card (Cube r) = 2 ^ r := by
  simp [Cube]

noncomputable def fourier {r : ℕ} (f : Cube r → ℝ) (a : Cube r) : ℝ :=
  ∑ x, f x * character a x

@[simp] theorem fourier_zero {r : ℕ} (f : Cube r → ℝ) : fourier f 0 = ∑ x, f x := by
  simp [fourier]

noncomputable def walsh {r : ℕ} {P : Type*} [Fintype P]
    (shifts : P → Cube r) (a : Cube r) : ℝ := ∑ i, character a (shifts i)

def SmallWalsh {r : ℕ} {P : Type*} [Fintype P] (shifts : P → Cube r) (ε : ℝ) : Prop :=
  ∀ a, a ≠ 0 → |walsh shifts a| ≤ ε * Fintype.card P

@[simp] theorem walsh_zero {r : ℕ} {P : Type*} [Fintype P] (shifts : P → Cube r) :
    walsh shifts 0 = Fintype.card P := by simp [walsh]

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CayleyFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators

variable {r : ℕ}

noncomputable def adjacency {P : Type*} [Fintype P] (shifts : P → Cube r)
    (f : Cube r → ℝ) (x : Cube r) : ℝ := ∑ i, f (x + shifts i)

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared interfaces for sparse ternary parity checks

The definitions distinguish edge coordinates from graph vertices. Parallel
edges have different ports. All construction theorems built on these interfaces
must eventually discharge the local-distance and graph-mixing hypotheses.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

abbrev F3 := ZMod 3

abbrev CheckMatrix (R C : Type*) := Matrix R C F3

section Words

variable {C R : Type*} [Fintype C]

def support (w : C → F3) : Finset C :=
  Finset.univ.filter fun c => w c ≠ 0

def weight (w : C → F3) : ℕ := (support w).card

@[simp] theorem mem_support (w : C → F3) (c : C) :
    c ∈ support w ↔ w c ≠ 0 := by
  simp [support]

@[simp] theorem support_zero : support (0 : C → F3) = ∅ := by
  simp [support]

@[simp] theorem weight_zero : weight (0 : C → F3) = 0 := by
  simp [weight]

@[simp] theorem weight_eq_zero_iff (w : C → F3) : weight w = 0 ↔ w = 0 := by
  simp only [weight, Finset.card_eq_zero]
  constructor
  · intro h
    funext c
    by_contra hc
    have : c ∈ support w := (mem_support w c).2 hc
    simp [h] at this
  · intro h
    simp [h]

def check (Q : CheckMatrix R C) (w : C → F3) (r : R) : F3 :=
  ∑ c, Q r c * w c

@[simp] theorem check_zero (Q : CheckMatrix R C) (r : R) :
    check Q 0 r = 0 := by
  simp [check]

end Words

/-- A regular bipartite graph represented by its bijection of left and right
ports. Edges are left ports. No simplicity assumption is made. -/
structure PortGraph (V P : Type*) where
  rotation : (V × P) ≃ (V × P)

namespace PortGraph

variable {V P : Type*} [Fintype V] [Fintype P] [DecidableEq V]

def leftWord (w : V × P → F3) (v : V) : P → F3 := fun p => w (v, p)

def rightWord (G : PortGraph V P) (w : V × P → F3) (v : V) : P → F3 :=
  fun p => w (G.rotation.symm (v, p))

end PortGraph

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CayleyGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A bipartite regular Cayley multigraph with explicit ordered ports.
Every pair `(x,i)` is a separate edge, including repeated shifts. -/
namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators
open SubexponentialSAT.SqrtLog.SparseCode

variable {r : ℕ} {P : Type*}

/-- The involutive port rotation retains the port even for parallel edges. -/
def graph (shifts : P → Cube r) : PortGraph (Cube r) P where
  rotation := {
    toFun := fun e => (e.1 + shifts e.2, e.2)
    invFun := fun e => (e.1 + shifts e.2, e.2)
    left_inv := by rintro ⟨x, i⟩; simp [add_assoc]
    right_inv := by rintro ⟨x, i⟩; simp [add_assoc] }

@[simp] theorem graph_rotation (shifts : P → Cube r) (x : Cube r) (i : P) :
    (graph shifts).rotation (x, i) = (x + shifts i, i) := rfl

@[simp] theorem graph_rotation_symm (shifts : P → Cube r) (x : Cube r) (i : P) :
    (graph shifts).rotation.symm (x, i) = (x + shifts i, i) := rfl

noncomputable def indicator (U : Finset (Cube r)) (x : Cube r) : ℝ :=
  if x ∈ U then 1 else 0

@[simp] theorem sum_indicator (U : Finset (Cube r)) :
    (∑ x, indicator U x) = (U.card : ℝ) := by
  classical
  simp [indicator]

@[simp] theorem sum_indicator_sq (U : Finset (Cube r)) :
    (∑ x, indicator U x ^ 2) = (U.card : ℝ) := by
  classical
  simp [indicator]

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A source-preserving floor quotient call using the audited finite binary
long-division program. Operands are runtime padded Boolean words. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

structure QuotientPorts (S : ℕ) where
  left : Fin S
  right : Fin S
  out : Fin S
  work : Fin 6 ↪ Fin S
  out_ne_left : out ≠ left
  out_ne_right : out ≠ right
  work_ne_left : ∀ i, work i ≠ left
  work_ne_right : ∀ i, work i ≠ right
  work_ne_out : ∀ i, work i ≠ out

@[simp] theorem quotient_right_ne_work {S : ℕ} (p : QuotientPorts S) (i : Fin 6) :
    p.right ≠ p.work i := (p.work_ne_right i).symm

@[simp] theorem quotient_out_ne_work {S : ℕ} (p : QuotientPorts S) (i : Fin 6) :
    p.out ≠ p.work i := (p.work_ne_out i).symm

@[simp] theorem quotient_right_ne_out {S : ℕ} (p : QuotientPorts S) :
    p.right ≠ p.out := p.out_ne_right.symm

def quotientStackMap {S : ℕ} (p : QuotientPorts S) : Fin 8 → Fin S :=
  ![p.work 0, p.work 1, p.work 2, p.work 3, p.work 4, p.right, p.work 5, p.out]

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpParameterProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs for the growing packing parameters

Numbers are little-endian Boolean stacks, with leading zeroes allowed. The
programs below manipulate only bits and stacks; natural-number quantities in
their specifications and cost bounds are not machine registers.
-/

namespace SubexponentialSAT.SubexpParameterProgram

/-! ## Consume a most-significant zero prefix and the leading one -/

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

def swapStacks : Equiv.Perm (Fin 3) := Equiv.swap 0 1

end SubexponentialSAT.SubexpParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual fixed bit programs for the two logarithmic setup quantities.
Input and output numbers are arbitrary padded little-endian words. -/
namespace SubexponentialSAT.SqrtLog.Setup

def incrementPorts : Fin 2 → Fin 3 := ![0, 1]

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Guard

def work : Fin 5 ↪ Fin 12 where
  toFun i := ⟨i.val + 6, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; simpa using this

def comparePorts : Fin 2 → Fin 12 := ![5,4]

end SubexponentialSAT.SqrtLog.Setup.Guard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Search

abbrev guardPorts : Fin 12 ↪ Fin 15 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 15 => x.val) h)

end SubexponentialSAT.SqrtLog.Setup.Search

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed runtime square-root and quotient interfaces for parameter pipelines.
All program syntax is fixed by the port maps, never by the operand values. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic


structure SqrtPorts (S : ℕ) where
  input : Fin S
  out : Fin S
  work : Fin 13 ↪ Fin S
  out_ne_input : out ≠ input
  work_ne_input : ∀ i, work i ≠ input
  work_ne_out : ∀ i, work i ≠ out

@[simp] theorem sqrt_input_ne_work {S : ℕ} (p : SqrtPorts S) (i : Fin 13) :
    p.input ≠ p.work i := (p.work_ne_input i).symm

@[simp] theorem sqrt_out_ne_work {S : ℕ} (p : SqrtPorts S) (i : Fin 13) :
    p.out ≠ p.work i := (p.work_ne_out i).symm

def sqrtStackMap {S : ℕ} (p : SqrtPorts S) : Fin 15 → Fin S :=
  ![p.work 0,p.work 1,p.input,p.work 2,p.work 3,p.work 4,p.work 5,p.work 6,
    p.work 7,p.work 8,p.work 9,p.work 10,p.out,p.work 11,p.work 12]

theorem sqrtStackMap_injective {S : ℕ} (p : SqrtPorts S) :
    Function.Injective (sqrtStackMap p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [sqrtStackMap,p.work.injective.eq_iff,p.work_ne_input,
      p.work_ne_out,p.out_ne_input,Ne.symm p.out_ne_input]

def sqrtBlock {S : ℕ} (p : SqrtPorts S) : Fin 15 ↪ Fin S :=
  ⟨sqrtStackMap p,sqrtStackMap_injective p⟩

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBlockParameterProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual block-size and block-threshold arithmetic

The three input words contain `s`, `delta`, and `Q`.  The width `k` is part
of the fixed code.  Seven high stacks are a reusable empty work bank; the
fifteen low stacks retain inputs, constants, and computed intermediate words.
Every arithmetic operation below invokes a proved finite Boolean program.
-/

namespace SubexponentialSAT.SubexpBlockParameterProgram

abbrev Regs := Fin 8 → Bool
abbrev Words := Fin 15 → List Bool

def port (i : Fin 15) : Fin 22 := i.castAdd 7

end SubexponentialSAT.SubexpBlockParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

abbrev Words := Fin 64 → List Bool

def port (i : Fin 64) : Fin 77 := i.castAdd 13

def work (m : ℕ) (hm : m ≤ 13) : Fin m ↪ Fin 77 where
  toFun i := ⟨64 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

@[simp] theorem work_val (m : ℕ) (hm : m ≤ 13) (i : Fin m) :
    (work m hm i).val = 64 + i.val := rfl


end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

def smallRegs : Fin 3 → Fin 8 := Fin.castAdd 5

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open Bank

/-- A finite arithmetic instruction table. All natural-number fields in this
type are code constants or physical port indices. Operand values reside in
Boolean stacks and are read by the concrete routines in `command`. -/
inductive Instr where
  | clear (a : Fin 64)
  | load (o : Fin 64) (bits : List Bool)
  | copy (a o : Fin 64) (h : o ≠ a)
  | add (a b o : Fin 64) (ha : o ≠ a) (hb : o ≠ b)
  | mul (a b o : Fin 64) (ha : o ≠ a) (hb : o ≠ b)
  | pow (a b o : Fin 64) (ha : o ≠ a) (hb : o ≠ b)
  | quot (a b o : Fin 64) (ha : o ≠ a) (hb : o ≠ b)
  | sqrt (a o : Fin 64) (h : o ≠ a)
  | logSucc (a : Fin 64)
  | addConst (a : Fin 64) (k : ℕ)
  | pred (a : Fin 64)
  | maxTwo (a : Fin 64)

def output : Instr → Fin 64
  | .clear a => a
  | .load o _ | .copy _ o _ | .add _ _ o _ _ | .mul _ _ o _ _
  | .pow _ _ o _ _ | .quot _ _ o _ _ | .sqrt _ o _ => o
  | .logSucc a | .addConst a _ | .pred a | .maxTwo a => a

def lengthBound (v l : Fin 64 → ℕ) : Instr → ℕ
  | .clear _ => 0
  | .load _ bits => bits.length
  | .copy a _ _ => l a
  | .add a b _ _ _ | .mul a b _ _ _ => l a+l b+1
  | .pow a b _ _ _ => 1+v b*l a
  | .quot a _ _ _ _ => l a
  | .sqrt a _ _ => v a
  | .logSucc a => l a+1
  | .addConst a k => l a+k
  | .pred a => l a
  | .maxTwo a => l a+2

def cost (v l : Fin 64 → ℕ) : Instr → ℕ
  | .clear a => 2*l a+3
  | .load _ bits => 2*bits.length
  | .copy a _ _ => 7*l a+5
  | .add a b _ _ _ | .mul a b _ _ _ => 100*(l a+l b+1)^2
  | .pow a b _ _ _ => v b*(50*(l a+1)*(2+(v b+1)*l a))+
      (v b+1)*(16*l b+16)+3+9*l b+8
  | .quot a b _ _ _ => 150*(l a+l b+1)^2
  | .sqrt a _ _ => 200001*(v a+l a+2)^3
  | .logSucc a => 32*(l a+1)^2+4
  | .addConst a k => 8*k*(l a+k+1)+4
  | .pred a => 20*(l a+1)
  | .maxTwo a => 100*(l a+3)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitRun -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open Bank

structure Model where
  val : Fin 64 → ℕ
  len : Fin 64 → ℕ

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

def majorant (B : ℕ) : ℕ := 10000000*(B+2)^6

def iterMajorant : ℕ → ℕ → ℕ
  | 0,B => B
  | n+1,B => iterMajorant n (majorant B)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutCost -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

/-- An integer upper binary logarithm sufficient for every construction bound. -/
def logSize (m : ℕ) : ℕ := Nat.log 2 m + 1

theorem lt_two_pow_logSize (m : ℕ) : m < 2 ^ logSize m := by
  exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) m

def gapDenom (m B : ℕ) : ℕ := 200 * B * logSize m

def degreeBound (m B : ℕ) : ℕ := 8 * gapDenom m B ^ 2 * logSize m

def degree (m B : ℕ) : ℕ := min m (degreeBound m B)

theorem exists_dimension (m : ℕ) {D : ℕ} (hD : 0 < D) :
    ∃ r : ℕ, m ≤ D * 2 ^ r := by
  refine ⟨logSize m, ?_⟩
  have hm := lt_two_pow_logSize m
  nlinarith

/-- Total increasing search for the first power-of-two vertex count whose
edge count covers the requested columns. The zero-degree default is never
used by the nonempty construction. -/
def dimensionFor (m D : ℕ) : ℕ :=
  if hD : 0 < D then Nat.find (exists_dimension m hD) else 0

def dimension (m B : ℕ) : ℕ := dimensionFor m (degree m B)

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

def localRows (m B : ℕ) : ℕ := degree m B / (8 * B) + 1

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production sparse-code parameter program. Fixed arithmetic, minimum,
metadata identities and unary materialization are checked in one unit. -/

/-! Arithmetic identities used by the physical sparse-code parameter program. -/


/-! A concrete minimum operation used between two straight-line arithmetic
stages. The comparison consumes only two explicitly copied temporary words. -/


/-! Fixed finite arithmetic instructions for all sparse-code search metadata.
Ports 0 and 1 contain m and B. Outputs: q=5, D=9, t=11, tD=12,
local distance=15, r=18, rD=19, N=21. Unary conversion is a separate,
explicitly paid stage. -/


/-! Explicit paid binary-to-unary copies for code-search metadata. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open LeafParametersProgram.Bank

/-- Each pair is (binary source, unary destination). Binary source words are
retained. Destination slots24--30 and temporary slot62 start empty. -/
def unaryPairs : List (Fin 64 × Fin 64) :=
  [(9,24),(11,25),(12,26),(15,27),(18,28),(19,29),(21,30)]

def unaryPorts : Fin 7 → Fin 64 := ![24,25,26,27,28,29,30]
def parameterValues (m B : ℕ) : Fin 7 → ℕ :=
  ![SparseCode.degree m B,SparseCode.localRows m B,
    SparseCode.localRows m B*SparseCode.degree m B,
    SparseCode.degree m B/(100*B*SparseCode.logSize m)+1,
    SparseCode.dimension m B,SparseCode.dimension m B*SparseCode.degree m B,
    2^SparseCode.dimension m B]

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordinary-polynomial cost of the actual sparse-code metadata producer.
The two exhaustive code searches have separate costs; this file accounts
for the fixed arithmetic table and all seven unary materializations. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open LeafParametersProgram.Circuit


def setupInput (m ml Bl : ℕ) : ℕ := m+ml+Bl+16

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

abbrev Records := List (List Bool)

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

def cartesianOutput (tuples alphabet : Records) : Records :=
  (tuples.flatMap fun tuple => alphabet.map (tuple ++ ·)).reverse

abbrev powerRows (alphabet : Records) : ℕ → Records → Records
  | 0, rows => rows
  | n + 1, rows => powerRows alphabet n (cartesianOutput rows alphabet)

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GatherProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program gathering runtime-selected rows

The packed assignment is on stack 0 and its unary row width on stack 3.
Stack 8 contains `ProgramEncoding.encodeRecords` of unary index words.
The program preserves the assignment and width and writes the selected rows,
in plan order, to stack 1. All widths and indices are stack data.
-/

namespace SubexponentialSAT.Subexp.GatherProgram

def indexRecords (plan : List ℕ) : List (List Bool) :=
  plan.map (fun i => List.replicate i true)

def gathered (rows : List (List Bool)) (plan : List ℕ) : List Bool :=
  plan.flatMap (fun i => rows.getD i [])

end SubexponentialSAT.Subexp.GatherProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PaddedCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit padded completion leaves

Every optional coordinate branches over the entire word alphabet. A real
coordinate updates the assignment; a dummy coordinate ignores the word.
Padding therefore implements the common-denominator multiplicity by actual
finite leaves rather than a multiplication of the resulting score.
-/

namespace SubexponentialSAT.Subexp.PaddedCompletion

variable {I W J : Type*} [DecidableEq I]

/-- The natural value of a successful or unsuccessful collision test. -/
def boolValue (b : Bool) : ℕ := if b then 1 else 0

/-- A unary score is the list of successful Boolean leaves. -/
def successful (bs : List Bool) : List Bool := bs.filter id

def trueCount (bs : List Bool) : ℕ := (successful bs).length

@[simp] theorem trueCount_singleton (b : Bool) :
    trueCount [b] = boolValue b := by
  cases b <;> rfl

end SubexponentialSAT.Subexp.PaddedCompletion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionTupleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Streaming collisions from framed runtime tuples

The current word array and selected read plans are preserved. Each parsed
tuple is appended to the current array by actual transfer/copy routines, then
the fixed collision callback gathers the two types and emits one bit.
-/

namespace SubexponentialSAT.Subexp.CollisionTupleProgram

def byteGather (table : List Bool) (width : ℕ) (plan : List ℕ) : List Bool :=
  plan.flatMap fun i => (table.drop (i * width)).take width

def leafBit (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuple : List Bool) : Bool :=
  decide (byteGather (current ++ tuple) width left = byteGather (current ++ tuple) width right)

def streamed (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) : List Bool :=
  tuples.foldl (fun acc bits => leafBit current width left right bits :: acc) stream

end SubexponentialSAT.Subexp.CollisionTupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UnaryCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for exact conditional-score comparisons

The local conditional scores admit bounded natural numerators. Unary storage
is therefore already polynomial in the growing parameters. This module gives
an actual fixed finite instruction table comparing two stack lengths and
connects its measured execution to those conditional scores.
-/

namespace SubexponentialSAT.Subexp.UnaryCompare

/-- A unary natural is represented only by its stack length. -/
def encode (n : ℕ) : List Bool := List.replicate n false

@[simp] theorem encode_length (n : ℕ) : (encode n).length = n := by
  simp [encode]

end SubexponentialSAT.Subexp.UnaryCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Aggregating the actual collision streams of all vertex pairs

The fixed program consumes framed pairs of already selected read plans.
Producing those selected plans from original plans and the remaining-index
table is a separate preparation step.  Every pair invokes the actual tuple
generator and collision machine; a final fixed unary tally produces the score.
-/

namespace SubexponentialSAT.Subexp.PairScoreProgram

abbrev PlanPair := List ℕ × List ℕ

structure Context where
  current : List (List Bool)
  width : List Bool
  alphabet : List (List Bool)
  depth : List Bool

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native five-pop decoder for the scalar frames emitted by code search.
It consumes one frame and exposes its two little-endian scalar bits. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell
def frame (a b : Bool) : List Bool := [true,a,true,b,false]

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Elementary low-weight counting by successive single-coordinate updates. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

def lowWords (D h : ℕ) : Finset (Fin D → F3) :=
  Finset.univ.filter fun w => weight w ≤ h

@[simp] theorem mem_lowWords {D h : ℕ} (w : Fin D → F3) :
    w ∈ lowWords D h ↔ weight w ≤ h := by simp [lowWords]

@[simp] theorem zero_mem_lowWords (D h : ℕ) : (0 : Fin D → F3) ∈ lowWords D h := by
  simp

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeTanner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

namespace PortGraph

variable {V P R : Type*} [Fintype V] [Fintype P]
    [DecidableEq V] [DecidableEq P]

def leftActive (w : V × P → F3) : Finset V :=
  Finset.univ.filter fun v => leftWord w v ≠ 0

def rightActive (G : PortGraph V P) (w : V × P → F3) : Finset V :=
  Finset.univ.filter fun v => G.rightWord w v ≠ 0

omit [DecidableEq V] [DecidableEq P] in
@[simp] theorem mem_leftActive (w : V × P → F3) (v : V) :
    v ∈ leftActive w ↔ leftWord w v ≠ 0 := by simp [leftActive]

omit [DecidableEq V] [DecidableEq P] in
@[simp] theorem mem_rightActive (G : PortGraph V P) (w : V × P → F3) (v : V) :
    v ∈ G.rightActive w ↔ G.rightWord w v ≠ 0 := by simp [rightActive]

end PortGraph

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode.PortGraph

open scoped BigOperators

variable {V P R : Type*} [Fintype V] [Fintype P]
    [DecidableEq V] [DecidableEq P]

/-- One explicit check row for each vertex and each local check, on both
sides of the bipartite graph. -/
def matrix (G : PortGraph V P) (Q : CheckMatrix R P) :
    CheckMatrix ((V × R) ⊕ (V × R)) (V × P)
  | Sum.inl (v, r), e => if e.1 = v then Q r e.2 else 0
  | Sum.inr (v, r), e => if (G.rotation e).1 = v then Q r (G.rotation e).2 else 0

omit [DecidableEq P] in
@[simp] theorem check_matrix_left (G : PortGraph V P) (Q : CheckMatrix R P)
    (w : V × P → F3) (v : V) (r : R) :
    check (G.matrix Q) w (Sum.inl (v, r)) = check Q (leftWord w v) r := by
  simp [check, matrix, Fintype.sum_prod_type, leftWord, ite_mul]

omit [DecidableEq P] in
@[simp] theorem check_matrix_right (G : PortGraph V P) (Q : CheckMatrix R P)
    (w : V × P → F3) (v : V) (r : R) :
    check (G.matrix Q) w (Sum.inr (v, r)) = check Q (G.rightWord w v) r := by
  calc
    _ = ∑ e : V × P, (if e.1 = v then Q r e.2 else 0) * w (G.rotation.symm e) := by
      simpa [check, matrix] using
        G.rotation.sum_comp
          (fun e : V × P => (if e.1 = v then Q r e.2 else 0) * w (G.rotation.symm e))
    _ = _ := by simp [check, rightWord, Fintype.sum_prod_type, ite_mul]

end SubexponentialSAT.SqrtLog.SparseCode.PortGraph

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeShorten
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

variable {C E R : Type*} [Fintype C] [Fintype E]
    [DecidableEq C] [DecidableEq E]

/-- Executable zero extension along an embedding. Finite summation avoids
any choice of an inverse for an index outside the image. -/
def zeroExtend (e : C ↪ E) (w : C → F3) : E → F3 :=
  fun z => ∑ c, if e c = z then w c else 0

omit [Fintype E] in
@[simp] theorem zeroExtend_apply (e : C ↪ E) (w : C → F3) (c : C) :
    zeroExtend e w (e c) = w c := by
  simp [zeroExtend, e.injective.eq_iff]

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Existence and finite executable search for a small Walsh spectrum. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

/-- The integer counterpart makes the predicate executable. -/
def characterInt {r : ℕ} (a x : Cube r) : ℤ :=
  ∏ j, if a j * x j = 0 then 1 else -1

def walshInt {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) : ℤ :=
  ∑ i, characterInt a (s i)

@[simp] theorem characterInt_cast {r : ℕ} (a x : Cube r) :
    (characterInt a x : ℝ) = character a x := by
  simp [characterInt, character, bitSign]

@[simp] theorem walshInt_cast {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) :
    (walshInt s a : ℝ) = walsh s a := by
  simp [walshInt, walsh]

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse local-slot specifications. A row lists at most D original clause
indices, including any zero coefficients; shortening only removes slots whose
actual shifted edge index lies outside the original m coordinates. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

def edge (shifts : Fin D → Cayley.Cube r) (side : Bool) (v : Cayley.Cube r)
    (p : Fin D) : Cayley.Cube r × Fin D :=
  (if side then v+shifts p else v,p)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

def vertexBits {r : ℕ} (v : Cayley.Cube r) : List Bool :=
  List.ofFn fun i => decide (v i=1)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving CRT adapters for the native arbitrary-degree ring
programs. The adapter is a fixed finite table. Its cost includes three input
copies, the actual native trace, output copying and cleanup. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

open SubexponentialSAT SubexpConvolutionControl

def nativeStacks (modulus width zero table result x y degree : List Bool) :
    Fin 32 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (fun _ => [])
      0 result) 5 modulus) 8 x) 9 y) 11 degree) 12 width) 17 zero) 22 table

end SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed-control dynamic coefficient loader

The source contains a flat vector. A preserved unary width word determines
how many bits are removed. Exactly that many bits are prefixed, in their
original order, to the destination. Control size is independent of both the
width and the number of coefficients.
-/
namespace SubexponentialSAT.SqrtLog.RingScan

def loadTapes (src dst width count scratch : List Bool) : Fin 5 → List Bool :=
  ![src, dst, width, count, scratch]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar addition inside a flat, runtime-sized coefficient scan. -/
namespace SubexponentialSAT.SqrtLog.RingScan

/-- The lower eight stacks are precisely the audited scalar ABI. The remaining
seven contain the flat input vectors, output accumulator, and unary controls. -/
def addTapes (modulus left right xs ys out count width : List Bool) : Fin 15 → List Bool :=
  fun i => if i = 0 then left else if i = 1 then right else if i = 5 then modulus
    else if i = 8 then xs else if i = 9 then ys else if i = 10 then out
    else if i = 11 then count else if i = 12 then width else []

theorem update_self_regs (regs : Fin 8 → Bool) :
    Function.update (Function.update regs 1 (regs 1)) 3 (regs 3) = regs := by
  simp

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAddLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The vector length is a unary input, never a generated list of instructions. -/
namespace SubexponentialSAT.SqrtLog.RingScan

theorem update_count (modulus left right xs ys out count width next : List Bool) :
    Function.update (addTapes modulus left right xs ys out count width) 11 next =
      addTapes modulus left right xs ys out next width := by
  funext i
  by_cases hi : i = 11
  · subst i; simp [addTapes]
  · simp [addTapes, hi]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed outer loop contracts a runtime-sized sequence of triple blocks. -/
namespace SubexponentialSAT.SqrtLog.RingScan

def contractTapes (modulus left stream count width outer inner zero out : List Bool) :
    Fin 20 → List Bool := fun i =>
  if i = 0 then left else if i = 5 then modulus else if i = 9 then stream
  else if i = 11 then count else if i = 12 then width else if i = 15 then outer
  else if i = 16 then inner else if i = 17 then zero else if i = 18 then out else []

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContractLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native whole-vector contraction, with both dimensions held on data tapes. -/
namespace SubexponentialSAT.SqrtLog.RingScan

theorem update_outer (modulus left stream count width outer inner zero out next : List Bool) :
    Function.update (contractTapes modulus left stream count width outer inner zero out) 15 next =
    contractTapes modulus left stream count width next inner zero out := by
  funext i; by_cases h : i = 15
  · subst i; simp [contractTapes]
  · simp [contractTapes, h]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native loop produces a unary square from a unary input. -/
namespace SubexponentialSAT.SqrtLog.RingScan

def countTapes (source counter out : List Bool) : Fin 4 → List Bool := ![source, counter, out, []]

def repeatCount (source : List Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => source ++ repeatCount source n

@[simp] theorem repeatCount_length (source : List Bool) (n : ℕ) :
    (repeatCount source n).length = n*source.length := by
  induction n with
  | zero => simp [repeatCount]
  | succ n ih => simp [repeatCount, ih, Nat.add_mul, Nat.add_comm]

theorem repeatCount_append (source : List Bool) (n : ℕ) :
    repeatCount source n ++ source = source ++ repeatCount source n := by
  induction n with
  | zero => simp [repeatCount]
  | succ n ih => simp only [repeatCount, List.append_assoc, ih]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port primitives for dynamic Cartesian triple expansion. All loop
bounds and coefficient widths are words on stacks, not generated code. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

structure Store where
  x : List Bool
  y : List Bool
  table : List Bool
  out : List Bool
  xs : List Bool
  ys : List Bool
  held : List Bool
  degree : List Bool
  kc : List Bool
  ic : List Bool
  jc : List Bool
  width : List Bool

def tapes (s : Store) : Fin 16 → List Bool :=
  ![s.x, s.y, s.table, s.out, s.xs, s.ys, s.held, [], [],
    s.degree, s.kc, s.ic, s.jc, s.width, [], []]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The input/output of the dynamic expander is exactly the k-major table and
triple stream used by the native ring contraction. `List.ofFn` below describes
the serialized input and theorem; the fixed program builds the repeated stream
by actual counted loops and paid source copies. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

def layout (x y degree width : List Bool) : Store where
  x := x
  y := y
  table := []
  out := []
  xs := []
  ys := []
  held := []
  degree := degree
  kc := []
  ic := []
  jc := []
  width := width

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared native coefficient-ring ABI. All service programs have fixed size. -/
namespace SubexponentialSAT.SqrtLog.RingScan

/-- Public ports are result0, modulus5, operands8/9, degree11, width12,
base scalar zero17, and cached k-major table22. Other fields are private work. -/
structure ServiceStore where
  modulus : List Bool
  result : List Bool
  x : List Bool
  y : List Bool
  degree : List Bool
  width : List Bool
  zero : List Bool
  table : List Bool
  outer : List Bool := []
  inner : List Bool := []
  tableWork : List Bool := []
  reverseStream : List Bool := []
  stream : List Bool := []

def serviceTapes (s : ServiceStore) : Fin 32 → List Bool := fun i =>
  if i = 0 then s.result else if i = 5 then s.modulus
  else if i = 8 then s.x else if i = 9 then s.y else if i = 11 then s.degree
  else if i = 12 then s.width else if i = 15 then s.outer else if i = 16 then s.inner
  else if i = 17 then s.zero else if i = 20 then s.tableWork
  else if i = 21 then s.reverseStream else if i = 22 then s.table
  else if i = 23 then s.stream else []

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramServices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully discharged native binary services for arbitrary coefficient-vector
length. Shared by Horner, local CRT and dense polynomial services. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram.Services

open SubexponentialSAT SubexpConvolutionControl

theorem nativeStacks_eq (modulus width zero table result x y degree : List Bool) :
    ReconstructionProgram.RingAdapter.nativeStacks modulus width zero table result x y degree =
      RingScan.serviceTapes ⟨modulus, result, x, y, degree, width, zero, table, [], [], [], [], []⟩ := by
  first | done | (funext i; fin_cases i <;> rfl)

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def workPorts : List (Fin 640) :=
  (List.finRange 223).map fun i => ⟨417+i.val, by omega⟩


end SubexponentialSAT.SqrtLog.LeafRingSetupProgram


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete evaluation-result extraction

The extractor removes the singleton operand-list framing, parses the result
payload into a reversed scratch stack, and transfers it to physical stack 15.
It clears the operand/depth/scratch stacks and preserves every other stack.
-/

namespace SubexponentialSAT.SubexpEvaluationProgram

def parserLabel (i : Fin 7) : Fin 17 := Fin.natAdd 3 (Fin.castAdd 7 i)

/-! ## Entry from arbitrary caller registers -/

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

abbrev Word := List Bool

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end


