-- Prove2me | Definitions.Def_OAIQ081S026
-- name    : OAIQ081S026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:29:46.134993+00:00
-- url     : https://prove2.me/theorems/71357256-b349-43cd-84e2-2cd68fa98e4f
-- title:
--   Definitions bundle OAIQ081S026 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 185 declarations of OpenAI's Lean: 92 definitions, 1 inductive type or structure, 10 instances and 82 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.LiftRing.coordinates`, `OAI.Algorithms.SubexponentialSAT.LocalSpectrum.kernelMap`, `OAI.Algorithms.SubexponentialSAT.LocalSpectrum.positionMap`, `OAI.Algorithms.SubexponentialSAT.LocalSpectrum.swapAt`, `OAI.Algorithms.SubexponentialSAT.ModularPrograms.reverseOutput`, `OAI.Algorithms.SubexponentialSAT.ModularQuotientArithmetic.divide`, `OAI.Algorithms.SubexponentialSAT.ModularQuotientArithmetic.quotientBit`, `OAI.Algorithms.SubexponentialSAT.ModularQuotientLift.quotientStacksAt`, `OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms.divideFrom`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Joint`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Side`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Spectator`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.equivProd`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.joint`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.jointEquivPairs`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.pinHead`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.pinSlot`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.side`, `OAI.Algorithms.SubexponentialSAT.ParserProgram.restoreProgram`, `OAI.Algorithms.SubexponentialSAT.PowerPrograms.nextAccumulator`, `OAI.Algorithms.SubexponentialSAT.PowerPrograms.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.PowerPrograms.workBound`, `OAI.Algorithms.SubexponentialSAT.ProgramLogic.registerWrites`, `OAI.Algorithms.SubexponentialSAT.ProgramLogic.stackWrites`, `OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms.unread`, `OAI.Algorithms.SubexponentialSAT.RegisterResetProgram.all`, `OAI.Algorithms.SubexponentialSAT.RegisterResetProgram.clear`, `OAI.Algorithms.SubexponentialSAT.RegisterResetProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.RegisterResetProgram.zeroed`, `OAI.Algorithms.SubexponentialSAT.RemovalCharging.literalUniverse`, `OAI.Algorithms.SubexponentialSAT.SAT.Clause.IsTautology`, `OAI.Algorithms.SubexponentialSAT.SAT.OccurrenceAtMost`, `OAI.Algorithms.SubexponentialSAT.SAT.Satisfiable`, `OAI.Algorithms.SubexponentialSAT.SAT.absorb`, `OAI.Algorithms.SubexponentialSAT.SAT.normalize`, `OAI.Algorithms.SubexponentialSAT.SAT.occurrences`, `OAI.Algorithms.SubexponentialSAT.SAT.removeTautologies`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.saturated`, `OAI.Algorithms.SubexponentialSAT.SlotAssignment.Incident` and 53 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_LiftRing`, `SubexponentialSAT_LocalSpectrum`, `SubexponentialSAT_ModularPrograms`, `SubexponentialSAT_ModularQuotientArithmetic`, `SubexponentialSAT_ModularQuotientLift`, `SubexponentialSAT_ModularQuotientPrograms`, `SubexponentialSAT_MulticolorTypes`, `SubexponentialSAT_ParserProgram`, `SubexponentialSAT_PowerPrograms`, `SubexponentialSAT_ProgramLogic`, `SubexponentialSAT_RecordMappedPrograms`, `SubexponentialSAT_RecordPrograms`, `SubexponentialSAT_RegisterResetProgram`, `SubexponentialSAT_RemovalCharging`, `SubexponentialSAT_SAT`, `SubexponentialSAT_SaturatingSubtractionProgram`, `SubexponentialSAT_SlotAssignment`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_BinaryArgmin`, `SubexponentialSAT_SqrtLog_BucketProgramArithmetic`, `SubexponentialSAT_SqrtLog_BucketProgramDot`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep`, `SubexponentialSAT_SqrtLog_BucketProgramProducedRankLiteral`, `SubexponentialSAT_SqrtLog_BucketProgramRow`, `SubexponentialSAT_SqrtLog_BucketProgramSignature`, `SubexponentialSAT_SqrtLog_LayoutBlocks`, `SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithmEntry`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowScan`, `SubexponentialSAT_SqrtLog_LayoutProducedMatrix`, `SubexponentialSAT_SqrtLog_LayoutProgramDispatch`, `SubexponentialSAT_SqrtLog_PackingWords`, `SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic`, `SubexponentialSAT_SqrtLog_RowSelectionProgramParser`, `SubexponentialSAT_SqrtLog_RowSelectionProgramTotal`, `SubexponentialSAT_SubexpJetCellProgram`, `SubexponentialSAT_Subexp_CollisionProgram`, `SubexponentialSAT_Subexp_ConstructivePacking`, `SubexponentialSAT_Subexp_MatrixEntryKernel`, `SubexponentialSAT_Subexp_MatrixEntryScalar`, `SubexponentialSAT_Subexp_MatrixExtendedEntrySemantics`, `SubexponentialSAT_Subexp_MatrixSupport`, `SubexponentialSAT_Subexp_ReadPlan`, `SubexponentialSAT_Subexp_TypeEnumeration`, `SubexponentialSAT_WorkspaceCleanupProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002` and `OAIQ081S003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S062` and `OAIQ081S064`; the statements `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_accepted_command_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds_accepted_inputs` and `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds_trial_inputs`; the proofs of `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_accepted_command_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_accepted_command_kept_frame`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds_accepted_inputs` and `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds_trial_inputs`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LiftRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The finite free ring used for prime-power counting

This file constructs the quotient by a monic polynomial, proves that a
positive-degree quotient retains the base ring, and constructs coefficient
reduction maps between these polynomial quotient rings.
-/

namespace SubexponentialSAT.LiftRing

noncomputable section

open Polynomial

section General

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Every residue class has one and only one vector of coefficients below
the degree of the monic defining polynomial. -/
noncomputable def coordinates {F : R[X]} (hF : F.Monic) :
    Extension F ≃ₗ[R] (Fin F.natDegree → R) := by
  classical
  exact
    { toFun := fun x i => (remainder hF x).coeff i
      invFun := fun c => mk F (∑ i : Fin F.natDegree, monomial i (c i))
      map_add' := fun x y => by
        funext i
        simp only [map_add, coeff_add, Pi.add_apply]
      map_smul' := fun a x => by
        funext i
        simp only [map_smul, coeff_smul, Pi.smul_apply, RingHom.id_apply]
      left_inv := fun x => by
        obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
        change mk F (∑ i : Fin F.natDegree,
          monomial i ((remainder hF (mk F q)).coeff i)) = mk F q
        simp only [remainder_mk, sum_modByMonic_coeff hF degree_le_natDegree]
        rw [mk_eq_mk, modByMonic_eq_sub_mul_div, sub_sub_cancel_left, dvd_neg]
        exact dvd_mul_right _ _
      right_inv := fun c => by
        funext i
        nontriviality R
        simp only [remainder_mk]
        rw [(modByMonic_eq_self_iff hF).mpr, finsetSum_coeff]
        · simp_rw [coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq',
            ite_eq_left (Finset.mem_univ _)]
        · simp_rw [← C_mul_X_pow_eq_monomial]
          exact (degree_eq_natDegree hF.ne_zero).symm ▸ degree_sum_fin_lt _ }

/-- A finite coefficient ring yields a genuinely finite quotient ring. -/
theorem extension_finite_type [Finite R] {F : R[X]} (hF : F.Monic) :
    Finite (Extension F) :=
  Finite.of_injective (coordinates hF) (coordinates hF).injective

end General

end

end SubexponentialSAT.LiftRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LocalSpectrum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The four-state involution in the interpolation layout

This file constructs the operator rather than assuming a spectral decomposition.
The only characteristic hypothesis on the field is that `2 ≠ 0`.
-/

namespace SubexponentialSAT.LocalSpectrum

section Positions

variable {ι : Type*} [DecidableEq ι]

/-- Change the bit pair at just one position. -/
def swapAt (l : ι) (x : ι → PairState) : ι → PairState :=
  Function.update x l (swapPair (x l))

@[simp] theorem swapAt_same (l : ι) (x : ι → PairState) :
    swapAt l x l = swapPair (x l) := by simp [swapAt]

@[simp] theorem swapAt_other {l j : ι} (h : j ≠ l) (x : ι → PairState) :
    swapAt l x j = x j := by simp [swapAt, h]

@[simp] theorem swapAt_involutive (l : ι) (x : ι → PairState) :
    swapAt l (swapAt l x) = x := by
  funext j
  by_cases h : j = l
  · subst j; simp
  · simp [swapAt_other h]

variable (K : Type*) [Field K]

/-- The actual permutation operator on all assignments of the separate positions. -/
def positionMap (l : ι) : Module.End K ((ι → PairState) → K) where
  toFun f x := f (swapAt l x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem positionMap_apply (l : ι) (f : (ι → PairState) → K)
    (x : ι → PairState) : positionMap K l f x = f (swapAt l x) := rfl

@[simp] theorem positionMap_sq (l : ι) : positionMap K l * positionMap K l = 1 := by
  ext f x
  exact congrArg f (swapAt_involutive l x)

end Positions

section ProductBasis

open scoped BigOperators

variable (K : Type*) [Field K]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Actual linear action of a finite matrix represented by its entries. -/
def kernelMap (A : Ω → Ω → K) : Module.End K (Ω → K) where
  toFun f x := ∑ y, A x y * f y
  map_add' f g := by
    ext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp [Finset.mul_sum, mul_left_comm ]

theorem kernelMap_inverse (A B : Ω → Ω → K)
    (h : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (f : Ω → K) : kernelMap K A (kernelMap K B f) = f := by
  classical
  funext x
  change (∑ y, A x y * ∑ z, B y z * f z) = f x
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, h]
  simp

end ProductBasis

end SubexponentialSAT.LocalSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete finite CNF syntax and semantics for the candidate SAT argument. -/

namespace SubexponentialSAT.SAT

universe u

variable {V : Type u}

variable [DecidableEq V]

def Satisfiable (F : CNF V) : Prop := ∃ a : Assignment V, F.eval a = true

section Decidable

def occurrences (v : V) (F : CNF V) : ℕ :=
  (F.filter fun C => ∃ l ∈ C, l.variable = v).card

def OccurrenceAtMost (B : ℕ) (F : CNF V) : Prop := ∀ v, occurrences v F ≤ B

/-- A clause containing both polarities of a literal. -/
abbrev Clause.IsTautology (C : Clause V) : Prop := ∃ l ∈ C, l.negate ∈ C

def removeTautologies (F : CNF V) : CNF V :=
  F.filter fun C => ¬ C.IsTautology

/-- Keep exactly the clauses having no strict subset among the clauses of `F`. -/
def absorb (F : CNF V) : CNF V :=
  F.filter fun C => ¬ ∃ D ∈ F, D ⊂ C

theorem absorb_subset (F : CNF V) : absorb F ⊆ F := Finset.filter_subset _ _

theorem absorb_antichain {F : CNF V} {C D : Clause V}
    (hC : C ∈ absorb F) (hD : D ∈ absorb F) (hDC : D ⊆ C) : D = C := by
  by_contra hne
  exact (Finset.mem_filter.mp hC).2
    ⟨D, (Finset.mem_filter.mp hD).1, Finset.ssubset_iff_subset_ne.mpr ⟨hDC, hne⟩⟩

def normalize (F : CNF V) : CNF V := absorb (removeTautologies F)

end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite Boolean-stack programs for modular arithmetic

The programs in this file use only a fixed finite collection of labels,
Boolean registers, and Boolean stacks. The operand width and modulus are data.
-/

namespace SubexponentialSAT.ModularPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic

/-- Reorient the reversed result while preserving the borrow register. -/
abbrev reverseOutput : Program 8 3 4 :=
  SubexponentialSAT.StackRoutines.transferProgram 2 0 1 3

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

end SubexponentialSAT.ModularPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularQuotientArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The quotient bits emitted by binary long division

These bit/list functions specify the output of the finite division program.
Each quotient bit is the complement of the actual subtraction borrow; neither
the recurrence nor the bit selector calls natural-number division.
-/

namespace SubexponentialSAT.ModularQuotientArithmetic

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic

def quotientBit (m r : List Bool) (b : Bool) : Bool :=
  !(subCarry false (b :: r) (padTo (b :: r) m)).2

/-- Return the little-endian quotient and padded remainder, in that order. -/
def divide (m : List Bool) : List Bool → List Bool × List Bool
  | [] => ([], padTo m [])
  | b :: bs =>
      let qr := divide m bs
      (quotientBit m qr.2 b :: qr.1, shiftReduce m qr.2 b)

@[simp] theorem divide_nil (m : List Bool) : divide m [] = ([], padTo m []) := rfl

@[simp] theorem divide_cons (m : List Bool) (b : Bool) (bs : List Bool) :
    divide m (b :: bs) =
      (quotientBit m (divide m bs).2 b :: (divide m bs).1,
        shiftReduce m (divide m bs).2 b) := rfl

@[simp] theorem divide_remainder (m xs : List Bool) :
    (divide m xs).2 = reduce m xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [reduce, ih]

@[simp] theorem divide_quotient_length (m xs : List Bool) :
    (divide m xs).1.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [ih]

@[simp] theorem divide_remainder_length (m xs : List Bool) :
    (divide m xs).2.length = m.length + xs.length := by
  rw [divide_remainder, reduce_length]

end SubexponentialSAT.ModularQuotientArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularQuotientPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Binary quotient and remainder from a fixed finite Boolean-stack program. -/

namespace SubexponentialSAT.ModularQuotientPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms SubexponentialSAT.ModularDivisionPrograms
open SubexponentialSAT.ModularQuotientArithmetic

theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

theorem quotientPorts_injective : Function.Injective quotientPorts := by decide

def divideFrom (m q r : List Bool) : List Bool → List Bool × List Bool
  | [] => (q, r)
  | b :: bs => divideFrom m (quotientBit m r b :: q) (shiftReduce m r b) bs

theorem divideFrom_append (m q r xs ys : List Bool) :
    divideFrom m q r (xs ++ ys) =
      let out := divideFrom m q r xs
      divideFrom m out.1 out.2 ys := by
  induction xs generalizing q r with
  | nil => rfl
  | cons b bs ih => exact ih (quotientBit m r b :: q) (shiftReduce m r b)

end SubexponentialSAT.ModularQuotientPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLogic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured verification rules for fixed bit programs

Every execution judgment below contains actual transitions of one fixed step
function. Loop iterations may be controlled by unbounded data; neither the
transition function nor its finite control changes with the iteration count.
No judgment assigns a cost to an unimplemented mathematical function.
-/

namespace SubexponentialSAT.ProgramLogic

open SubexponentialSAT.Computation
open scoped BigOperators

section BitPrograms

open SubexponentialSAT.BitProgram

variable {r s l : ℕ}

/-- Registers possibly modified by this concrete instruction. -/
def registerWrites : Instr r s l → Finset (Fin r)
  | .set dst _ _ => {dst}
  | .copy dst _ _ => {dst}
  | .bnot dst _ _ => {dst}
  | .band dst _ _ _ => {dst}
  | .bor dst _ _ _ => {dst}
  | .bxor dst _ _ _ => {dst}
  | .peek _ value present _ => {value, present}
  | .pop _ value present _ => {value, present}
  | _ => ∅

/-- Stacks possibly modified by this concrete instruction. Peeking is read-only. -/
def stackWrites : Instr r s l → Finset (Fin s)
  | .push stack _ _ => {stack}
  | .pop stack _ _ _ => {stack}
  | _ => ∅

end BitPrograms

end SubexponentialSAT.ProgramLogic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularQuotientLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Binary quotient and remainder on caller-selected stack ports

The fixed quotient program is relocated to eight distinct caller ports.  Its
existing instruction-trace bound is retained exactly.  Endpoints are explicit
updates of the caller's own stack store, so every unassigned stack is framed.
-/

namespace SubexponentialSAT.ModularQuotientLift

open BitProgram StackRoutines StructuredCalls
open ModularQuotientPrograms ModularQuotientArithmetic

/-- Only the remainder, consumed input, and quotient ports change. -/
def quotientStacksAt {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update (Function.update stk (ports 0) remainder)
    (ports 6) []) (ports 7) quotient

end SubexponentialSAT.ModularQuotientLift

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SlotAssignment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Incidence slots and globally consistent factor words

Section 5.4 assigns each coordinate's incident factors to different slots.
The same factor word is then used at every incidence of that factor.  The
slot numbers themselves need not agree at different coordinates.

The ordered constructor and the slot-filling operations are computable.  An
additional constructor for arbitrary finite factor types chooses an enumeration.
No running-time bound or probabilistic independence assertion is hidden here.
-/

namespace SubexponentialSAT.SlotAssignment

open SubexponentialSAT.Factor

variable {V E : Type*} [DecidableEq V]

/-- The actual factors incident to one coordinate. -/
abbrev Incident (P : Pattern V E) (v : V) := {e : E // v ∈ P.scope e}

@[simp] theorem card_incident [Fintype E] (P : Pattern V E) (v : V) :
    Fintype.card (Incident P v) =
      (Finset.univ.filter fun e => v ∈ P.scope e).card := by
  exact Fintype.card_subtype _

end SubexponentialSAT.SlotAssignment

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_MulticolorTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multicolor universal types and consistent incidence slots

The number `r` of colors is an explicit natural parameter throughout. No
finiteness instance or cardinality identity treats it as a fixed constant.
The joint fiber uses a head color different from the selected slot color,
as required by Sections 3.1 and 3.4 of the subexponential construction.
-/

namespace SubexponentialSAT.MulticolorTypes

structure UniversalType (r Q Δ : ℕ) where
  head : Word r Q
  slot : Fin Δ → Word r Q
  deriving DecidableEq

variable {r Q Δ : ℕ}

@[ext] theorem UniversalType.ext {u v : UniversalType r Q Δ}
    (hhead : u.head = v.head) (hslot : u.slot = v.slot) : u = v := by
  cases u
  cases v
  cases hhead
  cases hslot
  rfl

def equivProd (r Q Δ : ℕ) :
    UniversalType r Q Δ ≃ Word r Q × (Fin Δ → Word r Q) where
  toFun u := (u.head, u.slot)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeUniversalType : Fintype (UniversalType r Q Δ) :=
  Fintype.ofEquiv (Word r Q × (Fin Δ → Word r Q)) (equivProd r Q Δ).symm

@[simp] theorem card_word (r Q : ℕ) : Fintype.card (Word r Q) = r ^ Q := by
  simp [Word ]

@[simp] theorem card_universalType (r Q Δ : ℕ) :
    Fintype.card (UniversalType r Q Δ) = r ^ (Q * (Δ + 1)) := by
  rw [Fintype.card_congr (equivProd r Q Δ)]
  simp [Fintype.card_prod, ← pow_mul, Nat.mul_add,
    pow_add, Nat.mul_comm]

/-- The cardinality form independent of the chosen `Fintype` instance. -/
@[simp] theorem natCard_universalType (r Q Δ : ℕ) :
    Nat.card (UniversalType r Q Δ) = r ^ (Q * (Δ + 1)) := by
  rw [Nat.card_eq_fintype_card, card_universalType]

/-- Cast form used by the rational deviation and block-threshold inequalities. -/
@[simp] theorem card_universalType_rat (r Q Δ : ℕ) :
    (Fintype.card (UniversalType r Q Δ) : ℚ) = (r : ℚ) ^ (Q * (Δ + 1)) := by
  rw [card_universalType, Nat.cast_pow]

@[simp] theorem natCard_universalType_rat (r Q Δ : ℕ) :
    (Nat.card (UniversalType r Q Δ) : ℚ) = (r : ℚ) ^ (Q * (Δ + 1)) := by
  rw [natCard_universalType, Nat.cast_pow]

def side (t : Fin Q) (g : Fin r) : Set (UniversalType r Q Δ) :=
  {u | u.head t = g}

def joint (t : Fin Q) (g : Fin r) (i : Fin Δ) : Set (UniversalType r Q Δ) :=
  {u | u.head t = g ∧ u.slot i t ≠ g}

abbrev Side (t : Fin Q) (g : Fin r) :=
  {u : UniversalType r Q Δ // u ∈ side t g}
abbrev Joint (t : Fin Q) (g : Fin r) (i : Fin Δ) :=
  {u : UniversalType r Q Δ // u ∈ joint t g i}

instance instDecidablePredUniversalTypeSide (t : Fin Q) (g : Fin r) : DecidablePred (side (Δ := Δ) t g) :=
  fun _ => inferInstanceAs (Decidable (_ = _))
instance instDecidablePredUniversalTypeJoint (t : Fin Q) (g : Fin r) (i : Fin Δ) : DecidablePred (joint t g i) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

instance decidableMemSide (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) :
    Decidable (u ∈ side t g) :=
  inferInstanceAs (Decidable (u.head t = g))
instance decidableMemJoint (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r)
    (i : Fin Δ) : Decidable (u ∈ joint t g i) :=
  inferInstanceAs (Decidable (u.head t = g ∧ u.slot i t ≠ g))

instance instFintypeSide (t : Fin Q) (g : Fin r) : Fintype (Side (Δ := Δ) t g) :=
  inferInstanceAs (Fintype {u : UniversalType r Q Δ // u.head t = g})
instance instFintypeJoint (t : Fin Q) (g : Fin r) (i : Fin Δ) : Fintype (Joint t g i) :=
  inferInstanceAs (Fintype {u : UniversalType r Q Δ // u.head t = g ∧ u.slot i t ≠ g})

@[simp] theorem mem_side (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) :
    u ∈ side t g ↔ u.head t = g := Iff.rfl
@[simp] theorem mem_joint (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r)
    (i : Fin Δ) : u ∈ joint t g i ↔ u.head t = g ∧ u.slot i t ≠ g := Iff.rfl

def pinHead (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) : UniversalType r Q Δ :=
  {u with head := Function.update u.head t g}

def pinSlot (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q) (g : Fin r) :
    UniversalType r Q Δ :=
  {u with slot := Function.update u.slot i (Function.update (u.slot i) t g)}

@[simp] theorem pinHead_head (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) :
    (pinHead u t g).head = Function.update u.head t g := rfl
@[simp] theorem pinHead_slot (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) :
    (pinHead u t g).slot = u.slot := rfl
@[simp] theorem pinSlot_head (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q)
    (g : Fin r) : (pinSlot u i t g).head = u.head := rfl
@[simp] theorem pinSlot_slot (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q)
    (g : Fin r) : (pinSlot u i t g).slot =
      Function.update u.slot i (Function.update (u.slot i) t g) := rfl

@[simp] theorem pinHead_pinHead (u : UniversalType r Q Δ) (t : Fin Q) (g h : Fin r) :
    pinHead (pinHead u t g) t h = pinHead u t h := by
  cases u
  simp [pinHead]
@[simp] theorem pinHead_self (u : UniversalType r Q Δ) (t : Fin Q) :
    pinHead u t (u.head t) = u := by
  cases u
  simp [pinHead, Function.update_eq_self]
@[simp] theorem pinSlot_pinSlot (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q)
    (g h : Fin r) : pinSlot (pinSlot u i t g) i t h = pinSlot u i t h := by
  cases u
  simp [pinSlot]
@[simp] theorem pinSlot_self (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q) :
    pinSlot u i t (u.slot i t) = u := by
  cases u
  simp [pinSlot, Function.update_eq_self]

@[simp] theorem card_otherPosition (t : Fin Q) :
    Fintype.card (OtherPosition t) = Q - 1 := by
  change Fintype.card {l : Fin Q // ¬l = t} = Q - 1
  rw [Fintype.card_subtype_compl]
  simp
@[simp] theorem card_otherSlot (i : Fin Δ) :
    Fintype.card (OtherSlot i) = Δ - 1 := by
  change Fintype.card {j : Fin Δ // ¬j = i} = Δ - 1
  rw [Fintype.card_subtype_compl]
  simp
@[simp] theorem card_otherColor (g : Fin r) :
    Fintype.card (OtherColor g) = r - 1 := by
  change Fintype.card {c : Fin r // ¬c = g} = r - 1
  rw [Fintype.card_subtype_compl]
  simp
@[simp] theorem card_otherSlotWords (i : Fin Δ) :
    Fintype.card (OtherSlot i → Word r Q) = r ^ (Q * (Δ - 1)) := by
  simp [ ← pow_mul]

/-- Coordinates not changed by the swaps at positions other than `t`. -/
abbrev Spectator (g : Fin r) (i : Fin Δ) :=
  OtherColor g × (OtherSlot i → Word r Q)

/-- A joint fiber is the product of free head--slot pairs at all other
positions and the untouched slot color at `t` and all other slot words. -/
def jointEquivPairs (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Joint t g i ≃ (OtherPosition t → Fin r × Fin r) × Spectator (Q := Q) g i where
  toFun u := ((fun l => (u.val.head l.val, u.val.slot i l.val)),
    (⟨u.val.slot i t, u.property.2⟩, fun j => u.val.slot j.val))
  invFun z := ⟨{
    head := fun l => if h : l = t then g else (z.1 ⟨l, h⟩).1
    slot := fun j => if hj : j = i then
      fun l => if h : l = t then z.2.1.val else (z.1 ⟨l, h⟩).2
      else z.2.2 ⟨j, hj⟩
    }, by simpa [joint] using z.2.1.property⟩
  left_inv u := by
    apply Subtype.ext
    apply UniversalType.ext
    · funext l
      by_cases hl : l = t
      · subst l
        simpa using u.property.1.symm
      · simp [hl]
    · funext j l
      by_cases hj : j = i
      · subst j
        by_cases hl : l = t
        · subst l
          simp
        · simp [hl]
      · simp [hj]
  right_inv z := by
    apply Prod.ext
    · funext l
      apply Prod.ext <;> simp [l.property]
    · apply Prod.ext
      · apply Subtype.ext
        simp
      · funext j l
        simp [j.property]

@[simp] theorem jointEquivPairs_head (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (u : Joint t g i) (l : OtherPosition t) :
    ((jointEquivPairs t g i u).1 l).1 = u.val.head l.val := rfl
@[simp] theorem jointEquivPairs_slot (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (u : Joint t g i) (l : OtherPosition t) :
    ((jointEquivPairs t g i u).1 l).2 = u.val.slot i l.val := rfl
@[simp] theorem jointEquivPairs_color (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (u : Joint t g i) : (jointEquivPairs t g i u).2.1.val = u.val.slot i t := rfl
@[simp] theorem jointEquivPairs_otherSlot (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (u : Joint t g i) (j : OtherSlot i) :
    (jointEquivPairs t g i u).2.2 j = u.val.slot j.val := rfl

@[simp] theorem jointEquivPairs_symm_head (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (z : (OtherPosition t → Fin r × Fin r) × Spectator (Q := Q) g i)
    (l : OtherPosition t) :
    ((jointEquivPairs t g i).symm z).val.head l.val = (z.1 l).1 := by
  simp [jointEquivPairs, l.property]
@[simp] theorem jointEquivPairs_symm_slot (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (z : (OtherPosition t → Fin r × Fin r) × Spectator (Q := Q) g i)
    (l : OtherPosition t) :
    ((jointEquivPairs t g i).symm z).val.slot i l.val = (z.1 l).2 := by
  simp [jointEquivPairs, l.property]
@[simp] theorem jointEquivPairs_symm_otherSlot (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (z : (OtherPosition t → Fin r × Fin r) × Spectator (Q := Q) g i)
    (j : OtherSlot i) :
    ((jointEquivPairs t g i).symm z).val.slot j.val = z.2.2 j := by
  simp [jointEquivPairs, j.property]

end SubexponentialSAT.MulticolorTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

open SubexponentialSAT.BitProgram

/-! ## In-place removal of one escape frame -/

/-- Move the reversed payload back onto the input stack. -/
abbrev restoreProgram : Program 2 2 4 :=
  StackRoutines.transferProgram 1 0 0 1

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_PowerPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Variable exponentiation with finite Boolean control

The exponent is a binary stack word.  The multiplication callback below uses
only fixed finite programs and leaves the countdown ports untouched.
-/

namespace SubexponentialSAT.PowerPrograms

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredProgram
open SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

theorem extend_mulPorts (base exponent x y acc cp tmp rev : List Bool) :
    Function.extend mulPorts (SubexponentialSAT.BinaryPrograms.Mul.stackState x y acc cp tmp rev)
      (stackState base exponent [] [] [] [] [] [] []) =
      stackState base exponent y x acc cp tmp rev [] := by
  funext i
  fin_cases i
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨j, hj⟩; fin_cases j <;> simp [mulPorts] at hj
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨j, hj⟩; fin_cases j <;> simp [mulPorts] at hj
  · exact mulPorts_injective.extend_apply _ _ (1 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (0 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (2 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (3 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (4 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (5 : Fin 6)
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨j, hj⟩; fin_cases j <;> simp [mulPorts] at hj

/-- The left operand is always a copy of the fixed base. -/
def nextAccumulator (base acc : List Bool) : List Bool :=
  SubexponentialSAT.BinaryPrograms.Mul.accumulate base acc []

@[simp] theorem nextAccumulator_value (base acc : List Bool) :
    BinaryArithmetic.toNat (nextAccumulator base acc) = BinaryArithmetic.toNat base * BinaryArithmetic.toNat acc := by
  simpa [nextAccumulator] using SubexponentialSAT.BinaryPrograms.Mul.accumulate_value base acc []

theorem nextAccumulator_length (base acc : List Bool) :
    (nextAccumulator base acc).length ≤ acc.length + base.length := by
  simpa [nextAccumulator] using SubexponentialSAT.BinaryPrograms.Mul.accumulate_length base acc []

/-- A polynomial in numerical exponent and the actual input word lengths. -/
def workBound (base exponent : List Bool) : ℕ :=
  BinaryArithmetic.toNat exponent * callbackBound base (BinaryArithmetic.toNat exponent) +
    (BinaryArithmetic.toNat exponent + 1) * (16 * exponent.length + 16)

def runtimeBound (base exponent : List Bool) : ℕ := workBound base exponent + 3

end SubexponentialSAT.PowerPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RecordPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A reusable actual iterator over the project's framed-record representation.
The callback is a fixed structured program, whose executions are measured in the
same semantics as the parser and iterator. It is never an atomic semantic oracle.
-/

namespace SubexponentialSAT.RecordPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem budget_eq (cost : List Bool → ℕ) (records : List (List Bool)) :
    budget cost records = 6 * (records.map List.length).sum +
      (records.map cost).sum + 7 * records.length := by
  induction records with
  | nil => simp [budget]
  | cons bits rest ih => simp [budget, ih]; omega

theorem budget_le_linear (cost : List Bool → ℕ) (records : List (List Bool))
    (a b : ℕ) (h : ∀ bits ∈ records, cost bits ≤ a * bits.length + b) :
    budget cost records ≤ (a + 6) * (records.map List.length).sum + (b + 7) * records.length := by
  induction records with
  | nil => simp [budget]
  | cons bits rest ih =>
      have hh := h bits (by simp)
      have ht := ih (fun item hi => h item (by simp [hi]))
      simp only [budget, List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

end SubexponentialSAT.RecordPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RecordMappedPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual record iteration over encoded logical values

The instruction sequence is `RecordPrograms.iterate`. The contract below is
required only for payloads emitted by the supplied encoder. It does not ask a
callback for correct behavior on malformed encodings, and it does not install
the encoder, test, or cost function as a machine instruction.
-/

namespace SubexponentialSAT.RecordMappedPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {α : Type*} {r s : ℕ}

def unread (enc : α → List Bool) (test : α → Bool) : List α → List Bool → List Bool
  | [], suffix => suffix
  | a :: rest, suffix =>
      if test a then Encoding.encodeList enc rest ++ suffix else unread enc test rest suffix

end SubexponentialSAT.RecordMappedPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RegisterResetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed finite register initialization. The list of ports is part of the
program, not input data; every reset is one actual Boolean-register instruction. -/

namespace SubexponentialSAT.RegisterResetProgram

open BitProgram StructuredCalls

def clear {r s : ℕ} : List (Fin r) → Cmd r s
  | [] => .base .skip
  | i :: rest => .seq (.base (.atom (.set i false))) (clear rest)

def cleared {r s : ℕ} (ports : List (Fin r)) (a : State r s) : State r s :=
  ⟨fun i => if i ∈ ports then false else a.regs i, a.stacks⟩

abbrev all {r s : ℕ} : Cmd r s := clear (List.finRange r)

abbrev zeroed {r s : ℕ} (a : State r s) : State r s := ⟨fun _ => false, a.stacks⟩

end SubexponentialSAT.RegisterResetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RemovalCharging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Appendix A.2: charging removals to smaller insertions

The trace below records finite clause families before and after each replacement.
The cumulative insertion counter counts events, not distinct clauses.  Its
accounting identity therefore does not assume that reinsertion is impossible.
-/

namespace SubexponentialSAT.RemovalCharging

open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

section SATLiteralUniverse

variable {V : Type*} [DecidableEq V] [Fintype V] {T : ℕ}

/-- An explicit finite universe containing the two signs of every variable. -/
def literalUniverse : Finset (SAT.Literal V) :=
  Finset.univ.image fun p : V × Bool => ⟨p.1, p.2⟩

end SATLiteralUniverse

end SubexponentialSAT.RemovalCharging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SaturatingSubtractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving saturating binary subtraction

Eight Boolean registers and eight stacks suffice. The two operands remain
on stacks 0 and 1; stack 2 receives their natural-number difference and
stacks 3 through 7 return empty. Copied concatenations supply a common
padding shape without computing a numeric width. The final borrow bit
controls a real clear loop. Every copy, pad, subtraction, and clear is
charged in the linear instruction bound.
-/

namespace SubexponentialSAT.SaturatingSubtractionProgram

open BitProgram StructuredCalls BinaryArithmetic ModularArithmetic

def saturated (xs ys : List Bool) : List Bool :=
  if (subCarry false xs ys).2 then [] else (subCarry false xs ys).1

end SubexponentialSAT.SaturatingSubtractionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Filter

def clauseCode (C : Clause) : List Bool := Encoding.encodeList id C


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgmin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A binary-score minimum update implemented by finite bit programs

The score is a little-endian bit word. Comparisons inspect its numeric value,
not its length. Candidate payloads may themselves be binary indices or encoded
rows. Ports 0/1 hold the incoming payload/score, 2/3 the incumbent, 4--7 are
scratch, and 8 is an untouched caller queue. Every copy and comparison below
has a measured trace of a fixed finite instruction table.
-/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def value (a : Entry) : ℕ := BinaryArithmetic.toNat a.score

def pick (best next : Entry) : Entry := if value next < value best then next else best

abbrev atom (a : StructuredProgram.Atom 8 9) : Cmd 8 9 := .base (.atom a)
abbrev copy (src dst : Fin 9) : Cmd 8 9 := .call (copyProgram src dst 7 1 2)

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary conditional-add kernel for exact offset signatures. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls
open scoped BigOperators

abbrev AddData := State 8 9

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_WorkspaceCleanupProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual fixed workspace cleanup

The selected ports are part of the finite program. Their initial contents
and lengths are arbitrary. Every clear is an existing measured instruction
loop, and all unselected stacks and non-scratch registers are preserved.
-/

namespace SubexponentialSAT.WorkspaceCleanupProgram

open BitProgram StackRoutines StructuredCalls

def finalRegs {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (regs : Fin r → Bool) : Fin r → Bool :=
  match ports with
  | [] => regs
  | _ :: _ => readRegs regs value present none

@[simp] theorem finalRegs_cons {r s : ℕ} (value present : Fin r)
    (port : Fin s) (rest : List (Fin s)) (regs : Fin r → Bool) :
    finalRegs value present (port :: rest) regs = readRegs regs value present none := rfl

end SubexponentialSAT.WorkspaceCleanupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramDot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual row-entry parsing, assignment-bit scanning, binary addition and
workspace recycling for one exact offset-signature row. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev DotCode := Cmd 8 12

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed EOF-controlled reversal of a raw list of framed words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev PreReverseCode := Cmd 8 4

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete decoding and shifting of one signed coefficient pair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev PreCode := Cmd 8 14

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete row-major signed matrix preprocessor. All input and output
frames are scanned by fixed instructions; the original bound word is retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev PreMatrixCode := Cmd 8 17

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit-program implementation of type collision

Each color is represented by an r-bit one-hot word.  All head and slot words
are serialized at a fixed width.  The existing fixed bitEqualityProgram
then compares two such encodings, including at the primitive-machine level.
The execution boundary has the two encoded types already on its two stacks;
seed lookup and the production of these encodings are separate operations.
-/

namespace SubexponentialSAT.Subexp.CollisionProgram

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BitProgram

variable {r Q Δ : ℕ}

/-- Register zero is the head, and register i+1 is slot i. -/
def registerWord (u : UniversalType r Q Δ) (a : Fin (Δ + 1)) : Word r Q :=
  Fin.cases u.head u.slot a

@[simp] theorem registerWord_zero (u : UniversalType r Q Δ) :
    registerWord u 0 = u.head := rfl

@[simp] theorem registerWord_succ (u : UniversalType r Q Δ) (i : Fin Δ) :
    registerWord u i.succ = u.slot i := by
  simp [registerWord]

/-- One bit of the one-hot representation. -/
def codeBit (u : UniversalType r Q Δ) (j : Fin (typeWidth r Q Δ)) : Bool :=
  let outer : Fin ((Δ + 1) * Q) × Fin r := finProdFinEquiv.symm j
  let inner : Fin (Δ + 1) × Fin Q := finProdFinEquiv.symm outer.1
  decide (registerWord u inner.1 inner.2 = outer.2)

@[simp] theorem codeBit_codeIndex (u : UniversalType r Q Δ)
    (a : Fin (Δ + 1)) (q : Fin Q) (c : Fin r) :
    codeBit u (codeIndex a q c) = decide (registerWord u a q = c) := by
  simp [codeBit, codeIndex]

/-- Uniform, fixed-width serialization of all type registers. -/
def encodeType (u : UniversalType r Q Δ) : List Bool := List.ofFn (codeBit u)

@[simp] theorem encodeType_length (u : UniversalType r Q Δ) :
    (encodeType u).length = typeWidth r Q Δ := by
  simp [encodeType]

theorem encodeType_injective :
    Function.Injective (encodeType : UniversalType r Q Δ → List Bool) := by
  intro u v h
  have hbits : codeBit u = codeBit v := List.ofFn_injective h
  have hreg : registerWord u = registerWord v := by
    funext a q
    have hb := congrFun hbits (codeIndex a q (registerWord u a q))
    simp only [codeBit_codeIndex, decide_true] at hb
    exact (of_decide_eq_true hb.symm).symm
  apply UniversalType.ext
  · exact congrFun hreg 0
  · funext i
    exact congrFun hreg i.succ

@[simp] theorem encodeType_eq_iff (u v : UniversalType r Q Δ) :
    encodeType u = encodeType v ↔ u = v :=
  encodeType_injective.eq_iff

end SubexponentialSAT.Subexp.CollisionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ReadPlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit local read plans

Read plans are lists of numeric positions in the explicit seed array. The
machine-facing data are fixed-width one-hot word records and unary indices.
Gathering them in head/slot order reproduces the actual type encoding.
-/

namespace SubexponentialSAT.Subexp.ReadPlan

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

section Encoding

variable {r Q Δ : ℕ}

/-- Position first, then color: each letter is a one-hot r-bit record. -/
def encodeWord (w : Word r Q) : List Bool :=
  (List.ofFn fun q : Fin Q => List.ofFn fun c : Fin r => decide (w q = c)).flatten

@[simp] theorem encodeWord_length (w : Word r Q) :
    (encodeWord w).length = wordWidth r Q := by
  simp [encodeWord, wordWidth, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.ofFn_const]

end Encoding

section PartialVertexPlans

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E)
  {r Q Δ : ℕ}

/-- A finite, explicit current array from the search's reverse fixed list. -/
def currentArray (default : Word r Q) (seedCount : ℕ) (fixed : List (Word r Q)) :
    List (Word r Q) :=
  (List.range seedCount).map (SubexponentialSAT.LocalExpectation.decode default fixed)

@[simp] theorem currentArray_length (default : Word r Q) (seedCount : ℕ)
    (fixed : List (Word r Q)) : (currentArray default seedCount fixed).length = seedCount := by
  simp [currentArray]

end PartialVertexPlans

end SubexponentialSAT.Subexp.ReadPlan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstructivePacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable complete-block packing

All execution definitions use supplied finite lists, filtering, minimum scans,
indexed list access, and index lookup. No execution definition uses classical
choice or an abstract inverse. Mathematical cardinalities occur only in proofs.
-/

namespace SubexponentialSAT.Subexp.ConstructivePacking

open scoped BigOperators

namespace PackingData

variable {V U : Type*} [DecidableEq U]

variable [DecidableEq V]

/-- The old mathematical interface, now filled by the computed placement. -/
def completeBlocks (P : PackingData V U) : BlockPacking.CompleteBlocks P.label P.blockCount where
  embed := {
    toFun := fun z => P.vertexAt z.1 z.2
    inj' := by
      intro x y h
      have hi := congrArg P.lookup h
      simpa only [lookup_at, Option.some.injEq, Prod.eta] using hi }
  type_eq := P.label_at

@[simp] theorem completeBlocks_apply (P : PackingData V U) (z : Fin P.blockCount × U) :
    P.completeBlocks.embed z = P.vertexAt z.1 z.2 := rfl

/-- Exact correctness specification for the executable inverse lookup. -/
theorem lookup_some_iff (P : PackingData V U) (v : V) (z : Fin P.blockCount × U) :
    P.lookup v = some z ↔ P.completeBlocks.embed z = v := by
  constructor
  · exact P.lookup_sound v z
  · intro h
    rw [← h]
    exact P.lookup_at z.1 z.2

theorem lookup_none_iff (P : PackingData V U) (v : V) :
    P.lookup v = none ↔ v ∉ Set.range P.completeBlocks.embed := by
  constructor
  · intro hn ⟨z, hz⟩
    have hs := (P.lookup_some_iff v z).mpr hz
    rw [hn] at hs
    cases hs
  · intro hn
    cases hl : P.lookup v with
    | none => rfl
    | some z => exact False.elim (hn ⟨z, (P.lookup_some_iff v z).mp hl⟩)

/-- The original vertex order, filtered by executable lookup failure. -/
def leftovers (P : PackingData V U) : List V :=
  P.vertices.values.filter fun v => decide (P.lookup v = none)

@[simp] theorem mem_leftovers (P : PackingData V U) (v : V) :
    v ∈ P.leftovers ↔ v ∉ Set.range P.completeBlocks.embed := by
  simp only [leftovers, List.mem_filter, P.vertices.complete v, true_and, decide_eq_true_eq]
  exact P.lookup_none_iff v

end PackingData

end SubexponentialSAT.Subexp.ConstructivePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete measured coefficient scan for one integer signature row.
Runtime EOF controls the loop; no instruction count depends on row length. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def dotPeek : DotCode := .base (.atom (.peek 9 0 1))

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSignature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed nested row scanner.  The input matrix is a raw list of framed
rows, and each row is itself a raw list of framed coefficient words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev SignatureCode := Cmd 8 15

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact signed arithmetic for minor enumeration. Integers are represented as
pairs of natural binary words. No modular arithmetic, integer oracle, or
parameter-dependent instruction table is used. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

def signedValue (positive negative : List Bool) : ℤ :=
  (BinaryArithmetic.toNat positive : ℤ) - (BinaryArithmetic.toNat negative : ℤ)

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit framed input parsing for streams of signed binary word pairs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def pairValue (w : WordPair) : ℤ := signedValue w.1 w.2

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid traversal of the explicit original-column identifier records. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def pairWords : List Pair → List Bool
  | [] => []
  | p::ps => Encoding.frame p.1 ++ Encoding.frame p.2 ++ pairWords ps

@[simp] theorem pairWords_append (ps qs : List Pair) :
    pairWords (ps++qs)=pairWords ps++pairWords qs := by
  induction ps with
  | nil => simp [pairWords]
  | cons p ps ih => simp [pairWords,ih,List.append_assoc]

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact nonnegative component-mass contracts for the actual signed arithmetic
programs. These bounds control both components even when cancellation occurs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ArithmeticCalls

def pairTotal (positive negative : List Bool) : ℕ := BinaryArithmetic.toNat positive+BinaryArithmetic.toNat negative


end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual universal-type enumeration

The byte list is the output of the fixed Cartesian-power program.  The
semantic list and its finite equivalences only name that same physical
order; they are not executable inputs to any program.
-/

namespace SubexponentialSAT.Subexp.TypeEnumeration

open MulticolorTypes
open CollisionProgram (encodeType registerWord)

def ofWords {r Q Δ : ℕ} (v : Fin (Δ + 1) → Word r Q) : UniversalType r Q Δ :=
  ⟨v 0, fun i => v i.succ⟩

@[simp] theorem registerWord_ofWords {r Q Δ : ℕ} (v : Fin (Δ + 1) → Word r Q) :
    registerWord (ofWords v) = v := by
  funext a
  exact Fin.cases rfl (fun _ => rfl) a

@[simp] theorem ofWords_registerWord {r Q Δ : ℕ} (u : UniversalType r Q Δ) :
    ofWords (registerWord u) = u := by
  apply UniversalType.ext
  · rfl
  · funext i
    rfl

end SubexponentialSAT.Subexp.TypeEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Restricted support of the multicolor interpolation matrices

The multicolor register permutations and the products of (1 - J_l) / 2 are constructed
explicitly.  The support conclusion is derived from their sublist expansion.
-/

namespace SubexponentialSAT.Subexp.MatrixSupport

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

/-- Mismatches compare the column head against the row's selected slot. -/
def mismatches (i : Fin Δ) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  Finset.univ.filter (fun l => y.head l ≠ u.slot i l)

@[simp] theorem mem_mismatches (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    l ∈ mismatches i u y ↔ y.head l ≠ u.slot i l := by
  simp [mismatches]

/-- Swap the head and selected slot register at each selected position. -/
def swapPositions (i : Fin Δ) (s : Finset (Fin Q)) (u : UniversalType r Q Δ) :
    UniversalType r Q Δ where
  head l := if l ∈ s then u.slot i l else u.head l
  slot j l := if j = i then
    if l ∈ s then u.head l else u.slot j l
    else u.slot j l

@[simp] theorem swapPositions_head (i : Fin Δ) (s : Finset (Fin Q))
    (u : UniversalType r Q Δ) (l : Fin Q) :
    (swapPositions i s u).head l = if l ∈ s then u.slot i l else u.head l := rfl

@[simp] theorem swapPositions_slot_same (i : Fin Δ) (s : Finset (Fin Q))
    (u : UniversalType r Q Δ) (l : Fin Q) :
    (swapPositions i s u).slot i l =
      if l ∈ s then u.head l else u.slot i l := by
  simp [swapPositions]

@[simp] theorem swapPositions_slot_other (i j : Fin Δ) (h : j ≠ i)
    (s : Finset (Fin Q)) (u : UniversalType r Q Δ) (l : Fin Q) :
    (swapPositions i s u).slot j l = u.slot j l := by
  simp [swapPositions, h]

@[simp] theorem swapPositions_empty (i : Fin Δ) (u : UniversalType r Q Δ) :
    swapPositions i ∅ u = u := by
  apply UniversalType.ext
  · funext l
    simp
  · funext j l
    simp [swapPositions]

section Operators

variable {K : Type*} [Field K]

/-- The actual ordered product of Id - J_l, acting by pullback. -/
def differenceProduct (i : Fin Δ) :
    List (Fin Q) → (UniversalType r Q Δ → K) → UniversalType r Q Δ → K
  | [], f, u => f u
  | a :: as, f, u =>
      differenceProduct i as f u -
      differenceProduct i as f (swapPositions i {a} u)

/-- The product of the normalized projectors (Id - J_l) / 2. -/
def projectorProduct (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) : K :=
  (2 : K)⁻¹ ^ as.length * differenceProduct i as f u

/-- A column basis vector, in function coordinates. -/
def delta (y : UniversalType r Q Δ) (x : UniversalType r Q Δ) : K :=
  if x = y then 1 else 0

/-- Elementary symmetric sum of degree j in the actual normalized projectors. -/
noncomputable def elementaryProjector (i : Fin Δ) (t : Fin Q) (j : ℕ)
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) : K :=
  ∑ A ∈ (activePositions t).powersetCard j,
    projectorProduct i A.toList f u

/-- The permutation operator associated with any set of positions. -/
def permutationLinear (i : Fin Δ) (s : Finset (Fin Q)) :
    Module.End K (UniversalType r Q Δ → K) where
  toFun f u := f (swapPositions i s u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem permutationLinear_apply (i : Fin Δ) (s : Finset (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    permutationLinear i s f u = f (swapPositions i s u) := rfl

/-- Linear-map presentation of the ordered product of Id - J. -/
def differenceLinear (i : Fin Δ) :
    List (Fin Q) → Module.End K (UniversalType r Q Δ → K)
  | [] => 1
  | a :: as => (1 - permutationLinear i {a}) * differenceLinear i as

@[simp] theorem differenceLinear_apply (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    differenceLinear i as f u = differenceProduct i as f u := by
  induction as generalizing u with
  | nil => rfl
  | cons a as ih =>
    change differenceLinear i as f u -
      differenceLinear i as f (swapPositions i {a} u) = _
    rw [ih, ih]
    rfl

/-- A linear map for a product of normalized projectors. -/
def projectorLinear (i : Fin Δ) (as : List (Fin Q)) :
    Module.End K (UniversalType r Q Δ → K) :=
  (2 : K)⁻¹ ^ as.length • differenceLinear i as

@[simp] theorem projectorLinear_apply (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    projectorLinear i as f u = projectorProduct i as f u := by
  simp [projectorLinear, projectorProduct]

/-- The endomorphism in (3.5), before restriction to the joint fiber. -/
noncomputable def matrixLinear (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K) :
    Module.End K (UniversalType r Q Δ → K) :=
  permutationLinear i (activePositions t) *
    ∑ j ∈ Finset.range R,
      c j • ∑ A ∈ (activePositions t).powersetCard j, projectorLinear i A.toList

@[simp] theorem matrixLinear_apply (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    matrixLinear i t R c f u =
      ∑ j ∈ Finset.range R,
        c j * elementaryProjector i t j f (swapPositions i (activePositions t) u) := by
  simp [matrixLinear, elementaryProjector, Module.End.mul_apply]

/-- Extend a vector on the joint fiber by zero, using its coordinate basis. -/
noncomputable def extendJoint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (f : Joint t g i → K) : UniversalType r Q Δ → K :=
  ∑ y : Joint t g i, f y • delta y.val

@[simp] theorem extendJoint_on_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (f : Joint t g i → K) (u : Joint t g i) :
    extendJoint i t g f u.val = f u := by
  classical
  simp [extendJoint, delta, Subtype.val_inj]

theorem swapPositions_mem_joint_iff (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (s : Finset (Fin Q)) (ht : t ∉ s) (u : UniversalType r Q Δ) :
    swapPositions i s u ∈ joint t g i ↔ u ∈ joint t g i := by
  simp [ht]

/-- The actual position involution restricted to the joint fiber. -/
def jointSwap (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (l : OtherPosition t) (u : Joint t g i) : Joint t g i :=
  ⟨swapPositions i {l.val} u.val,
    (swapPositions_mem_joint_iff i t g {l.val}
      (by simpa using Ne.symm l.property) u.val).mpr u.property⟩

@[simp] theorem jointSwap_val (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (l : OtherPosition t) (u : Joint t g i) :
    (jointSwap i t g l u).val = swapPositions i {l.val} u.val := rfl

end Operators

end SubexponentialSAT.Subexp.MatrixSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBlocks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assemble complete copies of an actual universal block, with singleton
constraints on uncovered incidences. The scalar ring is arbitrary. -/
namespace SubexponentialSAT.SqrtLog.LayoutBlocks

open scoped BigOperators
open LayoutPullback

variable {U I F G O : Type*}
variable [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
variable [Fintype G] [DecidableEq G] [CommRing O]
variable {Q R b : ℕ} {label : I → U}

noncomputable def assembledRow (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (rows : U → U → Polynomial O) : I → I → Polynomial O :=
  Function.extend P.embed
    (fun z => row (P.blockEmbedding z.1) (rows z.2))
    (fun i v => Polynomial.C (if v = i then 1 else 0))

omit [DecidableEq U] [Fintype I] in
@[simp] theorem assembledRow_apply (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (rows : U → U → Polynomial O) (j : Fin b) (u : U) :
    assembledRow P rows (P.embed (j,u)) = row (P.blockEmbedding j) (rows u) :=
  P.embed.injective.extend_apply _ _ (j,u)

end SubexponentialSAT.SqrtLog.LayoutBlocks

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryKernel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Scalar kernels of the actual multicolor matrix

The tensor coordinates below describe entries of the existing swap/projector
operator. They do not introduce a new matrix chosen only for its rank or support.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

def pair (i : Fin Δ) (u : UniversalType r Q Δ) (l : Fin Q) : Fin r × Fin r :=
  (u.head l, u.slot i l)

def SpectatorsAgree (i : Fin Δ) (u y : UniversalType r Q Δ) : Prop :=
  ∀ j, j ≠ i → ∀ l, u.slot j l = y.slot j l

instance spectatorsAgreeDecidable (i : Fin Δ) (u y : UniversalType r Q Δ) :
    Decidable (SpectatorsAgree i u y) := by
  unfold SpectatorsAgree
  infer_instance

section Field

variable {K : Type*} [Field K]

noncomputable def background (i : Fin Δ) (u y : UniversalType r Q Δ) : K :=
  if SpectatorsAgree i u y then 1 else 0

def plain (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) : K :=
  if pair i u l = pair i y l then 1 else 0

def flipped (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) : K :=
  if (u.slot i l, u.head l) = pair i y l then 1 else 0

@[simp] theorem background_swap (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) :
    background (K := K) i (MatrixSupport.swapPositions i s u) y = background i u y := by
  classical
  have h : SpectatorsAgree i (MatrixSupport.swapPositions i s u) y ↔
      SpectatorsAgree i u y := by
    constructor
    · intro hs j hj l
      simpa only [MatrixSupport.swapPositions_slot_other i j hj] using hs j hj l
    · intro hs j hj l
      simpa only [MatrixSupport.swapPositions_slot_other i j hj] using hs j hj l
  simp only [background, h]

@[simp] theorem plain_swap (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) (l : Fin Q) :
    plain (K := K) i (MatrixSupport.swapPositions i s u) y l =
      if l ∈ s then flipped i u y l else plain i u y l := by
  by_cases h : l ∈ s <;> simp [plain, flipped, pair, h]

@[simp] theorem flipped_swap (i : Fin Δ) (s : Finset (Fin Q))
    (u y : UniversalType r Q Δ) (l : Fin Q) :
    flipped (K := K) i (MatrixSupport.swapPositions i s u) y l =
      if l ∈ s then plain i u y l else flipped i u y l := by
  by_cases h : l ∈ s <;> simp [plain, flipped, pair, h]

end Field

end SubexponentialSAT.Subexp.MatrixEntryKernel

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A scalar generating polynomial for the actual matrix entries

The coefficient of degree j equals 2^j times the j-th elementary projector
kernel. Consequently normalized coefficients need only scalar polynomial
arithmetic, with no enumeration of subsets in the eventual implementation.
-/

/-! The scalar kernel has only three nonzero local factors: 1, -X, and 1+X. -/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes Polynomial
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

def Compatible (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) : Prop :=
  SpectatorsAgree i u y ∧ pair i u t = pair i y t ∧
    ∀ l, l ≠ t → pair i u l = pair i y l ∨ (u.slot i l, u.head l) = pair i y l

instance compatibleDecidable (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    Decidable (Compatible i t u y) := by
  unfold Compatible SpectatorsAgree
  infer_instance

def unchanged (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  (MatrixSupport.activePositions t).filter fun l =>
    u.head l ≠ u.slot i l ∧ pair i u l = pair i y l

def transposed (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  (MatrixSupport.activePositions t).filter fun l =>
    u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = pair i y l

end SubexponentialSAT.Subexp.MatrixEntryKernel

/-!
# Exact binomial formula for the implemented multicolor matrix

This connects scalar additions and sign changes to the very same matrix
used in the support and rank proofs. The only normalization hypothesis is
that the field has characteristic different from two.
-/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithmEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable scalar formulas for the exact cleared integer matrix entries. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

def scalarEntry (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) : ℤ :=
  if Compatible i t u y then
    scalarSum A R (unchanged i t u y).card (transposed i t u y).card
  else 0

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntrySemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact joint-membership meaning of the three selected-color comparisons. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open MulticolorTypes

variable {r Q Δ : ℕ}

def anchorValid (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) : Prop :=
  u.head t = y.head t ∧ u.slot i t ≠ y.head t ∧ y.slot i t ≠ y.head t

instance instDecidableAnchorValid (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    Decidable (anchorValid i t u y) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical entry dispatch does not need a head-color oracle. The actual
head-ID scan supplies the column-head invariant; the joint guard compares the
two decoded type words at the requested node. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

variable {r Q : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

def localEntry (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (v w : I) : ℤ :=
  match P.lookup v with
  | none => if w = v then 1 else 0
  | some (j,u) => match P.lookup w with
    | none => 0
    | some (k,y) =>
      if j = k ∧ anchorValid (0 : Fin 1) t u y then
        (if u = y then (2 : ℤ)^(R-1) else 0) -
          LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y
      else 0

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual integer entry program is a literal owner-fiber sum. Restricting
its columns to the emitted head IDs has exactly the canonical pulled row span,
up to harmless column omission/repetition. All incidence rows are retained. -/
namespace SubexponentialSAT.SqrtLog.LayoutProducedMatrix
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutPullback LayoutProgram

variable {r Q : ℕ} {I V O : Type*}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [CommRing O]
variable {node : Fin Q → O}

def literalMatrix (P : PackingData I (UniversalType r Q 1)) (owner : I → V)
    (A R : ℕ) (t : Fin Q) : I → V → ℤ :=
  fun j => row owner (localEntry P A R t j)

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankLiteral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native fiber relation realizes the literal owner-sum matrix. Signed
component mass bounds imply both safe shifting and a signature-height bound. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q D n : ℕ}

def FiberRel (ps : List (ℕ × ℕ)) (value : ℕ → ℕ → ℤ) (H : ℕ)
    (j v : ℕ) (p : LayoutMatrixProgram.Pair) : Prop :=
  RowSelectionProgram.pairValue p=
    ((LayoutOwnerFiberProgram.fiberIndices v 0 ps).map (value j)).sum ∧
  RowSelectionProgram.pairTotal p.1 p.2 ≤ H

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual shared-head/shared-factor words on an arbitrary finite incidence set. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes

noncomputable section

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

abbrev WordAssignment (V E : Type*) (r Q : ℕ) := (V ⊕ E) → Word r Q

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete addition into one packed jet cell

The persistent jet, unary index, and cell width are on stacks 102, 103, and
104. The array subprogram uses 112--117, and order-preserving moves use 118.
All instruction tables are fixed independently of widths and indices. The
full service reads the old cell, invokes the actual flattened quartic adder,
and writes the sum back. Its endpoint changes only the contribution and jet
stacks; all other caller stacks and registers 8--15 are preserved.
-/

namespace SubexponentialSAT.SubexpJetCellProgram

open BitProgram StructuredCalls

abbrev Code := Cmd 16 128

end SubexponentialSAT.SubexpJetCellProgram

end OAI.Algorithms
end


