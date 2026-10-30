-- Prove2me | Definitions.Def_OAIQ081S003
-- name    : OAIQ081S003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:22:01.645137+00:00
-- url     : https://prove2.me/theorems/7c3aa3e1-2274-447b-b6a2-d408a4103de2
-- title:
--   Definitions bundle OAIQ081S003 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 188 declarations of OpenAI's Lean: 120 definitions, 7 inductive types or structures and 61 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms.quotientStacks`, `OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms.stepLabel`, `OAI.Algorithms.SubexponentialSAT.ModularRingPrograms.mulPorts`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.OtherColor`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.OtherPosition`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.OtherSlot`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.blockSize`, `OAI.Algorithms.SubexponentialSAT.NilpotentDefect.PowerDivisible`, `OAI.Algorithms.SubexponentialSAT.NilpotentDefect.geometricInverse`, `OAI.Algorithms.SubexponentialSAT.NilpotentDefect.residueInverse`, `OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm.add`, `OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm.addWithCost`, `OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm.coeff`, `OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm.denote`, `OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm.scaleWithCost`, `OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm.truncate`, `OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm.truncateWithCost`, `OAI.Algorithms.SubexponentialSAT.PowerCalls.Ports`, `OAI.Algorithms.SubexponentialSAT.PowerCalls.powerPorts`, `OAI.Algorithms.SubexponentialSAT.PowerPrograms.callbackBound`, `OAI.Algorithms.SubexponentialSAT.PowerPrograms.mulPorts`, `OAI.Algorithms.SubexponentialSAT.PowerPrograms.stackState`, `OAI.Algorithms.SubexponentialSAT.QuarticSearch.checkAll`, `OAI.Algorithms.SubexponentialSAT.QuarticSearch.elements`, `OAI.Algorithms.SubexponentialSAT.QuarticSearch.poly`, `OAI.Algorithms.SubexponentialSAT.QuarticSearch.scan`, `OAI.Algorithms.SubexponentialSAT.QuarticSearch.vectors`, `OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms.budget`, `OAI.Algorithms.SubexponentialSAT.RemovalCharging.Family`, `OAI.Algorithms.SubexponentialSAT.RemovalCharging.Trace`, `OAI.Algorithms.SubexponentialSAT.RemovalCharging.Trace.insertions`, `OAI.Algorithms.SubexponentialSAT.RemovalCharging.Trace.live`, `OAI.Algorithms.SubexponentialSAT.RemovalCharging.Trace.removals`, `OAI.Algorithms.SubexponentialSAT.RemovalCharging.Trace.removed`, `OAI.Algorithms.SubexponentialSAT.RemovalCharging.widthCount`, `OAI.Algorithms.SubexponentialSAT.RemovalCharging.widthLiteralDegree`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.leftPorts`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.rightPorts`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.subtractPorts`, `OAI.Algorithms.SubexponentialSAT.SpectralRank.badWeightEquiv` and 87 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_ModularQuotientPrograms`, `SubexponentialSAT_ModularRingCore`, `SubexponentialSAT_MulticolorTypes`, `SubexponentialSAT_NilpotentDefect`, `SubexponentialSAT_PolynomialAlgorithm`, `SubexponentialSAT_PositiveWordProgram`, `SubexponentialSAT_PowerCalls`, `SubexponentialSAT_PowerPrograms`, `SubexponentialSAT_ProgramLinking`, `SubexponentialSAT_QuarticSearch`, `SubexponentialSAT_RecordMappedPrograms`, `SubexponentialSAT_RemovalCharging`, `SubexponentialSAT_SaturatingSubtractionProgram`, `SubexponentialSAT_SpectralRank`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_AsymptoticLayoutParameters`, `SubexponentialSAT_SqrtLog_AsymptoticSchedule`, `SubexponentialSAT_SqrtLog_BinaryArgmin`, `SubexponentialSAT_SqrtLog_BinaryArgminScan`, `SubexponentialSAT_SqrtLog_BucketProgramArithmetic`, `SubexponentialSAT_SqrtLog_BucketProgramBounds`, `SubexponentialSAT_SqrtLog_BucketProgramDot`, `SubexponentialSAT_SqrtLog_BucketProgramNormalize`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessBounds`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep`, `SubexponentialSAT_SqrtLog_BucketProgramProducedRankFiber`, `SubexponentialSAT_SqrtLog_BucketProgramProducedRankMatrix`, `SubexponentialSAT_SqrtLog_BucketProgramProducedRankTables`, `SubexponentialSAT_SqrtLog_BucketProgramRow`, `SubexponentialSAT_SqrtLog_BucketProgramShift`, `SubexponentialSAT_SqrtLog_BucketProgramSignature`, `SubexponentialSAT_SqrtLog_BucketTupleProgramHeadOrder`, `SubexponentialSAT_SqrtLog_CRTLocalProgramCall`, `SubexponentialSAT_SqrtLog_CRTLocalProgramLoops`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramLoop`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramVisit`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBasic`, `SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithm`, `SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithmEntry`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutPullback`, `SubexponentialSAT_SqrtLog_LayoutRank`, `SubexponentialSAT_SqrtLog_LayoutRowSelection`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramPrepare`, `SubexponentialSAT_SqrtLog_MomentsBoolean`, `SubexponentialSAT_SqrtLog_RingProgramBasic`, `SubexponentialSAT_SqrtLog_RingProgramFold`, `SubexponentialSAT_SqrtLog_RowSelectionProgramParser`, `SubexponentialSAT_SubexpJetCellProgram`, `SubexponentialSAT_SubexpSymbolicCost`, `SubexponentialSAT_Subexp_CollisionProgram`, `SubexponentialSAT_Subexp_ConstructivePacking`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`, `SubexponentialSAT_Subexp_MatrixSupport`, `SubexponentialSAT_Subexp_PackingMetadata`, `SubexponentialSAT_Subexp_ReadPlan`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S033`, `OAIQ081S034`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S042`, `OAIQ081S043` and `OAIQ081S044`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_cutoff_ratio`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_inverse_target`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_layout_guards`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_uniform_label_log`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost.eventually_envelope_with_words`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_ambient_commonBase_log` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_residual_enumeration_ambient_bound`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_cutoff_ratio`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_inverse_target`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_layout_guards`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_uniform_label_log`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost.eventually_envelope_with_words`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_ambient_commonBase_log` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_residual_enumeration_ambient_bound`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_NilpotentDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Divisibility of the marked defect

After the input coordinates have been substituted, the coefficient of U in
each incidence argument is divisible by p. Polynomial operations preserve
the stronger invariant that the coefficient of U^j is divisible by p^j.
This proves the high-U vanishing needed by canonical truncation.
-/

namespace SubexponentialSAT.NilpotentDefect

noncomputable section

open scoped BigOperators

section General

variable {A : Type*} [CommSemiring A]

/-- The coefficient of the j-th power carries at least j copies of p. -/
def PowerDivisible (p : A) (P : Polynomial A) : Prop :=
  ∀ j, p ^ j ∣ P.coeff j

end General

section Units

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Explicit finite geometric correction of an approximate inverse b. -/
def geometricInverse (a b : R) (μ : ℕ) : R :=
  b * ∑ j ∈ Finset.range μ, (1 - a * b) ^ j

theorem mul_geometricInverse (a b : R) (μ : ℕ)
    (hnil : (1 - a * b) ^ μ = 0) :
    a * geometricInverse a b μ = 1 := by
  unfold geometricInverse
  rw [← mul_assoc]
  have h := mul_neg_geom_sum (1 - a * b) μ
  simpa only [sub_sub_cancel, hnil, sub_zero] using h

/-- The residue inverse is lifted by any specified section, then corrected
by a finite geometric sum in the original ring. -/
def residueInverse {K : Type*} [Field K] (ρ : R →+* K)
    (lift : K → R) (μ : ℕ) (a : R) : R :=
  geometricInverse a (lift ((ρ a)⁻¹)) μ

theorem mul_residueInverse {K : Type*} [Field K] (ρ : R →+* K)
    (lift : K → R) (hsection : ∀ z, ρ (lift z) = z)
    (p : R) (μ : ℕ) (hnil : p ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → p ∣ x)
    (a : R) (ha : ρ a ≠ 0) :
    a * residueInverse ρ lift μ a = 1 := by
  apply mul_geometricInverse
  have hz : ρ (1 - a * lift ((ρ a)⁻¹)) = 0 := by
    simp only [map_sub, map_one, map_mul, hsection, mul_inv_cancel₀ ha, sub_self]
  obtain ⟨d, hd⟩ := hker _ hz
  rw [hd, mul_pow, hnil, zero_mul]

end Units

end

end SubexponentialSAT.NilpotentDefect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLinking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite program relocation and linking

Every linked block is an instruction table inside one finite program.  A block's
halt can be replaced by a jump to a caller-specified continuation.  The proofs
below transfer actual instruction traces, including that final instruction, and
preserve all ambient registers and stacks outside the block's assigned ports.

The finite sizes and maps are fixed when the linked program is constructed; they
do not inspect the unbounded input stacks.
-/

namespace SubexponentialSAT.ProgramLinking

variable {r s l R S L : ℕ}

@[simp] theorem extend_id {α γ : Type*} (g base : α → γ) :
    Function.extend id g base = g := by
  funext a
  exact Function.injective_id.extend_apply g base a

/-! ## Concrete disjoint linking -/

end SubexponentialSAT.ProgramLinking

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

open SubexponentialSAT.ProgramLinking

abbrev quotientStacks (remainder modulus input quotient : List Bool) : Fin 8 → List Bool :=
  ![remainder, [], [], [], [], modulus, input, quotient]

def stepLabel (pc : Fin 58) : Fin 65 := Fin.natAdd 4 (Fin.castAdd 3 pc)

end SubexponentialSAT.ModularQuotientPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed Boolean-stack programs for arithmetic with a supplied binary modulus. -/

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.ProgramLinking
def mulPorts : Fin 6 → Fin 7 := ![0, 1, 6, 2, 3, 4]

theorem mulPorts_injective : Function.Injective mulPorts := by decide


end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_MulticolorTypes
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

variable {r Q Δ : ℕ}

def blockSize (r Q Δ : ℕ) : ℕ := r ^ (Q * (Δ + 1))

@[simp] theorem blockSize_rat (r Q Δ : ℕ) :
    (blockSize r Q Δ : ℚ) = (r : ℚ) ^ (Q * (Δ + 1)) := by
  rw [blockSize, Nat.cast_pow]

abbrev OtherPosition (t : Fin Q) := {l : Fin Q // l ≠ t}
abbrev OtherSlot (i : Fin Δ) := {j : Fin Δ // j ≠ i}
abbrev OtherColor (g : Fin r) := {c : Fin r // c ≠ g}

end SubexponentialSAT.MulticolorTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_PolynomialAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable dense univariate polynomial arithmetic

Lists store coefficients from constant term upwards. Trailing zeroes are allowed.
The instrumented algorithms return their value and the number of coefficient-ring
additions and multiplications they actually perform. List manipulation and primitive
bit costs are separate. Recursive results are bound once and reused.
-/

namespace SubexponentialSAT.PolynomialAlgorithm

variable {R : Type*}

section Algorithms

variable [Semiring R]

/-- Dense addition; unmatched tails are returned without scalar arithmetic. -/
def addWithCost : List R → List R → List R × ℕ
  | [], Q => (Q, 0)
  | P, [] => (P, 0)
  | a :: P, b :: Q =>
      let rest := addWithCost P Q
      ((a + b) :: rest.1, rest.2 + 1)

def add (P Q : List R) : List R := (addWithCost P Q).1

/-- One scalar multiplication for every stored coefficient. -/
def scaleWithCost (a : R) : List R → List R × ℕ
  | [] => ([], 0)
  | b :: P =>
      let rest := scaleWithCost a P
      ((a * b) :: rest.1, rest.2 + 1)

/-- Truncation is just a prefix of the coefficient list. -/
def truncate (D : ℕ) (P : List R) : List R := P.take D

/-- Taking a prefix performs no coefficient-ring operations. -/
def truncateWithCost (D : ℕ) (P : List R) : List R × ℕ := (truncate D P, 0)

/-- Coefficient lookup, with zero beyond the stored list. -/
def coeff : List R → ℕ → R
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: P, n + 1 => coeff P n

@[simp] theorem addWithCost_cost (P Q : List R) :
    (addWithCost P Q).2 = min P.length Q.length := by
  induction P generalizing Q with
  | nil => simp [addWithCost]
  | cons a P ih =>
      cases Q with
      | nil => simp [addWithCost]
      | cons b Q => simp [addWithCost, ih ]

@[simp] theorem addWithCost_length (P Q : List R) :
    (addWithCost P Q).1.length = max P.length Q.length := by
  induction P generalizing Q with
  | nil => simp [addWithCost]
  | cons a P ih =>
      cases Q with
      | nil => simp [addWithCost]
      | cons b Q => simp [addWithCost, ih ]

@[simp] theorem length_add (P Q : List R) :
    (add P Q).length = max P.length Q.length := addWithCost_length P Q

@[simp] theorem scaleWithCost_cost (a : R) (P : List R) :
    (scaleWithCost a P).2 = P.length := by
  induction P with
  | nil => rfl
  | cons b P ih => simp [scaleWithCost, ih]

@[simp] theorem scaleWithCost_length (a : R) (P : List R) :
    (scaleWithCost a P).1.length = P.length := by
  induction P with
  | nil => rfl
  | cons b P ih => simp [scaleWithCost, ih]

omit [Semiring R] in
@[simp] theorem length_truncate (D : ℕ) (P : List R) :
    (truncate D P).length = min D P.length := by simp [truncate]

omit [Semiring R] in
@[simp] theorem truncateWithCost_cost (D : ℕ) (P : List R) :
    (truncateWithCost D P).2 = 0 := rfl

end Algorithms

section Semantics

variable [CommSemiring R]

/-- Mathematical meaning of a coefficient list; only this interpretation is
noncomputable. The list algorithms above use no classical choice. -/
noncomputable def denote : List R → Polynomial R
  | [] => 0
  | a :: P => Polynomial.C a + Polynomial.X * denote P

@[simp] theorem denote_nil : denote ([] : List R) = 0 := rfl

@[simp] theorem denote_cons (a : R) (P : List R) :
    denote (a :: P) = Polynomial.C a + Polynomial.X * denote P := rfl

@[simp] theorem coeff_denote (P : List R) (n : ℕ) :
    (denote P).coeff n = coeff P n := by
  induction P generalizing n with
  | nil => simp [denote, coeff]
  | cons a P ih =>
      cases n with
      | zero => simp [denote, coeff]
      | succ n =>
          simp [denote, coeff, Polynomial.coeff_X_mul, ih]

@[simp] theorem denote_addWithCost (P Q : List R) :
    denote (addWithCost P Q).1 = denote P + denote Q := by
  induction P generalizing Q with
  | nil => simp [addWithCost]
  | cons a P ih =>
      cases Q with
      | nil => simp [addWithCost]
      | cons b Q =>
          simp only [addWithCost, denote_cons, ih, map_add]
          ring

@[simp] theorem denote_add (P Q : List R) :
    denote (add P Q) = denote P + denote Q := denote_addWithCost P Q

@[simp] theorem denote_scaleWithCost (a : R) (P : List R) :
    denote (scaleWithCost a P).1 = Polynomial.C a * denote P := by
  induction P with
  | nil => simp [scaleWithCost]
  | cons b P ih =>
      simp only [scaleWithCost, denote_cons, ih, map_mul]
      ring

end Semantics

end SubexponentialSAT.PolynomialAlgorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_PositiveWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A primitive implementation of the final positivity test

The same seven-label program scans every little-endian Boolean word.  It
returns true exactly when the encoded natural number is positive.  It may
leave an unused suffix after finding a one bit; only the output head is read
by the already verified primitive compiler.
-/

namespace SubexponentialSAT.PositiveWordProgram

@[simp] theorem update_stack (xs ys : List Bool) :
    Function.update (fun _ : Fin 1 => xs) 0 ys = fun _ => ys := by
  funext i
  fin_cases i
  simp

end SubexponentialSAT.PositiveWordProgram

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

/-- Base, exponent, accumulator, five work ports, and counter scratch. -/
def stackState (base exponent acc w₃ w₄ w₅ w₆ w₇ counterScratch : List Bool) :
    Fin 9 → List Bool := ![base, exponent, acc, w₃, w₄, w₅, w₆, w₇, counterScratch]

@[simp] theorem stack_0 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 0 = b := rfl
@[simp] theorem stack_1 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 1 = e := rfl
@[simp] theorem stack_2 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 2 = a := rfl
@[simp] theorem stack_3 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 3 = w₃ := rfl
@[simp] theorem stack_4 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 4 = w₄ := rfl
@[simp] theorem stack_5 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 5 = w₅ := rfl
@[simp] theorem stack_6 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 6 = w₆ := rfl
@[simp] theorem stack_7 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 7 = w₇ := rfl
@[simp] theorem stack_8 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 8 = t := rfl

@[simp] theorem update_2 (b e a w₃ w₄ w₅ w₆ w₇ t next : List Bool) :
    Function.update (stackState b e a w₃ w₄ w₅ w₆ w₇ t) 2 next =
      stackState b e next w₃ w₄ w₅ w₆ w₇ t := by
  funext k; fin_cases k <;> simp [stackState]
@[simp] theorem update_3 (b e a w₃ w₄ w₅ w₆ w₇ t next : List Bool) :
    Function.update (stackState b e a w₃ w₄ w₅ w₆ w₇ t) 3 next =
      stackState b e a next w₄ w₅ w₆ w₇ t := by
  funext k; fin_cases k <;> simp [stackState]
@[simp] theorem update_4 (b e a w₃ w₄ w₅ w₆ w₇ t next : List Bool) :
    Function.update (stackState b e a w₃ w₄ w₅ w₆ w₇ t) 4 next =
      stackState b e a w₃ next w₅ w₆ w₇ t := by
  funext k; fin_cases k <;> simp [stackState]

def mulPorts (i : Fin 6) : Fin 9 := ![3, 2, 4, 5, 6, 7] i

theorem mulPorts_injective : Function.Injective mulPorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [mulPorts]

def callbackBound (base : List Bool) (i : ℕ) : ℕ :=
  50 * (base.length + 1) * (2 + (i + 1) * base.length)

theorem callbackBound_monotone (base : List Bool) : Monotone (callbackBound base) := by
  intro i j hij
  dsimp [callbackBound]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _
    (Nat.add_le_add_right hij 1)) 2)

end SubexponentialSAT.PowerPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_PowerCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving variable-power calls on fixed assigned ports. -/

namespace SubexponentialSAT.PowerCalls

structure Ports (S : ℕ) where
  base : Fin S
  exponent : Fin S
  out : Fin S
  work : Fin 7 ↪ Fin S
  out_ne_base : out ≠ base
  out_ne_exponent : out ≠ exponent
  work_ne_base : ∀ i, work i ≠ base
  work_ne_exponent : ∀ i, work i ≠ exponent
  work_ne_out : ∀ i, work i ≠ out

@[simp] theorem base_ne_work {S : ℕ} (p : Ports S) (i : Fin 7) :
    p.base ≠ p.work i := (p.work_ne_base i).symm
@[simp] theorem exponent_ne_work {S : ℕ} (p : Ports S) (i : Fin 7) :
    p.exponent ≠ p.work i := (p.work_ne_exponent i).symm
@[simp] theorem out_ne_work {S : ℕ} (p : Ports S) (i : Fin 7) :
    p.out ≠ p.work i := (p.work_ne_out i).symm

def powerPorts {S : ℕ} (p : Ports S) : Fin 9 → Fin S :=
  ![p.base, p.work 0, p.out, p.work 1, p.work 2, p.work 3,
    p.work 4, p.work 5, p.work 6]

theorem powerPorts_injective {S : ℕ} (p : Ports S) :
    Function.Injective (powerPorts p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [powerPorts, p.work.injective.eq_iff, p.work_ne_base,
      p.work_ne_out, p.out_ne_base, p.out_ne_base.symm]

end SubexponentialSAT.PowerCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_QuarticSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable search for an irreducible quartic

The execution data are four field coefficients. Polynomial expressions occur
only in the correctness proof. Linear and quadratic trial division is performed
by fixed-size synthetic-division formulas.
-/
namespace SubexponentialSAT.QuarticSearch

open Polynomial
open scoped BigOperators

/-- Exhaustive explicit list of coefficient vectors. -/
def vectors {A : Type*} (alphabet : List A) : (d : ℕ) → List (Fin d → A)
  | 0 => [fun i => Fin.elim0 i]
  | d + 1 => alphabet.flatMap fun a => (vectors alphabet d).map (Fin.cons a)

theorem mem_vectors {A : Type*} (alphabet : List A) (h : ∀ a, a ∈ alphabet)
    (d : ℕ) (v : Fin d → A) : v ∈ vectors alphabet d := by
  induction d with
  | zero =>
      have he : v = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
      simp [vectors, he]
  | succ d ih =>
      rw [vectors, List.mem_flatMap]
      refine ⟨v 0, h _, ?_⟩
      apply List.mem_map.mpr
      exact ⟨Fin.tail v, ih _, Fin.cons_self_tail v⟩

theorem length_vectors {A : Type*} (alphabet : List A) (d : ℕ) :
    (vectors alphabet d).length = alphabet.length ^ d := by
  induction d with
  | zero => simp [vectors]
  | succ d ih =>
      simp [vectors, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

/-- Mathematical interpretation; the search does not execute polynomial operations. -/
noncomputable def poly {F : Type*} [Semiring F] {d : ℕ} (c : Fin d → F) : F[X] :=
  X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ)

/-- Polynomial interpretation commutes with a coefficient homomorphism. -/
theorem map_poly {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) {d : ℕ} (c : Fin d → R) :
    (poly c).map f = poly (fun i => f (c i)) := by
  simp [poly, Polynomial.map_sum]

section PolynomialProof

variable {F : Type*} [CommRing F] [Nontrivial F]

omit [Nontrivial F] in
theorem poly_monic {d : ℕ} (c : Fin d → F) : (poly c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

@[simp] theorem poly_natDegree {d : ℕ} (c : Fin d → F) : (poly c).natDegree = d := by
  unfold poly
  rw [natDegree_add_eq_left_of_degree_lt]
  · simp
  · simpa using degree_sum_fin_lt c

omit [Nontrivial F] in
theorem poly_of_coeff {d : ℕ} (f : F[X]) (hm : f.Monic) (hd : f.natDegree = d) :
    poly (fun i : Fin d => f.coeff i) = f := by
  have he := f.as_sum_range_C_mul_X_pow
  rw [hd, Finset.sum_range_succ] at he
  have hc : f.coeff d = 1 := hd ▸ hm.coeff_natDegree
  rw [hc, C_1, one_mul] at he
  unfold poly
  have hs : (∑ i : Fin d, C (f.coeff (i : ℕ)) * X^(i : ℕ)) =
      ∑ i ∈ Finset.range d, C (f.coeff i) * X^i :=
    Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X^i) d
  change X^d + (∑ i : Fin d, C (f.coeff (i : ℕ)) * X^(i : ℕ)) = f
  rw [hs]
  exact (add_comm _ _).trans he.symm

end PolynomialProof


/-- The explicit residue representatives, in increasing order. -/
def elements (p : ℕ) : List (ZMod p) :=
  List.ofFn fun i : Fin p => (i.val : ZMod p)

@[simp] theorem length_elements (p : ℕ) : (elements p).length = p := by
  simp [elements]

theorem mem_elements (p : ℕ) [Fact p.Prime] (a : ZMod p) : a ∈ elements p := by
  apply List.mem_ofFn.mpr
  exact ⟨⟨a.val, ZMod.val_lt a⟩, by simp⟩

/-- Boolean list conjunction, counting the tests actually performed. -/
def checkAll {A : Type*} (test : A → Bool) : List A → Bool × ℕ
  | [] => (true, 0)
  | a :: as => if test a then
      let rest := checkAll test as
      (rest.1, rest.2 + 1)
    else (false, 1)

theorem checkAll_value {A : Type*} (test : A → Bool) (as : List A) :
    (checkAll test as).1 = as.all test := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      by_cases h : test a = true <;> simp [checkAll, h, ih]

/-- Ordered exhaustive search, counting both candidates and inner tests. -/
def scan {A : Type*} (evaluate : A → Bool × ℕ) : List A → Option A × ℕ × ℕ
  | [] => (none, 0, 0)
  | a :: as =>
      let current := evaluate a
      if current.1 then (some a, 1, current.2)
      else
        let rest := scan evaluate as
        (rest.1, rest.2.1 + 1, rest.2.2 + current.2)

theorem scan_value {A : Type*} (evaluate : A → Bool × ℕ) (as : List A) :
    (scan evaluate as).1 = as.find? (fun a => (evaluate a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      by_cases h : (evaluate a).1 = true <;> simp [scan, h, ih]

end SubexponentialSAT.QuarticSearch

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

variable {α : Type*} {r s : ℕ}

def budget (enc : α → List Bool) (cost : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: rest => 6 * (enc a).length + cost a + 7 + budget enc cost rest

end SubexponentialSAT.RecordMappedPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RemovalCharging
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

abbrev Family (α : Type*) := Finset (Finset α)

def widthCount (F : Family α) (j : ℕ) : ℕ :=
  (F.filter fun C => C.card = j).card

def widthLiteralDegree (F : Family α) (j : ℕ) (a : α) : ℕ :=
  (F.filter fun C => C.card = j ∧ a ∈ C).card

/-- A finite replacement trace.  All fields are local properties of actual
finite sets; no cumulative counting conclusion is assumed. -/
structure Trace (α : Type*) [DecidableEq α] (T : ℕ) where
  formula : ℕ → Family α
  inserted : ℕ → Family α
  next_subset : ∀ t < T, formula (t + 1) ⊆ formula t ∪ inserted t
  inserted_live : ∀ t < T, inserted t ⊆ formula (t + 1)
  fresh : ∀ t < T, Disjoint (formula t) (inserted t)
  inserted_nonempty : ∀ t < T, ∀ Q ∈ inserted t, Q.Nonempty
  removed_subset : ∀ t < T, ∀ C ∈ formula t,
    C ∉ formula (t + 1) → ∃ Q ∈ inserted t, Q ⊂ C

namespace Trace

variable {T : ℕ} (tr : Trace α T)

/-- Clauses introduced by the trace that are still alive. Root clauses start
untracked; survival is tested against the actual next formula. -/
def live : ℕ → Family α
  | 0 => ∅
  | t + 1 => (live t ∩ tr.formula (t + 1)) ∪ tr.inserted t

@[simp] theorem live_zero : tr.live 0 = ∅ := rfl

@[simp] theorem live_succ (t : ℕ) :
    tr.live (t + 1) = (tr.live t ∩ tr.formula (t + 1)) ∪ tr.inserted t := rfl

/-- Cumulative individual insertion events, including clauses later removed. -/
def insertions (t j : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, widthCount (tr.inserted s) j

def removed (t : ℕ) : Family α := tr.live t \ tr.formula (t + 1)

def removals (t j : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, widthCount (tr.removed s) j

end Trace

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

def leftPorts : Fin 3 → Fin 8 := ![2, 4, 6]
def rightPorts : Fin 3 → Fin 8 := ![3, 5, 6]
def subtractPorts : Fin 3 → Fin 8 := ![2, 3, 6]

end SubexponentialSAT.SaturatingSubtractionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SpectralRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Rank defects of diagonal operators

The rank here is the dimension of the actual range of a linear map.  The main
bound is obtained by identifying that range with the span of precisely those
basis vectors on which the diagonal coefficient is nonzero.
-/

namespace SubexponentialSAT.SpectralRank

open Module Submodule
open scoped BigOperators

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Partition the bad basis indices according to their actual finite weight.
This is an explicit equivalence, so the later multiplicity sum counts each
basis vector exactly once. -/
def badWeightEquiv (weight : ι → ℕ) (n : ℕ) (hweight : ∀ i, weight i ≤ n)
    (good : Finset ℕ) :
    {i // weight i ∉ good} ≃
      (Σ w : {w : Fin (n + 1) // w.1 ∉ good}, {i // weight i = w.1.1}) where
  toFun i := ⟨⟨⟨weight i.1, Nat.lt_succ_of_le (hweight i.1)⟩, i.2⟩, ⟨i.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by rw [x.2.2]; exact x.1.2⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨⟨w, hw⟩, hg⟩, ⟨i, hi⟩⟩
    dsimp only at hi
    subst w
    rfl

end SubexponentialSAT.SpectralRank

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

namespace Filter

abbrev Regs := Fin 16 → Bool


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact, computable square-root-log scheduling. No algorithmic assertion is
hidden in these numerical lemmas. Small inputs may have schedule zero. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

noncomputable def logSize (n : ℕ) : ℝ := Real.logb 2 ((n : ℝ) + 16)
noncomputable def logLogSize (n : ℕ) : ℝ := Real.logb 2 (logSize n)
noncomputable def binaryScale (n : ℕ) : ℝ :=
  (n : ℝ) * logLogSize n ^ 2 / Real.sqrt (logSize n)

def L (n : ℕ) : ℕ := Nat.log2 (n + 16) + 1
def w (n : ℕ) : ℕ := Nat.log2 (L n) + 1
def s (n : ℕ) : ℕ := Nat.sqrt (L n) / w n ^ 2

theorem L_pos (n : ℕ) : 0 < L n := by unfold L; omega

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer layout parameters agreed with the layout and spectral components.
The occurrence bound `b` is an explicit argument. Positivity assumptions are
kept on theorems rather than built into an opaque choice. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

def layoutR (n : ℕ) : ℕ := max 2 (s n)
def layoutDen (n : ℕ) : ℕ := 64 * (Nat.log2 (layoutR n) + 1)
def layoutQ (n : ℕ) : ℕ := L n / layoutDen n
def layoutEnergy (n b : ℕ) : ℕ := Nat.log2 (64 * b * layoutR n * L n ^ 2) + 1
def layoutCutoff (n b : ℕ) : ℕ := Nat.sqrt (128 * layoutQ n * layoutEnergy n b) + 4
def layoutEpsilon (n b : ℕ) : ℚ := 1 / (32 * b * layoutR n * L n ^ 2 : ℕ)

theorem layoutR_ge_two (n : ℕ) : 2 ≤ layoutR n := le_max_left _ _

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
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

structure Entry where
  payload : List Bool
  score : List Bool
  deriving DecidableEq

def empty : Entry := ⟨[], []⟩

def store (next best : Entry) (queue : List Bool) : Fin 9 → List Bool :=
  ![next.payload, next.score, best.payload, best.score, [], [], [], [], queue]

def compareStacks : Fin 3 → Fin 9 := ![4, 5, 6]

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgminScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A measured binary argmin scan with a paid loader

`LoaderSpec` is a refinement obligation on a fixed, executable command. It
requires an actual `StructuredCalls.Eval` for every callback, including the
final empty callback; it is not an oracle or an instruction for evaluating a
mathematical score. A caller may satisfy it by parsing prepared records or by
enumerating candidates and executing a score program. The incumbent score is
cached. Its first evaluation and the preparation of the initial incumbent are
outside this scan and must be charged by the caller.
-/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

def Fits (B C : ℕ) (a : Entry) : Prop :=
  a.score.length = B ∧ a.payload.length ≤ C

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

open scoped BigOperators

def addWork : Fin 5 ↪ Fin 9 where
  toFun i := ⟨i.val+4, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

/-- Offset summation is exactly the integer signature translated by hW. -/
def offsetSignature {h : ℕ} (W : ℤ) (row : Fin h → ℤ) (x : Fin h → Bool) : ℤ :=
  ∑ i, if x i then W+row i else W

end SubexponentialSAT.SqrtLog.BucketProgram

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

def choicePort : Fin 9 → Fin 12 := Fin.castAdd 3

def dotStepBound (W coeff acc : List Bool) : ℕ :=
  200*(W.length+coeff.length+acc.length+2)^2+30

end SubexponentialSAT.SqrtLog.BucketProgram

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

def rowWidth (W : List Bool) (coeffs : List (List Bool)) (acc : List Bool) : ℕ :=
  acc.length + coeffs.length*(W.length+1) + (coeffs.map List.length).sum

def rowBudget (W : List Bool) (coeffs : List (List Bool)) (acc : List Bool) : ℕ :=
  (coeffs.length+1)*(200*(rowWidth W coeffs acc+2)^2+34)

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical, positive encodings for exact integer row signatures.  The
added one is common to all assignments and makes the normalizer total on
all legitimate row results, including the empty head. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

def normalizeRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def normalizePorts : Fin 3 → Fin 12 := fun i => ⟨i.val+2, by omega⟩

def canonicalRowBudget (W : List Bool) (coeffs : List (List Bool)) : ℕ :=
  rowBudget W coeffs [true] + 9*rowWidth W coeffs [true]+22

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

def rowCallPorts : Fin 12 → Fin 15 := Fin.castAdd 3

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial bounds for the physical integer-signature scan. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

def widthBound (W : List Bool) (h B : ℕ) : ℕ := 1+h*(W.length+1+B)

def rowCostBound (W : List Bool) (h B : ℕ) : ℕ :=
  (h+1)*(200*(widthBound W h B+2)^2+34)+9*widthBound W h B+22

def signatureRowBound (W : List Bool) (h B : ℕ) : ℕ :=
  9*(h*(2*B+1))+7+(7*h+5)+2+(rowCostBound W h B+1)+8*(widthBound W h B+1)+8

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

def preReverseCost (xs : List (List Bool)) : ℕ :=
  (xs.map (fun x => 17*x.length+17)).sum+1

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Primitive preparation of a nonnegative shifted integer coefficient.
The input signed integer is a pair P-N; W dominates N. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

def subtractPort : Fin 8 → Fin 10 := Fin.castAdd 2

def shiftWork : Fin 5 ↪ Fin 10 where
  toFun i := ⟨i.val+3, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

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

abbrev SignedWord := List Bool × List Bool

def preShiftPort : Fin 10 → Fin 14 := Fin.castAdd 4

def preStepCost (W : List Bool) (a : SignedWord) : ℕ :=
  600*(W.length+a.2.length+a.1.length+1)^2+100

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

def preScanCost (W : List Bool) (xs : List SignedWord) : ℕ :=
  (xs.map (fun a => preStepCost W a+2)).sum+1

def preOutputLength (W : List Bool) (xs : List SignedWord) : ℕ :=
  (xs.map (fun a => W.length+a.2.length+a.1.length+1)).sum

def preReversePorts : Fin 4 → Fin 14 := ![11,8,12,13]

def preRowCost (W : List Bool) (xs : List SignedWord) : ℕ :=
  preScanCost W xs+29*preOutputLength W xs+23*xs.length+20

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

def preRowPorts : Fin 14 → Fin 17 := Fin.castAdd 3

def preMatrixPayload (W : List Bool) (rows : List (List SignedWord)) : ℕ :=
  (rows.map (fun row => 2*preOutputLength W row+row.length)).sum

def preMatrixReversePorts : Fin 4 → Fin 17 := ![15,11,12,16]

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer semantics and explicit polynomial bounds for the concrete
signed-coefficient preprocessing machine. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

def preWordsBounded (L : ℕ) (xs : List SignedWord) : Prop :=
  ∀ a∈xs, a.1.length ≤ L ∧ a.2.length ≤ L

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

variable {r Q Δ : ℕ}

/-- The exact length of every type encoding. -/
def typeWidth (r Q Δ : ℕ) : ℕ := ((Δ + 1) * Q) * r

/-- A computable position in the flattened register-position-color order. -/
def codeIndex (a : Fin (Δ + 1)) (q : Fin Q) (c : Fin r) : Fin (typeWidth r Q Δ) :=
  finProdFinEquiv (finProdFinEquiv (a, q), c)

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

open SubexponentialSAT.MulticolorTypes

section Encoding

variable {r Q Δ : ℕ}

def wordWidth (r Q : ℕ) : ℕ := Q * r

end Encoding

end SubexponentialSAT.Subexp.ReadPlan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSymbolicCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform symbolic list costs for growing parameters

The old canonical-list algorithm has an explicit fixed-degree event bound. This
module retains its interfaces and makes all parameter dependence visible. It also
refines exponent addition to an actual unary bit-string algorithm. Unary is used
only for exponent indices, whose values are O(D), never for ring coefficients.

Counters below are charged operations/bit inspections. A primitive tape-machine
execution certificate is a separate requirement.
-/

namespace SubexponentialSAT.SubexpSymbolicCost

/-- Executable callbacks only. The semantic decoder is deliberately absent. -/
structure RingProgram (C : Type*) where
  zeroRun : C × ℕ
  oneRun : C × ℕ
  addRun : C → C → C × ℕ
  mulRun : C → C → C × ℕ
  negRun : C → C × ℕ

end SubexponentialSAT.SubexpSymbolicCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstructivePacking
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

/-- A supplied, duplicate-free enumeration of the whole finite type. -/
structure FiniteEnumeration (α : Type*) where
  values : List α
  nodup : values.Nodup
  complete : ∀ x, x ∈ values

/-- All operational packing inputs are explicit finite data. -/
structure PackingData (V U : Type*) where
  vertices : FiniteEnumeration V
  types : FiniteEnumeration U
  label : V → U

namespace PackingData

variable {V U : Type*} [DecidableEq U]

/-- One scan of the vertex list extracts a type fiber in the original order. -/
def bucket (P : PackingData V U) (u : U) : List V :=
  P.vertices.values.filter fun v => decide (P.label v = u)

theorem bucket_nodup (P : PackingData V U) (u : U) : (P.bucket u).Nodup :=
  P.vertices.nodup.filter _

@[simp] theorem mem_bucket (P : PackingData V U) (u : U) (v : V) :
    v ∈ P.bucket u ↔ P.label v = u := by
  simp [bucket, P.vertices.complete v]

/-- The minimum scan uses the vertex-list length as its initial cap. -/
def minCount (P : PackingData V U) : List U → ℕ
  | [] => P.vertices.values.length
  | u :: us => min (P.bucket u).length (P.minCount us)

def blockCount (P : PackingData V U) : ℕ := P.minCount P.types.values

theorem minCount_le_bucket (P : PackingData V U) (us : List U) (u : U) (hu : u ∈ us) :
    P.minCount us ≤ (P.bucket u).length := by
  induction us with
  | nil => simp at hu
  | cons v us ih =>
    rcases List.mem_cons.mp hu with huv | hu
    · subst v
      exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hu)

theorem blockCount_le_bucket (P : PackingData V U) (u : U) :
    P.blockCount ≤ (P.bucket u).length :=
  P.minCount_le_bucket P.types.values u (P.types.complete u)

/-- Indexed placement of a type in a block. -/
def vertexAt (P : PackingData V U) (i : Fin P.blockCount) (u : U) : V :=
  (P.bucket u).get ⟨i.val, lt_of_lt_of_le i.isLt (P.blockCount_le_bucket u)⟩

@[simp] theorem label_at (P : PackingData V U) (i : Fin P.blockCount) (u : U) :
    P.label (P.vertexAt i u) = u :=
  (P.mem_bucket u _).mp (List.get_mem _ _)

variable [DecidableEq V]

/-- Find the coordinate's position in its own bucket and check if it was selected. -/
def lookup (P : PackingData V U) (v : V) : Option (Fin P.blockCount × U) :=
  let u := P.label v
  let n := (P.bucket u).idxOf v
  if h : n < P.blockCount then some (⟨n, h⟩, u) else none

@[simp] theorem lookup_at (P : PackingData V U) (i : Fin P.blockCount) (u : U) :
    P.lookup (P.vertexAt i u) = some (i, u) := by
  dsimp only [lookup]
  rw [P.label_at i u]
  have hi : (P.bucket u).idxOf (P.vertexAt i u) = i.val :=
    List.get_idxOf (P.bucket_nodup u) _
  simp only [hi, dite_eq_left i.isLt]

theorem lookup_sound (P : PackingData V U) (v : V) (z : Fin P.blockCount × U)
    (h : P.lookup v = some z) : P.vertexAt z.1 z.2 = v := by
  dsimp only [lookup] at h
  split at h
  next hlt =>
    have hz := Option.some.inj h
    rw [← hz]
    exact List.idxOf_get _
  next hnot => cases h

end PackingData

end SubexponentialSAT.Subexp.ConstructivePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Literal incidence pullback

An incidence is sent to its original variable by `owner`. The pullback
duplicates a variable value; the dual operation adds row coefficients on
each fiber. No inverse matrix or new basis is used in these definitions.
-/

namespace SubexponentialSAT.SqrtLog.LayoutPullback

open scoped BigOperators

variable {I V R : Type*} [Fintype I] [Fintype V] [DecidableEq V]

def row [AddCommMonoid R] (owner : I → V) (a : I → R) (v : V) : R :=
  ∑ i, if owner i = v then a i else 0

end SubexponentialSAT.SqrtLog.LayoutPullback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRowSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Selecting actual integer constraint rows

This module isolates the semantic certificate for row selection. A later finite
minor search may produce the certificate; rational spanning is used only before
reduction, so the actual rows and their integer coefficient bounds are retained.
-/

namespace SubexponentialSAT.SqrtLog.LayoutRowSelection

open scoped BigOperators

universe u v

variable {J : Type u} {V : Type v} [Fintype J] [Fintype V]

def rationalRows (C : J → V → ℤ) : J → (V → ℚ) :=
  fun j v => (C j v : ℚ)

end SubexponentialSAT.SqrtLog.LayoutRowSelection

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rational row-space bounds for literal integer constraint families. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open Module LayoutPullback LayoutRowSelection

variable {J I V : Type*} [Fintype J] [Fintype I] [Fintype V]

def rowSpace (C : J → V → ℤ) : Submodule ℚ (V → ℚ) :=
  Submodule.span ℚ (Set.range (rationalRows C))

noncomputable def rowRank (C : J → V → ℤ) : ℕ := finrank ℚ (rowSpace C)

end SubexponentialSAT.SqrtLog.LayoutRank

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

abbrev WordPair := List Bool × List Bool

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocatable finite-bank contract for integer incidence entries, and the
fixed physical storage layout used by the direct all-row matrix builder. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram

abbrev Pair := List Bool × List Bool

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact row-major matrix emitted by the entry scanner, in the actual
selected identifier order. These proofs introduce no runtime permutation. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

/-- The coefficient matrix uses exactly the scanner's selected-ID order. -/
def selectedMatrix (C : ℕ → ℕ → ℤ) (D : ℕ) (js : List ℕ) : Fin D → Fin js.length → ℤ :=
  fun j i=>C j.val (js.get i)

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT

def fiberIndices (query : ℕ) : ℕ → List (ℕ × ℕ) → List ℕ
  | _, [] => []
  | index, p::ps => if p.1=query then index::fiberIndices query (index+1) ps
      else fiberIndices query (index+1) ps

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal equality between the runtime owner-fiber sum and an integer
matrix column. Both use the original incidence order and original owner IDs. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators

/-- A physical owner-fiber result computes this exact literal matrix, even
when incidence factors and variable labels are not consecutive. -/
def fiberMatrix {D n : ℕ} (owner : Fin D → Fin n)
    (entry : Fin D → Fin D → ℤ) : Fin D → Fin n → ℤ :=
  fun j v=>∑ i,if owner i=v then entry j i else 0

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

inductive Metadata where
  | covered (block typeCode : List Bool)
  | leftover (rank : List Bool)

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

def unary (n : ℕ) : List Bool := List.replicate n true

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramVisit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT

def predicate (rows : List (List Bool)) (low : List Bool) (z j : ℕ) : Bool :=
  low.getD j false && (rows.getD j []).getD z false

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT

def chosenIds (p : ℕ → Bool) (n : ℕ) : List ℕ := (List.range n).filter p

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixSupport
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

section Operators

variable {K : Type*} [Field K]

/-- The full permutation at t acts at every other position. -/
def activePositions (t : Fin Q) : Finset (Fin Q) := Finset.univ.erase t

end Operators

end SubexponentialSAT.Subexp.MatrixSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete head-selection stage. All three objects consumed by the
matrix/bucket phase are computed from runtime masters by fixed programs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

def selectedHeads (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) : List ℕ :=
  HeadIdentifierProgram.chosenIds (HeadIdentifierProgram.predicate rows low z) n

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rank-sensitive cardinality of the actual attained Cartesian inventory.
The hypotheses constrain entry values, not the cardinalities of head tables. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open LeafHeadSetupProgram
open scoped BigOperators

def headRank (C : ℕ → ℕ → ℤ) (D n : ℕ)
    (rows : List (List Bool)) (low : List Bool) (z : ℕ) : ℕ :=
  LayoutRank.rowRank (selectedMatrix C D (selectedHeads n rows low z))

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsBoolean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Boolean coordinate assembly and actual head weights. This avoids field
coordinates or residue representatives: head values are genuine Boolean bits. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators

variable {V G R : Type*} [Fintype V] [Fintype G] [DecidableEq V] [DecidableEq G]

def Head (head : V → G) (g : G) := {v : V // head v = g}

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketTupleProgramHeadOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The selected variable IDs give a canonical order on a typed free head. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

noncomputable section

def idOrder {n : ℕ} (js : List ℕ) (hb : ∀ v ∈ js, v < n)
    (i : Fin js.length) : Fin n :=
  ⟨js.get i, hb _ (List.get_mem ..)⟩

theorem idOrder_injective {n : ℕ} (js : List ℕ) (hb : ∀ v ∈ js, v < n)
    (hn : js.Nodup) : Function.Injective (idOrder js hb) := by
  intro i j he
  exact List.nodup_iff_injective_get.mp hn (congrArg Fin.val he)

variable {n r : ℕ} (H : Finset (Fin n))
  (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r)
  (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
  (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)

def freeOrderFun (i : Fin js.length) : Moments.Head head g := by
  let v := idOrder js hb i
  have hv : v.val ∈ js := List.get_mem ..
  let witness := (hs v).mp hv
  exact ⟨⟨v, witness.choose⟩, witness.choose_spec⟩

theorem freeOrderFun_val (i : Fin js.length) :
    (freeOrderFun H head g js hb hs i).val.val = idOrder js hb i := by
  rfl

end

end OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
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

abbrev Store := Fin 256 → List Bool

/-- The shared arithmetic workspace is below the persistent CRT ports. -/
def LowFrame (base s : Store) : Prop := ∀ i : Fin 256, i.val < 205 → s i = base i

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed native binary calls at arbitrary persistent ports. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

def CachePort (i : Fin 256) : Prop :=
  205 ≤ i.val ∧ i ≠ 240 ∧ i ≠ 241 ∧ i ≠ 244 ∧ i ≠ 245

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite coefficient tests for arbitrary-degree irreducible search

Only vectors, finite lists, and scalar arithmetic are executed. `ofFn` and
the polynomial interpretation occur solely in the correctness proofs.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial
open scoped BigOperators

/-- Read a coefficient with zero padding outside the stored vector. -/
def entry {R : Type*} [Zero R] {n : ℕ} (a : Fin n → R) (j : ℕ) : R :=
  if h : j < n then a ⟨j, h⟩ else 0

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable descending triangular solution for the original parity coefficients.
There are R coordinate updates, each scanning R potential upper entries.
No matrix inverse is executed. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators

def target (A j : ℕ) : ℤ := (-1 : ℤ) ^ A * (-2 : ℤ) ^ j

def upperTail (A R : ℕ) (j : Fin R) (v : Fin R → ℤ) : ℤ :=
  ∑ k : Fin R, if j.val < k.val then
    (A.choose (k.val - j.val) : ℤ) * v k else 0

def solve (A R : ℕ) : ℕ → (Fin R → ℤ)
  | 0 => fun _ => 0
  | n + 1 =>
    let v := solve A R n
    if h : n < R then
      let j : Fin R := ⟨R - 1 - n, by omega⟩
      Function.update v j (target A j.val - upperTail A R j v)
    else v

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithmEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable scalar formulas for the exact cleared integer matrix entries. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

def coefficientAt (A R j : ℕ) : ℤ :=
  if h : j < R then solve A R R ⟨j, h⟩ else 0

/-- The numeric loop uses only sign, powers, binomial coefficients, and a prefix sum. -/
def scalarSum (A R d h : ℕ) : ℤ :=
  (-1 : ℤ) ^ d * ∑ k ∈ Finset.range (R - d),
    coefficientAt A R (d + k) * 2 ^ (R - 1 - (d + k)) * (h.choose k : ℤ)

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Dynamic-degree coefficient arithmetic

These executable callbacks operate on a runtime-sized coefficient vector.
Their counters include all scalar callbacks and one event per vector/list
entry. A separate flat-stack refinement must account for scanning serialized
vectors; callback event counts alone are not claimed to be primitive time.
-/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

abbrev Code (C : Type*) (d : ℕ) := Fin d → C

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

abbrev Triple (C : Type*) := C × C × C

end SubexponentialSAT.SqrtLog.RingProgram

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

def regPorts : Fin 8 → Fin 16 := Fin.castAdd 8

end SubexponentialSAT.SubexpJetCellProgram

end OAI.Algorithms
end


