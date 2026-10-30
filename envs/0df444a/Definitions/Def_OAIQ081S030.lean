-- Prove2me | Definitions.Def_OAIQ081S030
-- name    : OAIQ081S030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:29:09.703512+00:00
-- url     : https://prove2.me/theorems/c10b7921-a951-47e0-938b-603b2e183e3a
-- title:
--   Definitions bundle OAIQ081S030 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 108 declarations of OpenAI's Lean: 75 definitions, 1 inductive type or structure, 2 instances and 30 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.entropyCutoff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.hashCalls`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.jetNumerator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.jetOrder`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.measuredParameterInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.nativeEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.threshold`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.Hash.polynomialBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashInputs.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.Ports.hash`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.reverseCoefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.tag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.atom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.pairBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.pairLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.programCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Arithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.incidenceEntries`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalFetchBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.convolution`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.finishBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insertBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onMiss`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.updatedBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.peek`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index.Kept`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index.origin`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.Entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.mapped` and 36 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CostAssemblyFinal`, `SubexponentialSAT_SqrtLog_CostAssemblyProducedGuards`, `SubexponentialSAT_SqrtLog_CostAssemblySearch`, `SubexponentialSAT_SqrtLog_CostAssemblySupport`, `SubexponentialSAT_SqrtLog_CostAssemblyUniform`, `SubexponentialSAT_SqrtLog_EarlyThreshold`, `SubexponentialSAT_SqrtLog_ExecutionHashBounds`, `SubexponentialSAT_SqrtLog_ExecutionHashInputs`, `SubexponentialSAT_SqrtLog_ExecutionHashParameters`, `SubexponentialSAT_SqrtLog_HashCircuitProgramConstant`, `SubexponentialSAT_SqrtLog_HashCircuitProgramControl`, `SubexponentialSAT_SqrtLog_HashCircuitProgramDecode`, `SubexponentialSAT_SqrtLog_HashCircuitProgramIncidence`, `SubexponentialSAT_SqrtLog_HashCircuitProgramLookup`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBasic`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryFinish`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryInsert`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_SparseCodeParameters`, `SubexponentialSAT_SqrtLog_SquarefreeBasic`, `SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding`, `SubexponentialSAT_SqrtLog_SquarefreeJet`, `SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram`, `SubexponentialSAT_SqrtLog_SquarefreeProgramFrame`, `SubexponentialSAT_SqrtLog_SquarefreeProgramLookup`, `SubexponentialSAT_SqrtLog_SquarefreeProgramPrepend`, `SubexponentialSAT_SqrtLog_SquarefreeProgramScan`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_SqrtLog_SquarefreeSparseOps`, `SubexponentialSAT_SqrtLog_SquarefreeSparseProduct`, `SubexponentialSAT_SqrtLog_SquarefreeSparseRing`, `SubexponentialSAT_SubexpNodeCost`, `SubexponentialSAT_SubexpRecordScan`, `SubexponentialSAT_Subexp_PairScoreBounds`, `SubexponentialSAT_Subexp_SelectorProgram`, `SubexponentialSAT_Truncation`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S004`, `OAIQ081S005`, `OAIQ081S006`, `OAIQ081S007` and `OAIQ081S008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S062`, `OAIQ081S063` and `OAIQ081S064`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_forwardHighMask_guards`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_hashCalls_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_measured_guards`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_nativeEnvelope_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_sparse_parameter_bounds` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_support_bound`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_hashCalls_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_nativeEnvelope_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_sparse_parameter_bounds` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_support_bound`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S004
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S008

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse squarefree polynomials. The index monoid multiplies by support union,
so the coefficient algebra imposes X_v^2 = X_v without enumerating all supports. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

variable {V R : Type*}

instance instCommMonoidSupportOfDecidableEq [DecidableEq V] : CommMonoid (Support V) where
  one := ⟨∅⟩
  mul a b := ⟨a.vars ∪ b.vars⟩
  mul_assoc a b c := Support.ext (Finset.union_assoc _ _ _)
  one_mul a := Support.ext (Finset.empty_union _)
  mul_one a := Support.ext (Finset.union_empty _)
  mul_comm a b := Support.ext (Finset.union_comm _ _)

@[simp] theorem vars_one [DecidableEq V] : (1 : Support V).vars = ∅ := rfl
@[simp] theorem vars_mul [DecidableEq V] (a b : Support V) :
    (a * b).vars = a.vars ∪ b.vars := rfl

@[simp] theorem support_mul_eq [DecidableEq V] (a b : Support V) (s : Finset V) :
    a * b = Support.mk s ↔ a.vars ∪ b.vars = s := by
  constructor
  · intro h; exact congrArg Support.vars h
  · exact Support.ext

abbrev Poly (V R : Type*) [Semiring R] := MonoidAlgebra R (Support V)

noncomputable section

variable [DecidableEq V] [CommSemiring R]

def monomial (s : Finset V) (c : R) : Poly V R := MonoidAlgebra.single ⟨s⟩ c

def coeff (s : Finset V) (f : Poly V R) : R := f.coeff ⟨s⟩

def scalar : R →+* Poly V R := MonoidAlgebra.singleOneRingHom

@[simp] theorem coeff_scalar_mul (s : Finset V) (c : R) (f : Poly V R) :
    coeff s (scalar c * f) = c * coeff s f := by
  exact MonoidAlgebra.coeff_single_one_mul f c (Support.mk s)

@[simp] theorem coeff_zero (s : Finset V) : coeff s (0 : Poly V R) = 0 := rfl
@[simp] theorem coeff_add (s : Finset V) (f g : Poly V R) :
    coeff s (f + g) = coeff s f + coeff s g := rfl
@[simp] theorem coeff_monomial (s t : Finset V) (c : R) :
    coeff s (monomial t c) = if t = s then c else 0 := by
  by_cases h : t = s
  · subst s
    simp [coeff, monomial]
  · have hs : Support.mk t ≠ Support.mk s := fun e => h (congrArg Support.vars e)
    simp [coeff, monomial, h, hs]

@[simp] theorem monomial_mul (s t : Finset V) (a b : R) :
    monomial s a * monomial t b = monomial (s ∪ t) (a * b) := by
  change MonoidAlgebra.single (Support.mk s) a * MonoidAlgebra.single (Support.mk t) b =
    MonoidAlgebra.single (Support.mk (s ∪ t)) (a * b)
  rw [MonoidAlgebra.single_mul_single]
  congr

theorem mul_weight_of_mem (x : V → R) (hx : ∀ v, x v * x v = x v)
    (s : Finset V) {v : V} (hv : v ∈ s) : x v * weight x s = weight x s := by
  rw [weight, ← Finset.insert_erase hv, Finset.prod_insert (Finset.notMem_erase _ _)]
  rw [← mul_assoc, hx]

theorem weight_union (x : V → R) (hx : ∀ v, x v * x v = x v)
    (s t : Finset V) : weight x (s ∪ t) = weight x s * weight x t := by
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | @insert v s hv ih =>
      by_cases hvt : v ∈ t
      · rw [Finset.insert_union, Finset.insert_eq_of_mem (Finset.mem_union_right _ hvt)]
        have hins : weight x (insert v s) = x v * weight x s := by
          simp [weight, hv]
        rw [hins]
        rw [ih, mul_assoc, mul_left_comm (x v), mul_weight_of_mem x hx t hvt]
      · rw [Finset.insert_union]
        rw [weight, Finset.prod_insert (by simp [hv, hvt])]
        change x v * weight x (s ∪ t) = weight x (insert v s) * weight x t
        have hins : weight x (insert v s) = x v * weight x s := by
          simp [weight, hv]
        rw [ih, hins, mul_assoc]

def weightHom (x : V → R) (hx : ∀ v, x v * x v = x v) : Support V →* R where
  toFun s := weight x s.vars
  map_one' := by simp [weight]
  map_mul' a b := weight_union x hx a.vars b.vars

/-- Evaluation at idempotent values is a ring/semiring homomorphism. -/
def evalHom (x : V → R) (hx : ∀ v, x v * x v = x v) : Poly V R →+* R :=
  MonoidAlgebra.liftNCRingHom (RingHom.id R) (weightHom x hx)
    (fun a b => Commute.all a ((weightHom x hx) b))

@[simp] theorem eval_monomial (x : V → R) (hx : ∀ v, x v * x v = x v)
    (s : Finset V) (c : R) : evalHom x hx (monomial s c) = c * weight x s := by
  exact MonoidAlgebra.liftNC_single _ _ _ _

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Truncation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Canonical truncation before substitution

Polynomials are represented with U outermost, Z in the middle, and the X variables
innermost.  Truncation is an operation on canonical polynomial representatives;
we never assert that U = 1 defines a map out of the truncated quotient.
-/

namespace SubexponentialSAT.Truncation

noncomputable section

open scoped BigOperators

variable {R ι : Type*} [CommSemiring R]

@[simp] theorem coeff_trunc {A : Type*} [Semiring A]
    (n j : ℕ) (P : Polynomial A) :
    (trunc n P).coeff j = if j < n then P.coeff j else 0 := by
  classical
  simp [trunc, Polynomial.coeff, Finsupp.filter_apply]

@[simp] theorem trunc_zero {A : Type*} [Semiring A] (n : ℕ) :
    trunc n (0 : Polynomial A) = 0 := by
  ext j
  simp

@[simp] theorem trunc_add {A : Type*} [Semiring A]
    (n : ℕ) (P Q : Polynomial A) :
    trunc n (P + Q) = trunc n P + trunc n Q := by
  ext j
  by_cases h : j < n <;> simp [h]

def truncAddHom {A : Type*} [Semiring A] (n : ℕ) :
    Polynomial A →+ Polynomial A where
  toFun := trunc n
  map_zero' := trunc_zero n
  map_add' := trunc_add n

/-- Lift a coefficient reduction and a monomial cutoff together. -/
def clipAddHom {A : Type*} [Semiring A] (n : ℕ) (f : A →+ A) :
    Polynomial A →+ Polynomial A :=
  (mapCoeffs f).comp (truncAddHom n)

@[simp] theorem coeff_clipAddHom {A : Type*} [Semiring A]
    (n : ℕ) (f : A →+ A) (P : Polynomial A) (j : ℕ) :
    (clipAddHom n f P).coeff j = if j < n then f (P.coeff j) else 0 := by
  change f ((trunc n P).coeff j) = _
  rw [coeff_trunc]
  split_ifs <;> simp

end

end SubexponentialSAT.Truncation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeJet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! U is the outer polynomial variable, Z the inner one. Support cardinality
is charged only to Z degree; no formal X support is charged to U. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

noncomputable section

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

abbrev ZJet (V R : Type*) [DecidableEq V] [Semiring R] := Polynomial (Poly V R)
abbrev Jet (V R : Type*) [DecidableEq V] [Semiring R] := Polynomial (ZJet V R)

/-- Canonical finite U and Z truncation. No enumeration of X supports occurs. -/
def canonical (t J : ℕ) : Jet V R →+ Jet V R :=
  Truncation.clipAddHom t (Truncation.truncAddHom J)

@[simp] theorem coeff_canonical (t J u j : ℕ) (f : Jet V R) :
    ((canonical t J f).coeff u).coeff j =
      if u < t ∧ j < J then (f.coeff u).coeff j else 0 := by
  by_cases hu : u < t <;> by_cases hj : j < J <;>
    simp [canonical, Truncation.coeff_clipAddHom, Truncation.truncAddHom, hu, hj]

def evalJet (x : V → R) (hx : ∀ v, x v * x v = x v) :
    Jet V R →+* Polynomial (Polynomial R) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (evalHom x hx))

@[simp] theorem coeff_evalJet (x : V → R) (hx : ∀ v, x v * x v = x v)
    (f : Jet V R) (u j : ℕ) :
    (((evalJet x hx) f).coeff u).coeff j = evalHom x hx ((f.coeff u).coeff j) := by
  simp [evalJet]

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Index

variable {V : Type*} [DecidableEq V]

def Kept (t J : ℕ) (a : Index V) : Prop := a.u < t ∧ a.z < J
instance instDecidableKept (t J : ℕ) (a : Index V) : Decidable (a.Kept t J) := inferInstanceAs (Decidable (_ ∧ _))

end Index

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

noncomputable def atom (a : Index V) (c : R) : Jet V R :=
  Polynomial.monomial a.u (Polynomial.monomial a.z (monomial a.vars c))

@[simp] theorem atom_zero (a : Index V) : atom a (0 : R) = 0 := by
  simp [atom, monomial]

noncomputable abbrev denote (l : Data (Index V) R) : Jet V R := decode atom l

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

namespace Index

variable {V : Type*} [DecidableEq V]

def origin : Index V := ⟨0, 0, ∅⟩

@[simp] theorem origin_join (a : Index V) : origin.join a = a := by
  cases a; simp [origin, join]

end Index

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

def zero : Data (Index V) R := []

def scale (c : R) (l : Data (Index V) R) : Data (Index V) R :=
  l.map (fun a => (a.1, c * a.2))

@[simp] theorem denote_zero : denote (zero : Data (Index V) R) = 0 := rfl

@[simp] theorem atom_origin_one : atom (Index.origin : Index V) (1 : R) = 1 := by
  change Polynomial.monomial 0 (Polynomial.monomial 0 (1 : Poly V R)) = 1
  simp

omit [DecidableEq V] in
@[simp] theorem scale_length (c : R) (l : Data (Index V) R) : (scale c l).length = l.length :=
  List.length_map _

omit [DecidableEq V] in
@[simp] theorem keys_scale (c : R) (l : Data (Index V) R) : keys (scale c l) = keys l := by
  simp [keys, scale, List.map_map, Function.comp_def]

end Sparse

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommRing R]

def neg (l : Data (Index V) R) : Data (Index V) R := l.map (fun a => (a.1, -a.2))

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblySupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact squarefree support entropy at the square-root-log scale.  The
hypothesis on J is a numerical jet-order bound, not a support-count oracle. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology BigOperators
open Asymptotic

noncomputable def entropyCutoff (n : ℕ) (C : ℝ) : ℝ :=
  C * n * w n / Real.sqrt (L n : ℝ)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblySearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- All failed candidates and all marked-clause counts, plus the final count. -/
def hashCalls (n m P : ℕ) : ℕ :=
  2*(3*m)^P*HashSelect.loopCap n m*m+1

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

def distanceDenom (m B : ℕ) : ℕ := 20000 * B ^ 2 * logSize m ^ 2

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One closed cost expression with actual jet order, hash candidate count,
high-incidence branch count, and joint-signature/head enumeration. The two
remaining algorithmic interfaces are setup work and ordinary primitive work. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

def jetNumerator (n : ℕ) (p : Resources) : ℕ :=
  2*p.factors+3*(LeafParametersProgram.precision n p.clauses-1)+1

def jetOrder (k n : ℕ) (p : Resources) : ℕ :=
  k*layoutCutoff p.residual p.localOccurrence*jetNumerator n p/layoutQ p.residual+1

def assembledWork (k n : ℕ) (p : Resources) : ℕ :=
  sparseWork n (jetOrder k n p) p.setup
    (hashCalls n p.clauses (SparseCode.distanceDenom p.clauses p.initialOccurrence))
    (2^p.branchVars) (enumerationWork p.labelBase p.labelRows p.heads p.headSize)
    p.bits p.ordinary

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyProducedGuards
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Instantiate the uniform guard theorem with the actual measured scope
statistics.  Only the retained-half and scope-size estimates remain as
upstream obligations; positivity and neutral coverage are derived here. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafStatisticsProgram LeafParametersProgram

def measuredParameterInput (scopes : List (List ℕ)) (mask : List Bool)
    (clauses width : ℕ) : Input :=
  { ambient := mask.length
    freeCount := (measured scopes mask).free
    clauses := clauses
    width := width
    factors := scopes.length + (measured scopes mask).uncovered
    occurrence := (measured scopes mask).occurrence
    arity := measuredArity scopes mask
    incidences := (measured scopes mask).incidences }

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyUniform
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform bounds over every input at a fixed size.  The cutoff depends only
on fixed numerical exponents, never on a chosen sequence of formulas. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly
open Filter
open scoped Topology
open Asymptotic

/-- Explicit closure for native algorithms that are polynomial in the
assembled counter.  In particular quadratic bucket grouping pays for its
second factor of `2^headSize` here, never inside a polynomial in n. -/
def nativeEnvelope (k n power ordinaryPower : ℕ) (p : Resources) : ℕ :=
  (n+1)^ordinaryPower*(assembledWork k n p+1)^power

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_EarlyThreshold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid, fixed native producer of the early high-incidence threshold.
The source is the original ambient count in bank slot 0.  It is never replaced
by the residual count or by the later block-size parameter. -/

namespace SubexponentialSAT.SqrtLog.EarlyThreshold

open BitProgram StructuredCalls BinaryArithmetic
open LeafParametersProgram.Bank LeafParametersProgram.Circuit


def threshold (ambient : ℕ) : ℕ := Nat.sqrt (Asymptotic.L ambient) + 1

end SubexponentialSAT.SqrtLog.EarlyThreshold

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionHashInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preparation of the selector's alphabet and its two unary loop
counters. Input ports0,5,6 hold binary alphabet size, tuple depth and round
count. Port9 is an arbitrary saved row stream; other ports start empty.
The arithmetic that computes these three binary values remains a separate
caller obligation. Their expansion is performed here, with its full cost. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashInputs

open BitProgram StructuredCalls

def budget (count depth rounds : List Bool) : ℕ :=
  HashAlphabet.budget (CounterPrograms.value count) count.length + 1 +
    (CounterConversions.coreBound depth + 1) + (CounterConversions.coreBound rounds + 1)

end SubexponentialSAT.SqrtLog.Execution.HashInputs

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionHashBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Output-sensitive numeric costs for the complete native hash controller.
The candidate-family term is quadratic in its actual number of records;
mass evaluation is still charged separately on every tested record. -/

namespace SubexponentialSAT.SqrtLog.Execution.Hash

open HashSelectProgram

def polynomialBudget (count depth rounds : List Bool) (B C cost : ℕ) : ℕ :=
  let A := CounterPrograms.value count
  let P := CounterPrograms.value depth
  let K := CounterPrograms.value rounds
  let w := count.length
  HashInputs.budget count depth rounds +
    400 * (P+1) * A^2 * (A^P)^2 * ((P+1)*w+1) + 15 +
    controllerBudget B C cost (1 + (2*(P*w)+2)*(A^P)) (A^P) K

end SubexponentialSAT.SqrtLog.Execution.Hash

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionHashParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the actual metadata arithmetic into a caller which also
holds the formula and ring context. Only binary n, m and B are supplied;
3m, the tuple depth and the number of hash rounds are computed by the fixed
parameter program. The empty-formula branch is handled by the leaf caller. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashParameters

open BitProgram StructuredCalls

def Ports.hash {R S : ℕ} (p : Ports R S) : Hash.Ports R S where
  register := p.register ∘ HashParametersProgram.ABI.selectorRegisters
  stack := p.stack ∘ HashParametersProgram.ABI.selectorStacks
  register_injective := p.register_injective.comp (Fin.castAdd_injective _ _)
  stack_injective := p.stack_injective.comp (Fin.castAdd_injective _ _)

end SubexponentialSAT.SqrtLog.Execution.HashParameters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

def encodeIndex {n : ℕ} (a : Index (Fin n)) : List Bool :=
  Encoding.encodeNat a.u ++ Encoding.encodeNat a.z ++ encodeMask a.vars

@[simp] theorem encodeIndex_length {n : ℕ} (a : Index (Fin n)) :
    (encodeIndex a).length = a.u + a.z + n + 2 := by
  simp [encodeIndex]
  omega

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame emitter. The source is a reversed payload. It is consumed
and the forward framed payload is prepended to the destination. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev frameBody : Cmd 3 2 :=
  .seq (.atom (.push 1 0)) (.seq (.atom (.push 1 2)) (.atom (.pop 0 0 1)))

abbrev frameLoop : Cmd 3 2 := .while 1 frameBody

abbrev frameEmit : Cmd 3 2 :=
  .seq (.atom (.set 2 false)) (.seq (.atom (.push 1 2))
    (.seq (.atom (.set 2 true)) (.seq (.atom (.pop 0 0 1)) frameLoop)))

def frameEmitProgram := compiled frameEmit 0 1

@[simp] theorem frameEmit_size : size frameEmit = 8 := rfl

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramPrepend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive emission of a key/coefficient record. Both source words
are reversed; all bits, framing tags and source cleanup are executed. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev prependRecord : Cmd 3 3 :=
  .seq (.call (ProgramLinking.liftProgram frameEmitProgram id payloadPorts))
    (.call (ProgramLinking.liftProgram frameEmitProgram id keyPorts))

def prependRecordProgram := compiled prependRecord 0 2

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRecordScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control selection of serialized coefficient records

The inner record body is `frame key ++ frame coefficient`. All execution
claims below are traces of fixed Boolean-register/stack instruction tables.
-/

namespace SubexponentialSAT.SubexpRecordScan

open BitProgram StructuredProgram StructuredCalls

def twoPorts (src dst : Fin 6) : Fin 2 → Fin 6 := ParserProgram.pair src dst

def skipRegs : Fin 3 → Fin 5 := ExecCNFRecords.ports 0 1 4
def payloadPorts : Fin 3 → Fin 6 := ExecCNFRecords.ports 0 5 4

end SubexponentialSAT.SubexpRecordScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct a cached sparse constant from a shape word and a forward flat
coefficient. Zero support bits, key delimiters, reversal, record framing and
cleanup all execute on the native bit machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev tag : Cmd 8 6 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 2 0))) (.base (.atom (.push 2 0))))

abbrev reverseCoefficient : Cmd 8 6 :=
  .call (StackRoutines.transferProgram (3 : Fin 6) 4 (0 : Fin 8) 1)

abbrev emit : Cmd 8 6 :=
  .call (ProgramLinking.liftProgram Squarefree.Program.prependRecordProgram emitRegisters emitStacks)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-code lookup with fallback for local read plans

The table is a raw sequence of framed key/payload pairs. The query and table
are runtime bit strings. The program reuses the verified key comparison and
record parsing routines, retaining the first matching payload.
-/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

def rawRecords (records : List (List Bool × List Bool)) : List Bool :=
  records.flatMap (fun p => Encoding.frame p.1 ++ Encoding.frame p.2)

abbrev atom (op : StructuredProgram.Atom 5 6) : Cmd 5 6 := .base (.atom op)
abbrev peek : Cmd 5 6 := atom (.peek 0 0 1)
abbrev continueOrStop : Cmd 5 6 := .ite 4 (atom (.set 1 false)) peek

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive dictionary lookup. Dictionary normalization guarantees
unique keys. All key and coefficient bits are scanned by the existing finite
record program; key width, coefficient width and dictionary length are runtime
data and do not affect the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

variable {K C : Type*} [DecidableEq K]

abbrev lookupRecords := SubexponentialSAT.Subexp.SelectorProgram.rawRecords

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Native literal parsing and hash-specific incidence lookup

A literal payload is `key ++ [positive]`; the existing record parser supplies
its reversal. The key selects a variable in a physically selected hash slice.
The fixed command pops the polarity, copies and scans the saved incidence
slice, returns its framed dictionary payload, and reclaims both scan and query.
There is no circuit-evaluation instruction and no scope truth table.
-/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

def literalFetchBudget (key : List Bool) (entries : List (List Bool × List Bool)) : ℕ :=
  9*(Squarefree.Program.lookupRecords entries).length + 2*key.length +
    Squarefree.Program.lookupBudget key entries + 15

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native conversion from the audited unary literal code `2*v+polarity` to
variable-key/polarity syntax. The source is a reversed parsed `encodeNat` record.
The loop consumes two unary marks per variable mark and records an odd tail as
positive polarity. Its instruction table is independent of the variable index. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

namespace Decode

abbrev atom (a : StructuredProgram.Atom 4 2) : Cmd 4 2 := .base (.atom a)

abbrev pairBody : Cmd 4 2 :=
  .seq (atom (.pop 0 0 1))
    (.ite 1 (.seq (atom (.push 1 2)) (atom (.pop 0 0 1))) (atom (.set 3 true)))
abbrev pairLoop : Cmd 4 2 := .while 1 pairBody

abbrev prepare : Cmd 4 2 :=
  .seq (atom (.pop 0 0 1))
    (.seq (atom (.set 2 true)) (.seq (atom (.set 3 false)) (atom (.pop 0 0 1))))

abbrev emit : Cmd 4 2 :=
  .seq (.call (StackRoutines.transferProgram (1 : Fin 2) 0 (0 : Fin 4) 1))
    (.seq (atom (.set 0 false)) (.seq (atom (.push 0 0)) (atom (.push 0 3))))

abbrev programCommand : Cmd 4 2 := .seq prepare (.seq pairLoop emit)
end Decode
end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed record-control code for sparse-hash evaluation. This module fixes
all parsing and traversal code. Arithmetic components below are finite native
commands, to be instantiated by the separate dictionary modules; no semantic
function is called by the machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev copy (src dst tmp : Fin 96) : Cmd 8 96 :=
  .call (StackRoutines.copyProgram src dst tmp (0 : Fin 8) 1)
abbrev transfer (src dst : Fin 96) : Cmd 8 96 :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 8) 1)

/-- Concrete fixed commands are supplied here, rather than semantic ring
operations. Their ABI is: complement61, product(67,61)→67 consuming61,
and scalar-weighted accumulation(65,67,68)→68 consuming65/67. -/
structure Arithmetic where
  oneMinus : Cmd 8 96
  multiply : Cmd 8 96
  scaleAdd : Cmd 8 96

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native lookup theorem specialized to actual hash-indexed incidence
payloads. Every occurrence of a variable uses the payload from the selected
hash slice; lookup correctness is discharged rather than an extra premise. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def incidenceEntries {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) : List (List Bool × List Bool) :=
  (List.finRange n).map fun v => (Encoding.encodeNat v.val,payload i v)

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- Ordinary schoolbook convolution, using no polynomial operations. -/
def convolution {R : Type*} [Semiring R] {n : ℕ}
    (a b : Fin n → R) (j : ℕ) : R :=
  ∑ i ∈ Finset.range (j + 1), entry a i * entry b (j - i)

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

def rawEntries : List ByteRecord → List Bool
  | [] => []
  | (key,payload) :: rest => Encoding.frame key ++ Encoding.frame payload ++ rawEntries rest

def erasedEntries (query : List Bool) (entries : List ByteRecord) : List ByteRecord :=
  entries.filter (fun a => decide (a.1 ≠ query))

def eraseBudget (query : List Bool) : List ByteRecord → ℕ
  | [] => 1
  | (key,payload) :: rest =>
      28 * key.length + 9 * query.length + 13 * payload.length + 53 + eraseBudget query rest

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical dictionary-insertion program. All dictionary/key/vector
lengths are input data. The complete semantic composition is proved separately;
this file defines the finite table and its paid stack primitives. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev copy (src dst tmp : Fin 27) : Cmd 8 27 :=
  .call (copyProgram src dst tmp (0 : Fin 8) 1)
abbrev transfer (src dst : Fin 27) : Cmd 8 27 :=
  .call (transferProgram src dst (0 : Fin 8) 1)
abbrev onMiss : Cmd 8 27 := copy 17 0 23

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def updatedBytes (entries : List (List Bool × List Bool)) (query coeff : List Bool) : List Bool :=
  Squarefree.Program.rawEntries ((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse)

def finishBudget (entries : List (List Bool × List Bool)) (query coeff remain : List Bool) : ℕ :=
  2 * remain.length + 7 * coeff.length + Squarefree.Program.eraseBudget query entries +
  4 * query.length + 9 * (updatedBytes entries query coeff).length + 31

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryInsert
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def insertBudget (entries : List (List Bool × List Bool)) (query result : List Bool) (branch : ℕ) : ℕ :=
  7 * (Squarefree.Program.rawEntries entries).length + Squarefree.Program.lookupBudget query entries +
  branch + finishBudget entries query result (Squarefree.Program.rawEntries entries) + 9

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev peek : Cmd 8 28 := .base (.atom (.peek 27 0 7))

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Closed bounds for the actual tuple generator and pair scorer

All costs below are the explicit bounds attached to proved executions of the
fixed programs.  The tuple recurrence is bounded from its actual list sizes;
no scalar-operation or callback-cost oracle is assumed.
-/

namespace SubexponentialSAT.Subexp.PairScoreBounds

open BitProgram

theorem cartesian_width (rows alphabet : List (List Bool)) (L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    ∀ row ∈ TupleProgram.cartesianOutput rows alphabet, row.length ≤ L + W := by
  intro row hrow
  simp only [TupleProgram.cartesianOutput, List.mem_reverse, List.mem_flatMap,
    List.mem_map] at hrow
  obtain ⟨pref, hp, word, hw, rfl⟩ := hrow
  simpa only [List.length_append] using Nat.add_le_add (hr pref hp) (ha word hw)

end SubexponentialSAT.Subexp.PairScoreBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def stepBudget {n : ℕ} (a b : Index (Fin n)) (t J coeffLength : ℕ) : ℕ :=
  9*(encodeIndex b).length+10*coeffLength+7*(encodeIndex a).length+
    14*(encodeIndex (a.join b)).length+14*(a.u+b.u+a.z+b.z)+8*n+9*(t+J)+108

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Entry (n : ℕ) := Index (Fin n) × List Bool

abbrev mapped {n : ℕ} (a : Index (Fin n)) (t J : ℕ) : List (Entry n) → List (Entry n)
  | [] => []
  | (b,c) :: rest => if (a.join b).Kept t J then (a.join b,c) :: mapped a t J rest
      else mapped a t J rest

def budget {n : ℕ} (a : Index (Fin n)) (t J : ℕ) : List (Entry n) → ℕ
  | [] => 1
  | (b,c) :: rest => stepBudget a b t J c.length + 2 + budget a t J rest

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Negation preserves the sparse support and the canonical representation.
These lemmas extend the semiring interface without changing its dependencies. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

variable {V R : Type*} [DecidableEq V] [CommRing R]

omit [DecidableEq V] in
@[simp] theorem neg_length (l : Data (Index V) R) : (neg l).length = l.length :=
  List.length_map _

omit [DecidableEq V] in
@[simp] theorem keys_neg (l : Data (Index V) R) : keys (neg l) = keys l := by
  simp [keys, neg, List.map_map, Function.comp_def]

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def stepBudget (B d keyLength : ℕ) : ℕ :=
  RingScan.serviceMulBudget B d + 16*keyLength + 29*(d*B) + 7*d + 49

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # A polynomial instruction bound for the fixed four-coordinate node program -/

namespace SubexponentialSAT.SubexpNodeCost

open Subexp.TupleProgram

theorem payloadSize_cartesian (rows alphabet : List (List Bool)) :
    payloadSize (cartesianOutput rows alphabet) =
      alphabet.length * payloadSize rows + rows.length * payloadSize alphabet := by
  rw [cartesianOutput, payloadSize_reverse]
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.flatMap_cons, payloadSize_append, payloadSize_prefix,
        ih, payloadSize_cons, List.length_cons]
      ring

theorem budget_affine (xs : List (List Bool)) (a b : ℕ) :
    RecordPrograms.budget (fun x => a * x.length + b) xs =
      (a + 6) * payloadSize xs + (b + 7) * xs.length := by
  induction xs with
  | nil => simp [RecordPrograms.budget]
  | cons x xs ih =>
      simp only [RecordPrograms.budget, ih, payloadSize_cons, List.length_cons]
      ring

end SubexponentialSAT.SubexpNodeCost

end OAI.Algorithms
end


