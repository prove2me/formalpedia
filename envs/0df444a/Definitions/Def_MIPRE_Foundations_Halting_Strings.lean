-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Strings
-- name    : MIPRE_Foundations_Halting_Strings
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:53:48.096363+00:00
-- url     : https://prove2.me/theorems/e52ba689-950e-4be7-859b-a2dc3464a8d4
-- title:
--   The two distinguished strings: a verifier in class $A$ and one in class $B$
-- statement:
--   Obligation O1 of the halting reduction (blueprint `rem:compression-abstract`) asks for a string whose verifier lies in `classA n` at every level above a threshold and one whose verifier lies in `classB n`. This bundle defines them. Both are descriptions `descOf 0 𝒟` (`Halting/Instantiation.lean`): the compressed sampler at parameter $0$ together with a decider program of a few nodes.
--
--   `MIPRE.Halting.decNo` is the program `nil`, which returns $\mathtt{nil}$ on every input and so never returns `encode true`: the wrapped decider accepts nothing. `MIPRE.Halting.decYes` is the fixed-answer decider: on an input $(n, x, y, a, b)$ it returns `encode true` exactly when both answers $a$ and $b$ are the empty bit string; four `elim`s take the tuple apart and two more test the answers. `MIPRE.Halting.yNo = descOf 0 decNo` is the string of the class $B$ and `MIPRE.Halting.yYes = descOf 0 decYes` the string of the class $A$. The two embedded lemmas identify the verifiers these strings denote, for a gap-preserving compression $G$ and a universal machine $U$:
--   $$\mathrm{Vof}\;G\;U\;\mathrm{yNo} = \mathrm{ofSamplerDecider}\;U\;(G.\mathrm{sampler}\;0)\;\mathrm{decNo},\qquad \mathrm{Vof}\;G\;U\;\mathrm{yYes} = \mathrm{ofSamplerDecider}\;U\;(G.\mathrm{sampler}\;0)\;\mathrm{decYes}.$$
--
--   The membership statements `yYes_mem` and `yNo_mem` that `halting_reduction` applies are theorems of the module and not part of this bundle; the module docstring records their content: the verifier of `decNo` accepts no tuple, is synchronous at every index for want of an accepting tuple and has $\mathrm{val}^* = 0$ (`Verifier.inClassB_of_rejects_all`), and the verifier of `decYes` has a value-$1$ PCC strategy (`Verifier.inClassA_of_accepts_diagonal`). The $\lambda$-boundedness of both comes from the wrapper's time bound (`Halting/WrapperCost.lean`), each program halting at constant cost.
--
--   **Formalization Note**. The paper's halting case is a decider that accepts everything; in the synchronous framework that verifier is not synchronous at all, since equal questions with unequal answers must be rejected, so the fixed-answer form is what item 1 of `thm:halting` takes here. `decYes` is the literal term `elim 0 nil (elim 1 nil (elim 1 nil (elim 1 nil (elim 0 (elim 1 (const (encode true)) nil) nil))))`; its docstring, not a lemma of this bundle, states what it computes. The two identification lemmas are `@[simp]`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Strings.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Strings.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost

/-!
# The two distinguished strings

Obligation **O1** of the halting reduction (`Halting/Reduction.lean`, which applies `yYes_mem`
and `yNo_mem` directly): a string whose verifier lies in `classA n` at every level above a
threshold, and one whose verifier lies in `classB n`.

Both are descriptions `descOf 0 𝒟` with the compressed sampler at parameter `0` and a decider
program of three or four nodes:

* `decNo` is the program `nil`. Its result is `nil`, never `encode true`, so the wrapped
  decider accepts nothing, the verifier is synchronous at every index for want of an accepting
  tuple, and `val* = 0` (`Verifier.inClassB_of_rejects_all`).
* `decYes` takes the input `(n, x, y, a, b)` apart and returns `encode true` exactly when both
  answers are the empty string. The paper's halting case is a decider that accepts
  *everything*; in the synchronous framework that verifier is not synchronous at all — equal
  questions with unequal answers must be rejected — so the fixed-answer form is what item 1 of
  `thm:halting` takes here (`Verifier.inClassA_of_accepts_diagonal`, the paper's trivial
  strategy).

`λ`-boundedness of both comes from `Verifier.ofSamplerDecider_isBounded`, whose three
hypotheses are fields of `MIPRE.GapCompression` for the sampler and immediate for these two
programs, each of which halts at constant cost.
-/

namespace MIPRE.Halting

open Cost

/-! ## The two decider programs -/

/-- **The rejecting decider**: the program `nil`, which returns `nil` on every input. -/
def decNo : Prog := .nil

/-- **The fixed-answer decider**: on `(n, x, y, a, b)` it returns `encode true` exactly when
`a` and `b` are both the empty bit string. Four `elim`s take the tuple apart and two more test
the answers. -/
def decYes : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil
    (.elim 0 (.elim 1 (.const (encode true)) .nil) .nil))))

/-! ## The fixed-answer decider -/

/-! ## The compressed sampler -/

variable (G : GapCompression) (U : UniversalMachine)

/-! ## The two strings -/

/-- **The string of the class `B`**: parameter `0`, decider `nil`. -/
def yNo : BitStr := descOf 0 decNo

/-- **The string of the class `A`**: parameter `0`, the fixed-answer decider. -/
def yYes : BitStr := descOf 0 decYes

@[simp] theorem Vof_yNo : Vof G U yNo = Verifier.ofSamplerDecider U (G.sampler 0) decNo := by
  simp [Vof, yNo, Verifier.ofSamplerDecider]

@[simp] theorem Vof_yYes : Vof G U yYes = Verifier.ofSamplerDecider U (G.sampler 0) decYes := by
  simp [Vof, yYes, Verifier.ofSamplerDecider]

end MIPRE.Halting


