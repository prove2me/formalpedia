-- Prove2me | Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
-- name    : MIPRE_Foundations_Pipeline_PowDomRun
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:37.475232+00:00
-- url     : https://prove2.me/theorems/c53b4001-4eaa-4847-91af-2f6343b23c58
-- title:
--   Definitions of PowDomRun: Runs within a powered monomial `PRuns W X K c m e p x r`: the program `p` runs from `x` to `r` at a cost below `(c (W +…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Pipeline.PowDomRun` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Runs within a powered monomial. `PRuns W X K c m e p x r`: the program `p` runs from `x` to `r` at a cost below `(c (W + 1)^m X^e)^{K + 1}` (`MIPRE.Pipeline.PDom`). The combinators follow the program constructors the pipeline's routines are built from — a polynomial-time function's code (`ptf`), sequencing (`seq`), a stage keeping a context (`stage`), hardcoding (`hardcode`), the universal machine (`univ`), and the two unary loops (`toUnary`, `pow`) — and each returns its constants from those of its arguments, so that a chain of them has constants uniform in `W`, `X`, `K` and the data. The…
--
--   **Definitions** (3): `MIPRE.Pipeline.PRuns` (`p` runs from `x` to `r` at a cost below `(c (W + 1)^m X^e)^{K + 1}`.); `MIPRE.Pipeline.powInit` (The initialization of `powProg`.); `MIPRE.Pipeline.toUnaryInit` (The initialization of `toUnaryProg`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Pipeline.PowDomRun` (`MIPRE/Foundations/Pipeline/PowDomRun.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 51 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/PowDomRun.lean; blueprint lem:ar-construction

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/PowDomRun.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Theorems.Thm_MIPRE_Cost_hardcode_time

/-!
# Runs within a powered monomial

`PRuns W X K c m e p x r`: the program `p` runs from `x` to `r` at a cost below
`(c (W + 1)^m X^e)^{K + 1}` (`MIPRE.Pipeline.PDom`). The combinators follow the program
constructors the pipeline's routines are built from — a polynomial-time function's code
(`ptf`), sequencing (`seq`), a stage keeping a context (`stage`), hardcoding (`hardcode`), the
universal machine (`univ`), and the two unary loops (`toUnary`, `pow`) — and each returns its
constants from those of its arguments, so that a chain of them has constants uniform in `W`, `X`,
`K` and the data.

The explicit running times of the unary loops are `toUnaryProg_time` and `powProg_time`: they are
polynomial in the *values* involved.
-/

namespace MIPRE.Pipeline

open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic

/-! ## The unary loops -/

/-- The initialization of `toUnaryProg`. -/
noncomputable abbrev toUnaryInit : PolyTimeFun Data Data :=
  encoded.comp ((readNat).pair (const ([] : Unary)))

/-- The initialization of `powProg`. -/
noncomputable abbrev powInit : PolyTimeFun Data Data :=
  encoded.comp ((readNat.comp treeTail).pair ((const (unary 1)).pair (readUnary.comp treeHead)))

/-! ## Sizes -/

/-! ## Runs within a powered monomial -/

/-- `p` runs from `x` to `r` at a cost below `(c (W + 1)^m X^e)^{K + 1}`. -/
def PRuns (W X K c m e : ℕ) (p : Prog) (x r : Data) : Prop :=
  ∃ t, PDom W X K c m e t ∧ p.Runs x r t

namespace PRuns

variable {W X K : ℕ}

end PRuns

end MIPRE.Pipeline


