-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_ProductSamplerCost
-- name    : MIPRE_Foundations_CL_ProductSamplerCost
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:29:10.115628+00:00
-- url     : https://prove2.me/theorems/fab80a4c-54b2-4378-b24e-e50d675d46f4
-- title:
--   Definitions of ProductSamplerCost: The running time of the product sampler `CL.TypedSampler.prodDirect` runs the parameter routine of its direct half…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.ProductSamplerCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The running time of the product sampler. `CL.TypedSampler.prodDirect` runs the parameter routine of its direct half through the universal machine, then routes the query: at most one call to the typed half's program, again through the universal machine, on a query at most linearly larger than the typed query (`route_call_size`), and polynomial-time work on the parameters around it. So its running time is dominated, in the sense of `MIPRE.Pipeline.PDom`, as soon as the parameter routine's is and the typed half runs within a monomial coefficient at degree `e (K + 1)` (`prog_time`), on every…
--
--   **Definitions** (1): `MIPRE.CL.ProductSampler.stageBound` (The explicit bound on the routed stage: the router, one call through the universal machine to `A`'s program on a query of size at most…).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.ProductSamplerCost` (`MIPRE/Foundations/CL/ProductSamplerCost.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 56 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/ProductSamplerCost.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSamplerCost.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.LinearAlgebra.Basis.Defs
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
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
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
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Theorems.Thm_MIPRE_Cost_hardcode_time

/-!
# The running time of the product sampler

`CL.TypedSampler.prodDirect` runs the parameter routine of its direct half through the universal
machine, then routes the query: at most one call to the typed half's program, again through the
universal machine, on a query at most linearly larger than the typed query (`route_call_size`),
and polynomial-time work on the parameters around it. So its running time is dominated, in the
sense of `MIPRE.Pipeline.PDom`, as soon as the parameter routine's is and the typed half runs
within a monomial coefficient at degree `e (K + 1)` (`prog_time`), on every input, well formed
or not.
-/

namespace MIPRE.CL.ProductSampler

open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline

variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)

/-- The explicit bound on the routed stage: the router, one call through the universal machine to
`A`'s program on a query of size at most `esize n + 12 |q| + 4 ℓa + 20`, and the post-processing. -/
noncomputable def stageBound (ap : Prog) (ℓa n : ℕ) (xs qs BA k : ℕ) : ℕ :=
  let Rt := (route B D).timeBound.eval xs
  let tU := selfUniversal.bound.eval
    (esize ap + (esize n + 12 * qs + 4 * ℓa + 20) + BA * (esize n + 12 * qs + 4 * ℓa + 21) ^ k)
  4 * Rt + 3 * (esize ap + esize n + 12 * qs + 4 * ℓa + 21) + 2 * tU +
    post.timeBound.eval (Rt + tU + 1) + 22

end MIPRE.CL.ProductSampler


