-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
-- name    : MIPRE_Foundations_CL_DetypingProgCost
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:21.082061+00:00
-- url     : https://prove2.me/theorems/fb405783-8cf3-48d9-a447-4be9d8895634
-- title:
--   Definitions of DetypingProgCost: Polynomial runtime transfer for the detyping sampler The bound follows the actual one-call program: preprocessing…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingProgCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Polynomial runtime transfer for the detyping sampler. The bound follows the actual one-call program: preprocessing bounds the size of the forwarded query and continuation, the original sampler bounds the forwarded run, and postprocessing reads their combined output. Constants in the graph table are fixed; no uniform graph-compilation bound is asserted.
--
--   **Definitions** (5): `MIPRE.CL.Detyping.samplerCoefficient` (The coefficient obtained from the explicit runtime polynomial.); `MIPRE.CL.Detyping.samplerCost` (The explicit detyping runtime polynomial in the raw query's size.); `MIPRE.CL.Detyping.samplerDegree` (The common query degree for every index and every original coefficient.); `MIPRE.Cost.Prog.routeCost` (The closed polynomial expression bounding a router with one call to a sampler whose indexed coefficient and input degree are `B` and `k`.); `MIPRE.Cost.Prog.routeDegree` (A common query degree, independent of the index and runtime coefficient.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingProgCost` (`MIPRE/Foundations/CL/DetypingProgCost.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 37 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgCost.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgCost.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
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
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler

/-! # Polynomial runtime transfer for the detyping sampler

The bound follows the actual one-call program: preprocessing bounds the size
of the forwarded query and continuation, the original sampler bounds the
forwarded run, and postprocessing reads their combined output. Constants in
the graph table are fixed; no uniform graph-compilation bound is asserted.
-/

namespace MIPRE.Cost

open PolyTimeFun Polynomial

namespace Prog

/-- The closed polynomial expression bounding a router with one call to a
sampler whose indexed coefficient and input degree are `B` and `k`. -/
noncomputable def routeCost (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (B k : ℕ) : Polynomial ℕ :=
  let R := route.timeBound
  let F := C B * (R + 1) ^ k
  C 10 * (R + F + post.timeBound.comp (R + F + 1) + C 10)

/-- A common query degree, independent of the index and runtime coefficient. -/
noncomputable def routeDegree (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (k : ℕ) : ℕ :=
  route.timeBound.natDegree * (k + 1) * (post.timeBound.natDegree + 1)

end Prog
end MIPRE.Cost

namespace MIPRE.CL.Detyping

open Cost Polynomial

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)

/-- The explicit detyping runtime polynomial in the raw query's size. -/
noncomputable def samplerCost (n B k : ℕ) : Polynomial ℕ :=
  (Prog.routeCost (Program.route E) (Program.post (graphDim T)) B k).comp
    (X + C (esize n + 1))

/-- The common query degree for every index and every original coefficient. -/
noncomputable def samplerDegree (k : ℕ) : ℕ :=
  Prog.routeDegree (Program.route E) (Program.post (graphDim T)) k

/-- The coefficient obtained from the explicit runtime polynomial. -/
noncomputable def samplerCoefficient (n B k : ℕ) : ℕ :=
  let Q := samplerCost E n B k
  ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i

end MIPRE.CL.Detyping


