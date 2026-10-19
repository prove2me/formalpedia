-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
-- name    : MIPRE_Foundations_CL_DetypingProgCall
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:58:03.343798+00:00
-- url     : https://prove2.me/theorems/7d850d6d-b603-4c0f-87c0-d320c81fc44a
-- title:
--   Definitions of DetypingProgCall: A total query router with at most one sampler call The preprocessing program either supplies a direct result, or an…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingProgCall` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A total query router with at most one sampler call. The preprocessing program either supplies a direct result, or an argument and continuation context. Only the latter branch calls the supplied sampler. The postprocessor is total on raw data, so malformed inputs preserve termination whenever routing preserves the sampler index.
--
--   **Definitions** (2): `MIPRE.Cost.Prog.callWithContext`; `MIPRE.Cost.Prog.routeOneCall`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingProgCall` (`MIPRE/Foundations/CL/DetypingProgCall.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 18 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgCall.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgCall.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite

/-! # A total query router with at most one sampler call

The preprocessing program either supplies a direct result, or an argument and
continuation context. Only the latter branch calls the supplied sampler. The
postprocessor is total on raw data, so malformed inputs preserve termination
whenever routing preserves the sampler index.
-/

namespace MIPRE.Cost

open PolyTimeFun

namespace Prog

def callWithContext (p : Prog) (post : PolyTimeFun (Data × Data) Data) : Prog :=
  .let_ fstProg (.let_ p
    (.let_ (.cons (callVar 2 sndProg) (.var 0)) post.code))

def routeOneCall (route : PolyTimeFun Data (Bool × Data))
    (p : Prog) (post : PolyTimeFun (Data × Data) Data) : Prog :=
  .let_ route.code (.elim 0 .nil (.elim 0 (.var 1)
    (callVar 3 (callWithContext p post))))

end Prog
end MIPRE.Cost


