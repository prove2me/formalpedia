-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_ProgBuild
-- name    : MIPRE_Foundations_CL_ProgBuild
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:30.738512+00:00
-- url     : https://prove2.me/theorems/812f9468-31ca-4051-8e8b-f72e5619067f
-- title:
--   Definitions of ProgBuild: Building programs in polynomial time A program is data (`Prog.toData`), so placing variable subprograms in a fixed…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.ProgBuild` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Building programs in polynomial time. A program is data (`Prog.toData`), so placing variable subprograms in a fixed context is a polynomial-time function of the subprograms: `letF` for `let e in b`, `elimF` for `elim i n c`, and from them `routeOneCallF` for a router with one call to a variable program. These are how a verifier's programs are computed from its input programs when the input programs enter as code rather than as data (the detyping compiler's).
--
--   **Definitions** (4): `MIPRE.CL.ProgBuild.callWithContextF` (`p ↦ callWithContext p post`, in polynomial time.); `MIPRE.CL.ProgBuild.elimF` (`c ↦ elim i n c`, in polynomial time.); `MIPRE.CL.ProgBuild.letF` (`(e, b) ↦ let e in b`, in polynomial time.); `MIPRE.CL.ProgBuild.routeOneCallF` (`p ↦ routeOneCall route p post`, in polynomial time.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `callWithContextF_apply`, `elimF_apply`, `letF_apply`, `routeOneCallF_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.ProgBuild` (`MIPRE/Foundations/CL/ProgBuild.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/ProgBuild.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProgBuild.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall

/-!
# Building programs in polynomial time

A program is data (`Prog.toData`), so placing variable subprograms in a fixed context is a
polynomial-time function of the subprograms: `letF` for `let e in b`, `elimF` for
`elim i n c`, and from them `routeOneCallF` for a router with one call to a variable program.
These are how a verifier's programs are computed from its input programs when the input programs
enter as code rather than as data (the detyping compiler's).
-/

namespace MIPRE.CL.ProgBuild

open Cost Cost.PolyTimeFun Detyping.Program

/-- `(e, b) ↦ let e in b`, in polynomial time. -/
noncomputable def letF : PolyTimeFun (Prog × Prog) Prog :=
  PolyTimeFun.cast (ap₂ treePair (const (Data.ofNat 4)) (encoded : PolyTimeFun (Prog × Prog) Data))
    (fun p => Prog.let_ p.1 p.2) (fun _ => rfl)

@[simp] theorem letF_apply (e b : Prog) : letF (e, b) = Prog.let_ e b := rfl

/-- `c ↦ elim i n c`, in polynomial time. -/
noncomputable def elimF (i : ℕ) (n : Prog) : PolyTimeFun Prog Prog :=
  PolyTimeFun.cast (ap₂ treePair (const (Data.ofNat 3)) (ap₂ treePair (const (Data.ofNat i))
    (ap₂ treePair (const n.toData) (encoded : PolyTimeFun Prog Data))))
    (fun c => Prog.elim i n c) (fun _ => rfl)

@[simp] theorem elimF_apply (i : ℕ) (n c : Prog) : elimF i n c = Prog.elim i n c := rfl

/-- `p ↦ callWithContext p post`, in polynomial time. -/
noncomputable def callWithContextF (post : PolyTimeFun (Data × Data) Data) : PolyTimeFun Prog Prog :=
  letF.comp ((const Prog.fstProg).pair (letF.comp ((PolyTimeFun.id Prog).pair
    (const (Prog.let_ (.cons (Prog.callVar 2 Prog.sndProg) (.var 0)) post.code)))))

@[simp] theorem callWithContextF_apply (post : PolyTimeFun (Data × Data) Data) (p : Prog) :
    callWithContextF post p = Prog.callWithContext p post := rfl

/-- `p ↦ routeOneCall route p post`, in polynomial time. -/
noncomputable def routeOneCallF (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) : PolyTimeFun Prog Prog :=
  letF.comp ((const route.code).pair ((elimF 0 .nil).comp ((elimF 0 (.var 1)).comp
    (letF.comp ((const (.var 3)).pair (callWithContextF post))))))

@[simp] theorem routeOneCallF_apply (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (p : Prog) :
    routeOneCallF route post p = Prog.routeOneCall route p post := rfl

end MIPRE.CL.ProgBuild


