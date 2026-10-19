-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
-- name    : MIPRE_Foundations_LowDegree_BinaryConstants
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:10:41.294741+00:00
-- url     : https://prove2.me/theorems/b74ad054-7971-4dbd-8041-b24628359288
-- title:
--   Definitions of BinaryConstants: Fixed-width zero and one for binary polynomial quotients
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryConstants` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Fixed-width zero and one for binary polynomial quotients
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryPolynomial.oneBits`; `MIPRE.LowDegree.BinaryPolynomial.oneBitsProg`; `MIPRE.LowDegree.BinaryPolynomial.zeroBits` (Zero and one use the width of the supplied lower-coefficient vector.); `MIPRE.LowDegree.BinaryPolynomial.zeroBitsProg`.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `evalBits_zeroBits`, `length_oneBits`, `length_zeroBits`, `oneBitsProg_apply`, `zeroBitsProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryConstants` (`MIPRE/Foundations/LowDegree/BinaryConstants.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 9 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryConstants.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryConstants.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial

/-! # Fixed-width zero and one for binary polynomial quotients -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost

/-- Zero and one use the width of the supplied lower-coefficient vector. -/
def zeroBits (p : BitStr) : BitStr := List.replicate p.length false

def oneBits : BitStr → BitStr
  | [] => []
  | _ :: p => true :: List.replicate p.length false

@[simp] theorem length_zeroBits (p : BitStr) : (zeroBits p).length = p.length := by
  simp [zeroBits]

@[simp] theorem length_oneBits (p : BitStr) : (oneBits p).length = p.length := by
  cases p <;> simp [oneBits]

variable {R : Type*} [CommRing R]

@[simp] theorem evalBits_zeroBits (z : R) (p : BitStr) : evalBits z (zeroBits p) = 0 := by
  simp [zeroBits]

open Cost.PolyTimeFun

noncomputable def zeroBitsProg : PolyTimeFun BitStr BitStr :=
  congr (replicate.comp (length.pair (const false))) zeroBits (by intro p; simp [zeroBits])

noncomputable def oneBitsProg : PolyTimeFun BitStr BitStr :=
  congr ((casesList (const [])
    (cons (const true) (zeroBitsProg.comp (snd.comp snd)))).comp
      ((const ()).pair (PolyTimeFun.id _))) oneBits (by intro p; cases p <;> rfl)

@[simp] theorem zeroBitsProg_apply (p : BitStr) : zeroBitsProg p = zeroBits p := rfl
@[simp] theorem oneBitsProg_apply (p : BitStr) : oneBitsProg p = oneBits p := rfl

end MIPRE.LowDegree.BinaryPolynomial


