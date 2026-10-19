-- Prove2me | Definitions.Def_MIPRE_Foundations_Sign
-- name    : MIPRE_Foundations_Sign
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:08.318356+00:00
-- url     : https://prove2.me/theorems/6f54b782-60c9-4e62-b304-b54af9eb8277
-- title:
--   Definitions of Sign: The sign of a bit `sgn x = (-1)^x` for `x : ZMod 2`, as a complex number
-- statement:
--   The definitions of the module `MIPRE.Foundations.Sign` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The sign of a bit. `sgn x = (-1)^x` for `x : ZMod 2`, as a complex number. It is the character group of `𝔽₂` written multiplicatively, and it is what every `±1`-observable in this development is built from: the observable of a two-outcome measurement, the phase of a Weyl operator in characteristic two, and the sign a Magic Square constraint carries. Characteristic two is why this is a *sign* and not a root of unity. Over `𝔽_p` the generalized Pauli operators carry phases `e^{2πi/p}`; this project's fields are always of admissible size `q = 2^k`, so `p = 2` and every phase is real. That…
--
--   **Definitions** (1): `MIPRE.sgn` (`(-1)^x` for a bit `x`.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `sgn_one`, `sgn_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Sign` (`MIPRE/Foundations/Sign.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Sign.lean; blueprint def:generalized-pauli

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sign.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-!
# The sign of a bit

`sgn x = (-1)^x` for `x : ZMod 2`, as a complex number. It is the character group of `𝔽₂` written
multiplicatively, and it is what every `±1`-observable in this development is built from: the
observable of a two-outcome measurement, the phase of a Weyl operator in characteristic two, and
the sign a Magic Square constraint carries.

Characteristic two is why this is a *sign* and not a root of unity. Over `𝔽_p` the generalized
Pauli operators carry phases `e^{2πi/p}`; this project's fields are always of admissible size
`q = 2^k`, so `p = 2` and every phase is real. That collapse is worth having in one place.
-/

noncomputable section

namespace MIPRE

/-- `(-1)^x` for a bit `x`. -/
def sgn (x : ZMod 2) : ℂ := if x.val = 1 then -1 else 1

@[simp] theorem sgn_zero : sgn 0 = 1 := by rw [sgn]; norm_num

@[simp] theorem sgn_one : sgn 1 = -1 := by
  rw [sgn, show ZMod.val (1 : ZMod 2) = 1 from rfl, if_pos rfl]

end MIPRE

end


