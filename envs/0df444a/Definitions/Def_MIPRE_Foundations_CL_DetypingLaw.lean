-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
-- name    : MIPRE_Foundations_CL_DetypingLaw
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:10:31.464322+00:00
-- url     : https://prove2.me/theorems/a56db40c-173c-474b-9a67-a91c36393b66
-- title:
--   Definitions of DetypingLaw: The joint law of detyped questions On an ordered edge the graph view depends only on the player's own type
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingLaw` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The joint law of detyped questions. On an ordered edge the graph view depends only on the player's own type. Conditioning on the valid-edge event gives the uniform ordered-edge law and one shared uniform content seed, exactly as in `types.tex`, `def:detyped-CL`.
--
--   **Definitions** (1): `MIPRE.CL.Detyping.view` (The fixed valid graph question of one type, independent of the neighboring type.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingLaw` (`MIPRE/Foundations/CL/DetypingLaw.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 7 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingLaw.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingLaw.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping

/-! # The joint law of detyped questions

On an ordered edge the graph view depends only on the player's own type.
Conditioning on the valid-edge event gives the uniform ordered-edge law and
one shared uniform content seed, exactly as in `types.tex`, `def:detyped-CL`.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- The fixed valid graph question of one type, independent of the neighboring type. -/
def view (E : T → T → Prop) [DecidableRel E] (w : Bool) (u : T) : Graph.Coord T → ZMod 2 :=
  fun p => if p.1 = w then Graph.encode E u p.2 else if p = (!w, (true, u)) then 1 else 0

end MIPRE.CL.Detyping


