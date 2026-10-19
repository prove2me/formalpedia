-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingCompleteSupport
-- name    : MIPRE_Foundations_CL_DetypingCompleteSupport
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:44.544395+00:00
-- url     : https://prove2.me/theorems/25fa95da-1a90-40d9-84e7-1d33195e0bea
-- title:
--   Definitions of DetypingCompleteSupport: The common measurement rule and support of detyping Both players use one decoder of graph views
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingCompleteSupport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The common measurement rule and support of detyping. Both players use one decoder of graph views. It agrees with their own type selector on sampled questions, and otherwise selects a deterministic fallback. This is the player-independent rule in `types.tex`, `lem:detyping-verifiers`.
--
--   **Definitions** (2): `MIPRE.CL.Detyping.decodeQuestion` (Decode a full question, retaining its content register.); `MIPRE.CL.Detyping.decodeView` (The common decoder recognizes either player's full valid graph view.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingCompleteSupport` (`MIPRE/Foundations/CL/DetypingCompleteSupport.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 14 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingCompleteSupport.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingCompleteSupport.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame

/-! # The common measurement rule and support of detyping

Both players use one decoder of graph views. It agrees with their own type
selector on sampled questions, and otherwise selects a deterministic fallback.
This is the player-independent rule in `types.tex`, `lem:detyping-verifiers`.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- The common decoder recognizes either player's full valid graph view. -/
def decodeView (E : T → T → Prop) [DecidableRel E]
    (g : Graph.Coord T → ZMod 2) : Option (Bool × T) :=
  if h : ∃ u, g = view E false u then some (false, h.choose)
  else if h : ∃ u, g = view E true u then some (true, h.choose)
  else none

/-- Decode a full question, retaining its content register. -/
def decodeQuestion (E : T → T → Prop) [DecidableRel E] (q : Coord T ι → ZMod 2) :
    Option (Bool × Question T ι) :=
  (decodeView E (pull .inl q)).map fun wu => (wu.1, wu.2, pull .inr q)

end MIPRE.CL.Detyping


