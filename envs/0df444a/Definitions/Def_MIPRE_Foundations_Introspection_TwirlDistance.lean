-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
-- name    : MIPRE_Foundations_Introspection_TwirlDistance
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:40.280654+00:00
-- url     : https://prove2.me/theorems/3bf77560-56d7-4f1d-8cc0-88dcf3a32b9c
-- title:
--   Definitions of TwirlDistance: Approximate commutation controls twirling in the state-dependent norm This is the paper's `lem:mixing-U`, with constant…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.TwirlDistance` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Approximate commutation controls twirling in the state-dependent norm. This is the paper's `lem:mixing-U`, with constant one and all outcome sums explicit. The state need not be invariant under any of the unitaries.
--
--   **Definitions** (1): `MIPRE.Introspection.unitaryTwirl` (Twirling against a finitely supported probability distribution.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.TwirlDistance` (`MIPRE/Foundations/Introspection/TwirlDistance.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 7 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TwirlDistance.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TwirlDistance.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B

/-! # Approximate commutation controls twirling in the state-dependent norm

This is the paper's `lem:mixing-U`, with constant one and all outcome sums explicit.
The state need not be invariant under any of the unitaries.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix

variable {dA dB I : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I]

/-- Twirling against a finitely supported probability distribution. -/
def unitaryTwirl (μ : I → ℝ) (U : I → Matrix dA dA ℂ) (M : Matrix dA dA ℂ) :
    Matrix dA dA ℂ := ∑ u, (μ u : ℂ) • (U u * M * (U u)ᴴ)

end MIPRE.Introspection

end


