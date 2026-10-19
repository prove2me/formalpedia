-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
-- name    : MIPRE_Foundations_CL_DetypingProgQueries
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:11.082321+00:00
-- url     : https://prove2.me/theorems/265af7b5-26d6-4cdb-89f3-f95079427b21
-- title:
--   Definitions of DetypingProgQueries: Bit-list query formulas for the numbered detyping sampler These identities connect the semantic CL construction to the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingProgQueries` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bit-list query formulas for the numbered detyping sampler. These identities connect the semantic CL construction to the executable router's graph-prefix and content-suffix operations. Prefix validity for forwarded content queries is derived from the original numbered prefix.
--
--   **Definitions** (1): `_private.MIPRE.Foundations.CL.DetypingProgQueries.0.MIPRE.CL.Detyping.indicatorVec`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `drop_graph_append`, `take_graph_append`, `toBits_indicator_equiv`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingProgQueries` (`MIPRE/Foundations/CL/DetypingProgQueries.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 13 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgQueries.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgQueries.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits

/-! # Bit-list query formulas for the numbered detyping sampler

These identities connect the semantic CL construction to the executable
router's graph-prefix and content-suffix operations. Prefix validity for
forwarded content queries is derived from the original numbered prefix.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

variable {T : Type*} [Fintype T] [DecidableEq T]

set_option linter.unusedSectionVars false

def indicatorVec {ι : Type*} [DecidableEq ι] (S : Finset ι) : ι → 𝔽₂ :=
  fun i => if i ∈ S then 1 else 0

theorem toBits_indicator_equiv {ι : Type*} [DecidableEq ι] {s : ℕ}
    (e : ι ≃ Fin s) (S : Finset ι) :
    toBits (push e.toEmbedding (indicatorVec S)) = indicatorBits (S.map e.toEmbedding) := by
  unfold toBits indicatorBits
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  have hp := push_apply e.toEmbedding (indicatorVec S) j
  change push e.toEmbedding (indicatorVec S) (e j) = _ at hp
  rw [hp]
  simp [indicatorVec]

theorem take_graph_append (g : Graph.Coord T → 𝔽₂) (v : Cost.BitStr) :
    (graphBits g ++ v).take (graphDim T) = graphBits g := by
  rw [← length_graphBits g, List.take_left]

theorem drop_graph_append (g : Graph.Coord T → 𝔽₂) (v : Cost.BitStr) :
    (graphBits g ++ v).drop (graphDim T) = v := by
  rw [← length_graphBits g, List.drop_left]

end MIPRE.CL.Detyping


