-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AnswerRefinement
-- name    : MIPRE_Foundations_Introspection_AnswerRefinement
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:29.062004+00:00
-- url     : https://prove2.me/theorems/8c29f333-775c-40cf-b000-059d0a1d3529
-- title:
--   Definitions of AnswerRefinement: Deterministic graph refinement of measurement answers The old answer is retained verbatim while its deterministic…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AnswerRefinement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Deterministic graph refinement of measurement answers. The old answer is retained verbatim while its deterministic coordinate is recorded in a first component. Thus every old operator occurs exactly once; the construction preserves projectivity and all commutator sums exactly.
--
--   **Definitions** (2): `MIPRE.Introspection.graphRefinement` (Record a deterministic coordinate without forgetting the original answer.); `MIPRE.Introspection.graphRefinementPOVM` (The alphabet change is ordinary deterministic POVM postprocessing.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AnswerRefinement` (`MIPRE/Foundations/Introspection/AnswerRefinement.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 24 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AnswerRefinement.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AnswerRefinement.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Theorems.Thm_MIPRE_POVM_map_map

/-! # Deterministic graph refinement of measurement answers

The old answer is retained verbatim while its deterministic coordinate is
recorded in a first component. Thus every old operator occurs exactly once;
the construction preserves projectivity and all commutator sums exactly.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-- Record a deterministic coordinate without forgetting the original answer. -/
def graphRefinement (M : A → Matrix D D ℂ) (c : A → C) (p : C × A) : Matrix D D ℂ :=
  if p.1 = c p.2 then M p.2 else 0

/-- The alphabet change is ordinary deterministic POVM postprocessing. -/
def graphRefinementPOVM (M : POVM A D) (c : A → C) : POVM (C × A) D :=
  M.map (fun a => (c a, a))

variable [Fintype K] [DecidableEq K] [Fintype B]

end MIPRE.Introspection
end


