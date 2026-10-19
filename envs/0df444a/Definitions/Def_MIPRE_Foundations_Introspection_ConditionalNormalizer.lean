-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
-- name    : MIPRE_Foundations_Introspection_ConditionalNormalizer
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:24.450908+00:00
-- url     : https://prove2.me/theorems/72082bd6-c289-4539-9a6c-6894bd5b6bfd
-- title:
--   Definitions of ConditionalNormalizer: Replacing a conditional hiding normalizer by its ideal prefix The coarse outcome map may depend on the retained…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ConditionalNormalizer` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Replacing a conditional hiding normalizer by its ideal prefix. The coarse outcome map may depend on the retained conditioning label. Positivity of the ideal commuting prefix/fine-projector products lets us retain the fine agreement without a factor depending on either outcome alphabet. The resulting replacement costs three times each of the conditional, prefix, and fine errors.
--
--   **Definitions** (1): `MIPRE.Introspection.conditionalIdeal` (The ideal joint outcome: its prefix times the fine family coarsened with the map selected by that prefix.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ConditionalNormalizer` (`MIPRE/Foundations/Introspection/ConditionalNormalizer.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 27 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ConditionalNormalizer.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ConditionalNormalizer.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Theorems.Thm_MIPRE_sum_snorm_sq_mul_le
import Theorems.Thm_MIPRE_sum_snorm_sq_triangle3

/-! # Replacing a conditional hiding normalizer by its ideal prefix

The coarse outcome map may depend on the retained conditioning label. Positivity
of the ideal commuting prefix/fine-projector products lets us retain the fine
agreement without a factor depending on either outcome alphabet. The resulting
replacement costs three times each of the conditional, prefix, and fine errors.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- The ideal joint outcome: its prefix times the fine family coarsened with
the map selected by that prefix. -/
def conditionalIdeal (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (p : Y × Z) : Matrix K K ℂ :=
  Q p.1 * fibSum P (f p.1) p.2

end MIPRE.Introspection


