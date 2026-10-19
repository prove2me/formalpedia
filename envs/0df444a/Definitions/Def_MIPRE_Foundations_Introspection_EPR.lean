-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_EPR
-- name    : MIPRE_Foundations_Introspection_EPR
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:49.232871+00:00
-- url     : https://prove2.me/theorems/c9dd61d5-0ed5-4b48-9ad7-99848b4bde94
-- title:
--   Definitions of EPR: Exactly consistent Pauli readouts with arbitrary ancillary states
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.EPR` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Exactly consistent Pauli readouts with arbitrary ancillary states
--
--   **Definitions** (1): `MIPRE.Introspection.eprWithAux` (EPR on the sampled register, together with an arbitrary auxiliary state.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.EPR` (`MIPRE/Foundations/Introspection/EPR.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/EPR.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/EPR.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_WeylEPR

/-! # Exactly consistent Pauli readouts with arbitrary ancillary states -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl
open scoped Kronecker

variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {n : ℕ}

/-- EPR on the sampled register, together with an arbitrary auxiliary state. -/
def eprWithAux (ξ : H × K → ℂ) : ((Fin n → F) × H) × ((Fin n → F) × K) → ℂ :=
  expVec (epr (F := F) (n := Fin n)) ξ

end MIPRE.Introspection

end


