-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
-- name    : MIPRE_Foundations_Introspection_ValueStability
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:40.790922+00:00
-- url     : https://prove2.me/theorems/57423e42-7a65-482f-b9e0-86315dc3afea
-- title:
--   Definitions of ValueStability: Value stability for the introspection induction The induction replaces projective measurements using summed squared…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ValueStability` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Value stability for the introspection induction. The induction replaces projective measurements using summed squared state distance. The resulting change in test acceptance is dimension independent: `2 sqrt(delta)` per party. Summing outcomes before Cauchy--Schwarz avoids any loss depending on the size of the introspection answer alphabet.
--
--   **Definitions** (1): `MIPRE.Introspection.testAcceptance` (The acceptance functional of one test on bare local measurement families.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ValueStability` (`MIPRE/Foundations/Introspection/ValueStability.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 25 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ValueStability.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ValueStability.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Swap

/-! # Value stability for the introspection induction

The induction replaces projective measurements using summed squared state
distance. The resulting change in test acceptance is dimension independent:
`2 sqrt(delta)` per party. Summing outcomes before Cauchy--Schwarz avoids any
loss depending on the size of the introspection answer alphabet.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]

set_option linter.unusedSectionVars false

section Bipartite

variable {A B H K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- The acceptance functional of one test on bare local measurement families. -/
def testAcceptance (ψ : H × K → ℂ) (D : A → B → Bool)
    (M : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ) : ℝ :=
  ∑ a, ∑ b, (if D a b then 1 else 0) * bornProb ψ (M a) (Q b)

end Bipartite

end MIPRE.Introspection

end


