-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister
-- name    : MIPRE_Foundations_Introspection_StrategyReplacementRegister
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:54:09.585357+00:00
-- url     : https://prove2.me/theorems/8a309a8b-474f-40d0-94d5-baedc6be2718
-- title:
--   Definitions of StrategyReplacementRegister: Reassembly in the original EPR-register ordering The added register belongs to Alice's auxiliary space
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.StrategyReplacementRegister` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reassembly in the original EPR-register ordering. The added register belongs to Alice's auxiliary space. The shared state is exactly the original EPR factor tensored with that extended auxiliary state. These definitions construct the actual strategy on finite registers and preserve all nonselected measurements under the displayed reassociation.
--
--   **Definitions** (1): `MIPRE.Introspection.registeredReplacement` (The new actual question-indexed family in the original register-first ordering.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `registeredReplacement_at`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.StrategyReplacementRegister` (`MIPRE/Foundations/Introspection/StrategyReplacementRegister.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 46 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/StrategyReplacementRegister.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/StrategyReplacementRegister.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement

/-! # Reassembly in the original EPR-register ordering

The added register belongs to Alice's auxiliary space. The shared state is
exactly the original EPR factor tensored with that extended auxiliary state.
These definitions construct the actual strategy on finite registers and
preserve all nonselected measurements under the displayed reassociation.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {X Y A B C I H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]

/-- The new actual question-indexed family in the original register-first
ordering. -/
def registeredReplacement (MA : X → POVM A (I × H)) (q : X)
    (R : POVM A ((I × H) × T)) : X → POVM A (I × (H × T)) :=
  fun x => (replaceExtended MA q R x).reindex (Equiv.prodAssoc I H T)

@[simp] theorem registeredReplacement_at (MA : X → POVM A (I × H)) (q : X)
    (R : POVM A ((I × H) × T)) :
    registeredReplacement MA q R q = R.reindex (Equiv.prodAssoc I H T) := by
  simp only [registeredReplacement, replaceExtended_at]

variable [Nonempty I]

end MIPRE.Introspection
end


