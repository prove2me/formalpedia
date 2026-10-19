-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuardGame
-- name    : MIPRE_Foundations_Introspection_PrefixGuardGame
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:54.52682+00:00
-- url     : https://prove2.me/theorems/b0a4838b-f865-4ac5-9e48-5677eff02d06
-- title:
--   Definitions of PrefixGuardGame: Adding honest prefix guards preserves completeness Changing a predicate only on zero measurement effects preserves its…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.PrefixGuardGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Adding honest prefix guards preserves completeness. Changing a predicate only on zero measurement effects preserves its value. Applying this observation to the local prefix guards keeps the honest state, dimension and PCC property, while guard rejection can only reduce arbitrary strategies' success.
--
--   **Definitions** (1): `MIPRE.Introspection.PrefixGuard.game` (Retain the question law and add both local prefix checks.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `copied_dimension`, `game_mu`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.PrefixGuardGame` (`MIPRE/Foundations/Introspection/PrefixGuardGame.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 49 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/PrefixGuardGame.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PrefixGuardGame.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
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
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuard

/-! # Adding honest prefix guards preserves completeness

Changing a predicate only on zero measurement effects preserves its value.
Applying this observation to the local prefix guards keeps the honest state,
dimension and PCC property, while guard rejection can only reduce arbitrary
strategies' success.
-/

noncomputable section
namespace MIPRE
open Classical
set_option linter.unusedSectionVars false

namespace SyncStrategy
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {G : SynchronousGame X A}

end SyncStrategy

namespace Introspection.PrefixGuard
variable {F ι A PA P Q : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq PA] [Fintype Q] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (type : Q → QuestionType P ℓ)
  (G : Game Q Q (ParsedAnswer (ι → F) A PA) (ParsedAnswer (ι → F) A PA))

/-- Retain the question law and add both local prefix checks. Raw question
payloads remain available to the original predicate. -/
def game : Game Q Q (ParsedAnswer (ι → F) A PA) (ParsedAnswer (ι → F) A PA) :=
  { G with D := fun q r a b => check L (type q) a && check L (type r) b && G.D q r a b }

@[simp] theorem game_mu (q r : Q) : (game L type G).μ q r = G.μ q r := rfl

@[simp] theorem copied_dimension (S : SyncStrategy G.doubled) :
    (S.copy (game L type G).doubled).d = S.d := rfl

end Introspection.PrefixGuard
end MIPRE


