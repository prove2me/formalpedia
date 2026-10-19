-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
-- name    : MIPRE_Foundations_Introspection_AuxiliaryChecks
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:50:51.326402+00:00
-- url     : https://prove2.me/theorems/a130b5c3-d067-4626-b66a-41bcc4bda6d9
-- title:
--   Definitions of AuxiliaryChecks: The concrete auxiliary introspection checks These are the finite predicates in the sampling, hiding and original-game…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AuxiliaryChecks` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The concrete auxiliary introspection checks. These are the finite predicates in the sampling, hiding and original-game tests. They operate on parsed answers. Byte parsing, the global length checks, and clocked calls to the original programs are separate machine obligations. In particular, prefixes are read from a claimed output without applying its CL map again, and both tail projections in a hiding edge use the later answer.
--
--   **Definitions** (7): `MIPRE.Introspection.CLChecks.dualReadout` (The dual linear readout at a selected stage, in its actual local coordinates.); `MIPRE.Introspection.CLChecks.hidingNext` (The four comparisons on the edge from hiding level `k+1` to `k+2`.); `MIPRE.Introspection.CLChecks.hidingPauli` (The first hiding edge compares with the Pauli-X answer on the original register.); `MIPRE.Introspection.CLChecks.hidingRead` (The last hiding measurement and Read agree on the earlier question and full dual answer.); `MIPRE.Introspection.CLChecks.prefixRegister` (Registers visited while reading the first `k` components of a claimed output.); `MIPRE.Introspection.CLChecks.reading` (The reading-introspection check forgets only the dual readout.); `MIPRE.Introspection.CLChecks.sampling` (The sampling-introspection check retains the original answer as well as the question.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AuxiliaryChecks` (`MIPRE/Foundations/Introspection/AuxiliaryChecks.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 44 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliaryChecks.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryChecks.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # The concrete auxiliary introspection checks

These are the finite predicates in the sampling, hiding and original-game
tests. They operate on parsed answers. Byte parsing, the global length checks,
and clocked calls to the original programs are separate machine obligations.
In particular, prefixes are read from a claimed output without applying its
CL map again, and both tail projections in a hiding edge use the later answer.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Classical

variable {F ι A : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

namespace CLChecks

/-- Registers visited while reading the first `k` components of a claimed output. -/
def prefixRegister : {ℓ : ℕ} → CL.CLFun F ι ℓ → ℕ → (ι → F) → Finset ι
  | _, _, 0, _ => ∅
  | _, .zero, _ + 1, _ => ∅
  | _, .cons S _ next, k + 1, y =>
      S ∪ prefixRegister (next (CL.proj S y)) k (CL.proj Sᶜ y)

/-- The dual linear readout at a selected stage, in its actual local coordinates. -/
def dualReadout : {ℓ : ℕ} → CL.CLFun F ι ℓ → ℕ → (ι → F) → (ι → F) → (ι → F)
  | _, .zero, _, _, _ => 0
  | _, .cons S L _, 0, _, x =>
      coordinateInsert S (CL.lperp (coordinateLinear L) (coordinateRestrict S x))
  | _, .cons S _ next, k + 1, y, x =>
      dualReadout (next (CL.proj S y)) k (CL.proj Sᶜ y) x

/-- The sampling-introspection check retains the original answer as well as the question. -/
def sampling (P : CL.CLFun F ι ℓ) (u v : (ι → F) × A) : Prop :=
  u.1 = P.eval v.1 ∧ u.2 = v.2

/-- The reading-introspection check forgets only the dual readout. -/
def reading (u : (ι → F) × A) (v : (ι → F) × (ι → F) × A) : Prop :=
  u.1 = v.1 ∧ u.2 = v.2.2

/-- The last hiding measurement and Read agree on the earlier question and full dual answer. -/
def hidingRead (P : CL.CLFun F ι ℓ)
    (u : (ι → F) × (ι → F) × (ι → F)) (v : (ι → F) × (ι → F) × A) : Prop :=
  P.outputPrefix (ℓ - 1) u.1 = P.outputPrefix (ℓ - 1) v.1 ∧ u.2.1 = v.2.1

/-- The four comparisons on the edge from hiding level `k+1` to `k+2`.
The later player's question fixes both tail projections and the new dual map. -/
def hidingNext (P : CL.CLFun F ι ℓ) (k : ℕ)
    (u v : (ι → F) × (ι → F) × (ι → F)) : Prop :=
  P.outputPrefix k u.1 = P.outputPrefix k v.1 ∧
    CL.proj (prefixRegister P (k + 1) v.1) u.2.1 =
      CL.proj (prefixRegister P (k + 1) v.1) v.2.1 ∧
    CL.proj (prefixRegister P (k + 2) v.1)ᶜ u.2.2 =
      CL.proj (prefixRegister P (k + 2) v.1)ᶜ v.2.2 ∧
    CL.proj (P.factorOfPrefix (k + 1) (P.outputPrefix (k + 1) v.1)) v.2.1 =
      dualReadout P (k + 1) v.1 u.2.2

/-- The first hiding edge compares with the Pauli-X answer on the original register. -/
def hidingPauli (P : CL.CLFun F ι ℓ) (x : ι → F)
    (v : (ι → F) × (ι → F) × (ι → F)) : Prop :=
  CL.proj (P.factorOfPrefix 0 0) v.2.1 = dualReadout P 0 0 x ∧
    CL.proj (P.factorOfPrefix 0 0)ᶜ x = CL.proj (P.factorOfPrefix 0 0)ᶜ v.2.2

end CLChecks

end MIPRE.Introspection

end


