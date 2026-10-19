-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
-- name    : MIPRE_Foundations_Introspection_HidingMaps
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:55:49.143863+00:00
-- url     : https://prove2.me/theorems/89840502-0a97-453e-8b1e-a28083227e94
-- title:
--   Definitions of HidingMaps: Guarded coarse maps for the actual adjacent hiding test The earlier fine label retains only its preceding prefix,…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.HidingMaps` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Guarded coarse maps for the actual adjacent hiding test. The earlier fine label retains only its preceding prefix, current dual output, and remaining tail. The next map uses the later prefix as a key. A separate dummy outcome handles malformed answers and prefix mismatches, so each keyed map is total on the entire answer alphabet and defines a complete measurement.
--
--   **Definitions** (2): `MIPRE.Introspection.TypedEstimates.hidingCoarse` (The fine outcome retained at hiding level `k+1`.); `MIPRE.Introspection.TypedEstimates.hidingNextGuarded` (Process a retained fine outcome using the later prefix.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.HidingMaps` (`MIPRE/Foundations/Introspection/HidingMaps.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 59 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingMaps.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingMaps.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
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
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
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
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity

/-! # Guarded coarse maps for the actual adjacent hiding test

The earlier fine label retains only its preceding prefix, current dual output,
and remaining tail. The next map uses the later prefix as a key. A separate
dummy outcome handles malformed answers and prefix mismatches, so each keyed
map is total on the entire answer alphabet and defines a complete measurement.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The fine outcome retained at hiding level `k+1`. Off-format answers have
their own outcome; unused coordinates of a well-formed answer are discarded. -/
def hidingCoarse (P : CL.CLFun F ι ℓ) (k : ℕ) :
    ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × (ι → F) × (ι → F))
  | .hide y yp x => some (P.outputPrefix k y,
      CL.proj (P.factorOfPrefix k (P.outputPrefix k y)) yp,
      CL.proj (CLChecks.prefixRegister P (k + 1) y)ᶜ x)
  | _ => none

/-- Process a retained fine outcome using the later prefix. On a prefix
mismatch the output is the dummy label, rather than an incomplete family. -/
def hidingNextGuarded (P : CL.CLFun F ι ℓ) (k : ℕ) :
    Option (ι → F) → Option ((ι → F) × (ι → F) × (ι → F)) →
      Option ((ι → F) × (ι → F) × (ι → F))
  | some y, some (p, _, x) =>
      if p = P.outputPrefix k y then
        some (p, CLChecks.dualReadout P (k + 1) y x,
          CL.proj (CLChecks.prefixRegister P (k + 2) y)ᶜ x)
      else none
  | _, _ => none

end MIPRE.Introspection.TypedEstimates

end


