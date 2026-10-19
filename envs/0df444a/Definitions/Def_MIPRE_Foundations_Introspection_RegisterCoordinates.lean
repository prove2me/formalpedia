-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
-- name    : MIPRE_Foundations_Introspection_RegisterCoordinates
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:49:32.247557+00:00
-- url     : https://prove2.me/theorems/b1fc38cd-074b-4aae-99a7-6bc86df5e5a1
-- title:
--   Definitions of RegisterCoordinates: The concrete coordinate splits for nested CL registers
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.RegisterCoordinates` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # The concrete coordinate splits for nested CL registers
--
--   **Definitions** (5): `MIPRE.Introspection.ambientSplit` (Splitting an ambient assignment into a register and its complement.); `MIPRE.Introspection.coordinateInsert` (Insert an enumerated vector into its ambient register, setting all other coordinates to zero.); `MIPRE.Introspection.coordinateLinear` (The paper's map on `U` in the coordinate presentation used by the Pauli library.); `MIPRE.Introspection.coordinateRestrict` (Restrict the ambient assignment to the enumerated register.); `MIPRE.Introspection.coordinateSplit` (Split `V` into the selected coordinates `U`, enumerated by `Fin`, and `V \ U`.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coordinateRestrict_insert`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.RegisterCoordinates` (`MIPRE/Foundations/Introspection/RegisterCoordinates.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 38 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/RegisterCoordinates.lean; blueprint lem:pauli-mixing

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RegisterCoordinates.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing

/-! # The concrete coordinate splits for nested CL registers -/

noncomputable section

namespace MIPRE.Introspection

open Finset Classical

set_option linter.unusedSectionVars false

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]

/-- Splitting an ambient assignment into a register and its complement. -/
def ambientSplit (V : Finset ι) : (ι → F) ≃ (V → F) × (↥(Vᶜ) → F) where
  toFun v := (fun i => v i, fun i => v i)
  invFun p i := if h : i ∈ V then p.1 ⟨i, h⟩ else p.2 ⟨i, mem_compl.mpr h⟩
  left_inv v := by funext i; dsimp only; split <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [dif_pos i.property]
    · funext i
      simp only [dif_neg (mem_compl.mp i.property)]

/-- Split `V` into the selected coordinates `U`, enumerated by `Fin`, and `V \ U`.
This is an actual coordinate restriction and assembly, rather than a cardinality choice. -/
def coordinateSplit (U V : Finset ι) (hUV : U ⊆ V) :
    (V → F) ≃ (Fin (Fintype.card U) → F) × (↥(V \ U) → F) where
  toFun v := (fun j => v ⟨(Fintype.equivFin U).symm j,
    hUV ((Fintype.equivFin U).symm j).property⟩,
    fun i => v ⟨i, (mem_sdiff.mp i.property).1⟩)
  invFun p i := if h : i.val ∈ U then p.1 (Fintype.equivFin U ⟨i, h⟩)
    else p.2 ⟨i, mem_sdiff.mpr ⟨i.property, h⟩⟩
  left_inv v := by
    funext i
    dsimp only
    split <;> simp only [Equiv.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · funext j
      simp only [dif_pos ((Fintype.equivFin U).symm j).property]
      change p.1 ((Fintype.equivFin U) ((Fintype.equivFin U).symm j)) = p.1 j
      rw [Equiv.apply_symm_apply]
    · funext i
      simp only [dif_neg (mem_sdiff.mp i.property).2]

variable [Field F]

/-- Insert an enumerated vector into its ambient register, setting all other coordinates to zero. -/
def coordinateInsert (U : Finset ι) : (Fin (Fintype.card U) → F) →ₗ[F] (ι → F) where
  toFun v i := if h : i ∈ U then v (Fintype.equivFin U ⟨i, h⟩) else 0
  map_add' v w := by funext i; by_cases hi : i ∈ U <;> simp [hi]
  map_smul' c v := by funext i; by_cases hi : i ∈ U <;> simp [hi]

/-- Restrict the ambient assignment to the enumerated register. -/
def coordinateRestrict (U : Finset ι) : (ι → F) →ₗ[F] (Fin (Fintype.card U) → F) where
  toFun v j := v ((Fintype.equivFin U).symm j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateRestrict_insert (U : Finset ι)
    (v : Fin (Fintype.card U) → F) : coordinateRestrict U (coordinateInsert U v) = v := by
  funext j
  simp only [coordinateRestrict, coordinateInsert, LinearMap.coe_mk, AddHom.coe_mk,
    dif_pos ((Fintype.equivFin U).symm j).property]
  change v ((Fintype.equivFin U) ((Fintype.equivFin U).symm j)) = v j
  rw [Equiv.apply_symm_apply]

/-- The paper's map on `U` in the coordinate presentation used by the Pauli library. -/
def coordinateLinear {U : Finset ι} (L : CL.RegLinear F U) :
    (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F) :=
  coordinateRestrict U ∘ₗ L.toLinearMap ∘ₗ coordinateInsert U

end MIPRE.Introspection

end


