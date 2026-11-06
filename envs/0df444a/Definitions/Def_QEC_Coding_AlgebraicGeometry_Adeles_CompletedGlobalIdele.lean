-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalIdele
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalIdele
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:22:55.404651+00:00
-- url     : https://prove2.me/theorems/4f9fac73-15fb-4a35-881b-f43b17fa9a27
-- title:
--   Completed Global Idele
-- statement:
--   Definitions and structural lemmas for Completed Global Idele, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedDiagonal_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedDiagonal_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open Filter
open scoped RestrictedProduct WithZero
noncomputable section
namespace GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
abbrev LocalUnitGroup (P : GlobalPlace k F) : Subgroup P.LocalCompletionˣ :=
  (Submonoid.ofClass P.LocalIntegerRing).units
theorem isOpen_localUnitGroup (P : GlobalPlace k F) :
    IsOpen (P.LocalUnitGroup : Set P.LocalCompletionˣ) := by
  apply Submonoid.isOpen_units
  exact Valued.isOpen_valuationSubring P.LocalCompletion
instance localUnitGroupOpenFact :
    Fact (∀ P : GlobalPlace k F,
      IsOpen (P.LocalUnitGroup : Set P.LocalCompletionˣ)) :=
  ⟨isOpen_localUnitGroup⟩
abbrev CompletedGlobalIdele : Type _ :=
  Πʳ P : GlobalPlace k F, [P.LocalCompletionˣ, P.LocalUnitGroup]
def completionUnitsEmbedding (P : GlobalPlace k F) : Fˣ →* P.LocalCompletionˣ :=
  Units.map P.completionEmbedding.toMonoidHom
@[simp]
theorem completionUnitsEmbedding_apply (P : GlobalPlace k F) (u : Fˣ) :
    (P.completionUnitsEmbedding u : P.LocalCompletion) =
      P.completionEmbedding (u : F) :=
  rfl
section Diagonal
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
def completedIdeleDiagonal : Fˣ →* CompletedGlobalIdele (k := k) (F := F) where
  toFun u := ⟨fun P ↦ P.completionUnitsEmbedding u, by
    filter_upwards
      [eventually_mem_valuationRing (k := k) (F := F) (u : F),
       eventually_mem_valuationRing (k := k) (F := F) ((u⁻¹ : Fˣ) : F)]
      with P hu huInv
    change P.completionUnitsEmbedding u ∈
      (Submonoid.ofClass P.LocalIntegerRing).units
    rw [Submonoid.mem_units_iff]
    constructor
    · exact (completionEmbedding_mem_localIntegerRing_iff P (u : F)).mpr hu
    · exact (completionEmbedding_mem_localIntegerRing_iff P
          ((u⁻¹ : Fˣ) : F)).mpr huInv⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro P
    exact map_one P.completionUnitsEmbedding
  map_mul' u v := by
    apply RestrictedProduct.ext
    intro P
    exact map_mul P.completionUnitsEmbedding u v
end Diagonal
def completedIdeleAt (P : GlobalPlace k F) :
    CompletedGlobalIdele (k := k) (F := F) →ₜ* P.LocalCompletionˣ where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := RestrictedProduct.continuous_eval P
def completedAdeleUnitsEquivIdele :
    (CompletedGlobalAdele (k := k) (F := F))ˣ ≃*
      CompletedGlobalIdele (k := k) (F := F) :=
  RestrictedProduct.unitsEquiv (fun P : GlobalPlace k F ↦ P.LocalCompletion)
section DiagonalCompatibility
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
end DiagonalCompatibility
def ideleNonintegralPlaces
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    Finset (GlobalPlace k F) :=
  (Filter.eventually_cofinite.mp x.property).toFinset
def completedIntegralIdeleSubgroup
    (S : Finset (GlobalPlace k F)) :
    Subgroup (CompletedGlobalIdele (k := k) (F := F)) where
  carrier := {x | ∀ P, P ∉ S → x P ∈ P.LocalUnitGroup}
  one_mem' := fun _P _ ↦ one_mem _
  mul_mem' hx hy P hP := mul_mem (hx P hP) (hy P hP)
  inv_mem' hx P hP := inv_mem (hx P hP)
abbrev completedEverywhereIntegralIdeleSubgroup :
    Subgroup (CompletedGlobalIdele (k := k) (F := F)) :=
  completedIntegralIdeleSubgroup (k := k) (F := F) ∅
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


