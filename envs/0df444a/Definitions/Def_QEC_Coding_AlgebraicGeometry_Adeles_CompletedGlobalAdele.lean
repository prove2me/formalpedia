-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:20:05.350005+00:00
-- url     : https://prove2.me/theorems/dfeca007-615a-491d-99ab-81fe537b3be0
-- title:
--   Completed Global Adele
-- statement:
--   Definitions and structural lemmas for Completed Global Adele, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalAdele.lean

import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.ValuedField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
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
abbrev LocalCompletion (P : GlobalPlace k F) : Type _ :=
  P.valuation.Completion
def completionEmbedding (P : GlobalPlace k F) : F →+* P.LocalCompletion :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv P.valuation).symm
@[simp]
theorem completionEmbedding_apply (P : GlobalPlace k F) (f : F) :
    P.completionEmbedding f = (f : P.LocalCompletion) :=
  rfl
@[simp]
theorem valuation_completionEmbedding (P : GlobalPlace k F) (f : F) :
    Valued.v (P.completionEmbedding f) = P.valuation f := by
  rw [completionEmbedding_apply, Valued.valuedCompletion_apply]
  exact WithVal.valued_toVal P.valuation f
abbrev LocalIntegerRing (P : GlobalPlace k F) : ValuationSubring P.LocalCompletion :=
  (Valued.v : Valuation P.LocalCompletion ℤᵐ⁰).valuationSubring
theorem completionEmbedding_mem_localIntegerRing_iff
    (P : GlobalPlace k F) (f : F) :
    P.completionEmbedding f ∈ P.LocalIntegerRing ↔ f ∈ P.valuationRing := by
  rw [Valuation.mem_valuationSubring_iff, valuation_completionEmbedding,
    mem_valuationRing_iff]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
abbrev CompletedGlobalAdele : Type _ :=
  Πʳ P : GlobalPlace k F, [P.LocalCompletion, P.LocalIntegerRing]
def completedDiagonal : F →+* CompletedGlobalAdele (k := k) (F := F) where
  toFun f := ⟨fun P ↦ P.completionEmbedding f, by
    filter_upwards [eventually_mem_valuationRing (k := k) (F := F) f] with P hP
    exact (completionEmbedding_mem_localIntegerRing_iff P f).mpr hP⟩
  map_one' := Subtype.ext <| funext fun P ↦ map_one P.completionEmbedding
  map_mul' f g := Subtype.ext <| funext fun P ↦ map_mul P.completionEmbedding f g
  map_zero' := Subtype.ext <| funext fun P ↦ map_zero P.completionEmbedding
  map_add' f g := Subtype.ext <| funext fun P ↦ map_add P.completionEmbedding f g
instance : IsTopologicalRing (CompletedGlobalAdele (k := k) (F := F)) := by
  letI : Fact (∀ P : GlobalPlace k F,
      IsOpen (P.LocalIntegerRing : Set P.LocalCompletion)) :=
    ⟨fun P ↦ Valued.isOpen_valuationSubring P.LocalCompletion⟩
  infer_instance
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


