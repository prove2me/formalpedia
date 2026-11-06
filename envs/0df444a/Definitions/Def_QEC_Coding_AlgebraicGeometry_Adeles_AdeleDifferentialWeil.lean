-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:46:13.831385+00:00
-- url     : https://prove2.me/theorems/424f3db9-a628-4f03-b9f8-eb6167e38706
-- title:
--   Adele Differential Weil
-- statement:
--   Definitions and structural lemmas for Adele Differential Weil, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialWeil.lean

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSimplePoleResidueSum_diagonal_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSimplePoleResidueSum_eq_zero_of_mem_differentialFilter

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance globalAdeleDifferentialWeilAlgebra :
    Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
attribute [local instance] globalAdeleDifferentialWeilAlgebra
local instance globalAdeleDifferentialWeilScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
attribute [local instance] globalAdeleDifferentialWeilScalarTower
namespace GlobalPlace
variable [IsFullConstantField k F]
noncomputable def differentialResiduePartial
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdele (k := k) (F := F) →ₗ.[k] k :=
  ⟨globalAdeleSimplePoleSubmodule (k := k) (F := F) omega,
    globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega⟩
noncomputable def diagonalZeroPartial :
    GlobalAdele (k := k) (F := F) →ₗ.[k] k :=
  ⟨diagonalAdeleSubmodule (k := k) (F := F), 0⟩
theorem differentialResiduePartial_compatible
    (omega : Differential k F) (homega : omega ≠ 0)
    (x : (differentialResiduePartial (k := k) (F := F) omega homega).domain)
    (y : (diagonalZeroPartial (k := k) (F := F)).domain)
    (hxy : (x : GlobalAdele (k := k) (F := F)) = y) :
    differentialResiduePartial (k := k) (F := F) omega homega x =
      diagonalZeroPartial (k := k) (F := F) y := by
  change globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega x = 0
  rcases y.property with ⟨f, hf⟩
  have hxf : (x : GlobalAdele (k := k) (F := F)) =
      diagonalAdele (k := k) (F := F) f := hxy.trans hf.symm
  have hfSimple : diagonalAdele (k := k) (F := F) f ∈
      globalAdeleSimplePoleSubmodule (k := k) (F := F) omega := by
    rw [← hxf]
    exact x.property
  have hx : x = ⟨diagonalAdele (k := k) (F := F) f, hfSimple⟩ :=
    Subtype.ext hxf
  rw [hx]
  exact globalAdeleSimplePoleResidueSum_diagonal_eq_zero
    (k := k) (F := F) omega homega f hfSimple
noncomputable def differentialResidueGluedPartial
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdele (k := k) (F := F) →ₗ.[k] k :=
  (differentialResiduePartial (k := k) (F := F) omega homega).sup
    (diagonalZeroPartial (k := k) (F := F))
    (differentialResiduePartial_compatible
      (k := k) (F := F) omega homega)
noncomputable def differentialResidueExtension
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdele (k := k) (F := F) →ₗ[k] k :=
  Classical.choose
    (LinearMap.exists_extend
      (differentialResidueGluedPartial
        (k := k) (F := F) omega homega).toFun)
theorem differentialResidueExtension_comp
    (omega : Differential k F) (homega : omega ≠ 0) :
    (differentialResidueExtension (k := k) (F := F) omega homega).comp
        (differentialResidueGluedPartial
          (k := k) (F := F) omega homega).domain.subtype =
      (differentialResidueGluedPartial
        (k := k) (F := F) omega homega).toFun :=
  Classical.choose_spec
    (LinearMap.exists_extend
      (differentialResidueGluedPartial
        (k := k) (F := F) omega homega).toFun)
theorem differentialResidueExtension_apply
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : (differentialResidueGluedPartial
      (k := k) (F := F) omega homega).domain) :
    differentialResidueExtension (k := k) (F := F) omega homega
        (a : GlobalAdele (k := k) (F := F)) =
      differentialResidueGluedPartial (k := k) (F := F) omega homega a := by
  have h := congrArg (fun f => f a)
    (differentialResidueExtension_comp
      (k := k) (F := F) omega homega)
  exact h
theorem differentialResidueExtension_apply_of_mem_simplePole
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : GlobalAdele (k := k) (F := F))
    (ha : a ∈ globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    differentialResidueExtension (k := k) (F := F) omega homega a =
      globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega ⟨a, ha⟩ := by
  let aGlued : (differentialResidueGluedPartial
      (k := k) (F := F) omega homega).domain :=
    ⟨a, Submodule.mem_sup_left ha⟩
  have hext := differentialResidueExtension_apply
    (k := k) (F := F) omega homega aGlued
  have hleft :=
    (LinearPMap.left_le_sup
      (differentialResiduePartial (k := k) (F := F) omega homega)
      (diagonalZeroPartial (k := k) (F := F))
      (differentialResiduePartial_compatible
        (k := k) (F := F) omega homega)).2
      (x := ⟨a, ha⟩) (y := aGlued) rfl
  exact hext.trans hleft.symm
theorem differentialResidueExtension_apply_of_mem_diagonal
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : GlobalAdele (k := k) (F := F))
    (ha : a ∈ diagonalAdeleSubmodule (k := k) (F := F)) :
    differentialResidueExtension (k := k) (F := F) omega homega a = 0 := by
  let aGlued : (differentialResidueGluedPartial
      (k := k) (F := F) omega homega).domain :=
    ⟨a, Submodule.mem_sup_right ha⟩
  have hext := differentialResidueExtension_apply
    (k := k) (F := F) omega homega aGlued
  have hright :=
    (LinearPMap.right_le_sup
      (differentialResiduePartial (k := k) (F := F) omega homega)
      (diagonalZeroPartial (k := k) (F := F))
      (differentialResiduePartial_compatible
        (k := k) (F := F) omega homega)).2
      (x := ⟨a, ha⟩) (y := aGlued) rfl
  exact hext.trans hright.symm
theorem differentialResidueExtension_vanishes
    (omega : Differential k F) (homega : omega ≠ 0) :
    ∀ a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega),
      differentialResidueExtension (k := k) (F := F) omega homega a = 0 := by
  intro a ha
  change a ∈ globalAdeleFilter (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega) +
      diagonalAdeleSubmodule (k := k) (F := F) at ha
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  rw [map_add,
    differentialResidueExtension_apply_of_mem_simplePole
      (k := k) (F := F) omega homega a₁
      (globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
        (k := k) (F := F) omega homega ha₁),
    globalAdeleSimplePoleResidueSum_eq_zero_of_mem_differentialFilter
      (k := k) (F := F) omega homega ⟨a₁, ha₁⟩,
    differentialResidueExtension_apply_of_mem_diagonal
      (k := k) (F := F) omega homega a₂ ha₂,
    add_zero]
noncomputable def globalAdeleWeilDifferentialOfDifferential
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdeleWeilDifferential k F :=
  ⟨differentialResidueExtension (k := k) (F := F) omega homega,
    ⟨FunctionFieldDifferential.differentialDivisor
      (k := k) (F := F) omega homega,
      differentialResidueExtension_vanishes
        (k := k) (F := F) omega homega⟩⟩
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


