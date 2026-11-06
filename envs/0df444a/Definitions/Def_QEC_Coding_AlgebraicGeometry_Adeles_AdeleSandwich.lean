-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:09:37.109592+00:00
-- url     : https://prove2.me/theorems/f08158f8-72ee-4287-ac39-9191660017e7
-- title:
--   Adele Sandwich
-- statement:
--   Definitions and structural lemmas for Adele Sandwich, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleSandwich.lean

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance globalAdeleSandwichAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
attribute [local instance] globalAdeleSandwichAlgebra
local instance globalAdeleSandwichScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
attribute [local instance] globalAdeleSandwichScalarTower
namespace GlobalPlace
variable [IsFullConstantField k F]
local instance globalAdeleSandwichRiemannRochFiniteDimensional
    (D : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule D) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
attribute [local instance] globalAdeleSandwichRiemannRochFiniteDimensional
local instance globalAdeleSandwichFilterAddCommGroup
    (D : Divisor (GlobalPlace k F)) :
    AddCommGroup (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.addCommGroup _
attribute [local instance] globalAdeleSandwichFilterAddCommGroup
local instance globalAdeleSandwichFilterModule
    (D : Divisor (GlobalPlace k F)) :
    Module k (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.module _
attribute [local instance] globalAdeleSandwichFilterModule
def globalAdeleTopSubmodule :
    Submodule k (GlobalAdele (k := k) (F := F)) :=
  ⊤
theorem globalAdeleExceptionalFinite
    (a : GlobalAdele (k := k) (F := F)) :
    {P : GlobalPlace k F | ¬P.valuation (a.val P) ≤ 1}.Finite :=
  (Filter.eventually_cofinite.mp a.property).subset (by
    intro P hP
    change a.val P ∉ P.valuationRing
    rw [mem_valuationRing_iff]
    exact hP)
noncomputable def globalAdeleExceptionalPlaces
    (a : GlobalAdele (k := k) (F := F)) : Finset (GlobalPlace k F) :=
  (globalAdeleExceptionalFinite (k := k) (F := F) a).toFinset
noncomputable def divisorOfGlobalAdele
    (a : GlobalAdele (k := k) (F := F)) :
    Divisor (GlobalPlace k F) :=
  Finsupp.onFinset (globalAdeleExceptionalPlaces (k := k) (F := F) a)
    (fun P =>
      if 1 < P.valuation (a.val P) then
        WithZero.log (P.valuation (a.val P))
      else 0)
    (by
      intro P hP
      by_cases hlt : 1 < P.valuation (a.val P)
      · dsimp only [globalAdeleExceptionalPlaces]
        exact (globalAdeleExceptionalFinite (k := k) (F := F) a).mem_toFinset.mpr
          (not_le.mpr hlt)
      · simp only [hlt, ite_false, ne_eq, not_true_eq_false] at hP)
noncomputable def riemannRochFilterDiffDimension
    (D E : Divisor (GlobalPlace k F)) : ℕ :=
  Module.finrank k
    (riemannRochSubmodule E ⧸
      Submodule.comap (riemannRochSubmodule E).subtype
        (riemannRochSubmodule D))
@[nolint unusedArguments]
noncomputable def globalAdeleSandwichRank
    (D E : Divisor (GlobalPlace k F)) (_hDE : D ≤ E) : ℤ := by
  letI : AddCommGroup
      (globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F)) :=
    Submodule.addCommGroup _
  letI : Module k
      (globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F)) :=
    Submodule.module _
  exact Int.ofNat (Module.finrank k
    (↥(globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F)) ⧸
      Submodule.comap
        (globalAdeleFilter (k := k) (F := F) E +
          diagonalAdeleSubmodule (k := k) (F := F)).subtype
        (globalAdeleFilter (k := k) (F := F) D +
          diagonalAdeleSubmodule (k := k) (F := F))))
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


