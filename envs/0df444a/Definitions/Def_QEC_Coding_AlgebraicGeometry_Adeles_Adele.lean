-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_Adele
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:19:22.346196+00:00
-- url     : https://prove2.me/theorems/3d14b202-6257-40f1-b7a5-568eafc80654
-- title:
--   Adele
-- statement:
--   Definitions and structural lemmas for Adele, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/Adele.lean

import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Filter.Cofinite
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
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
open scoped Polynomial RatFunc WithZero
noncomputable section
namespace GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
def globalAdeleSubmodule : Submodule k (GlobalPlace k F → F) where
  carrier := {a | ∀ᶠ P in cofinite, a P ∈ P.valuationRing}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change ∀ᶠ P in cofinite, a P ∈ P.valuationRing at ha
    change ∀ᶠ P in cofinite, b P ∈ P.valuationRing at hb
    change ∀ᶠ P in cofinite, (a + b) P ∈ P.valuationRing
    exact (ha.and hb).mono fun P hP => P.valuationRing.add_mem _ _ hP.1 hP.2
  smul_mem' c a ha := by
    change ∀ᶠ P in cofinite, a P ∈ P.valuationRing at ha
    change ∀ᶠ P in cofinite, (c • a) P ∈ P.valuationRing
    filter_upwards [ha] with P hP
    rw [Pi.smul_apply, Algebra.smul_def]
    exact P.valuationRing.mul_mem _ _
      ((mem_valuationRing_iff P _).mpr
        (FiniteField.valuation_algebraMap_le_one P.valuation c)) hP
abbrev GlobalAdele := globalAdeleSubmodule (k := k) (F := F)
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
theorem eventually_mem_valuationRing (f : F) :
    ∀ᶠ P : GlobalPlace k F in cofinite, f ∈ P.valuationRing := by
  rw [Filter.eventually_cofinite]
  by_cases hf : f = 0
  · subst f
    simp
  · let u : Fˣ := Units.mk0 f hf
    refine (GlobalPlace.principalDivisor (k := k) (F := F) u).support.finite_toSet.subset ?_
    intro P hP
    change f ∉ P.valuationRing at hP
    change P ∈ (GlobalPlace.principalDivisor (k := k) (F := F) u).support
    apply Finsupp.mem_support_iff.mpr
    rw [GlobalPlace.principalDivisor_apply]
    intro horder
    have horder' : P.order f = 0 := by
      simpa only [u, Units.val_mk0] using horder
    apply hP
    exact (regularAt_iff_mem_valuationRing P f).mp
      ((regularAt_iff_order_nonnegative P hf).mpr (by rw [horder']))
def smulGlobalAdele (x : F) (a : GlobalAdele (k := k) (F := F)) :
    GlobalAdele (k := k) (F := F) :=
  ⟨fun P => x * a.val P, by
    have hx := eventually_mem_valuationRing (k := k) (F := F) x
    have ha := a.property
    change ∀ᶠ P : GlobalPlace k F in cofinite, a.val P ∈ P.valuationRing at ha
    change ∀ᶠ P : GlobalPlace k F in cofinite, x * a.val P ∈ P.valuationRing
    exact (hx.and ha).mono fun P hP =>
      P.valuationRing.mul_mem _ _ hP.1 hP.2⟩
instance : SMul F (GlobalAdele (k := k) (F := F)) :=
  ⟨smulGlobalAdele (k := k) (F := F)⟩
instance : Module F (GlobalAdele (k := k) (F := F)) :=
  Module.ofMinimalAxioms
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_add _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => add_mul _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_assoc _ _ _)
    (fun _ => Subtype.ext <| funext fun _ => one_mul _)
def mulGlobalAdeleLinear (x : F) :
    GlobalAdele (k := k) (F := F) →ₗ[k] GlobalAdele (k := k) (F := F) where
  toFun a := x • a
  map_add' _ _ := smul_add x _ _
  map_smul' c a := by
    ext P
    change x * (c • a.val P) = c • (x * a.val P)
    simp only [Algebra.smul_def]
    ring
def MemGlobalAdeleFilter (D : Divisor (GlobalPlace k F))
    (a : GlobalAdele (k := k) (F := F)) : Prop :=
  ∀ P, P.valuation (a.val P) ≤ WithZero.exp (D P)
def globalAdeleFilter (D : Divisor (GlobalPlace k F)) :
    Submodule k (GlobalAdele (k := k) (F := F)) where
  carrier := {a | MemGlobalAdeleFilter D a}
  zero_mem' := fun P => by simp
  add_mem' {a b} ha hb := by
    intro P
    exact (Valuation.map_add P.valuation (a.val P) (b.val P)).trans
      (max_le (ha P) (hb P))
  smul_mem' c a ha := by
    intro P
    change P.valuation (c • a.val P) ≤ _
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_mul'
      (FiniteField.valuation_algebraMap_le_one P.valuation c) (ha P)).trans_eq
        (one_mul _)
def diagonalAdele : F →ₗ[k] GlobalAdele (k := k) (F := F) where
  toFun f := ⟨fun _ => f, eventually_mem_valuationRing (k := k) (F := F) f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def diagonalAdeleSubmodule : Submodule k (GlobalAdele (k := k) (F := F)) :=
  LinearMap.range (diagonalAdele (k := k) (F := F))
@[nolint unusedArguments]
def globalAdeleFilterWithin {D E : Divisor (GlobalPlace k F)} (_hDE : D ≤ E) :
    Submodule k (globalAdeleFilter (k := k) (F := F) E) :=
  Submodule.comap (globalAdeleFilter (k := k) (F := F) E).subtype
    (globalAdeleFilter (k := k) (F := F) D)
noncomputable def globalAdeleFilterDiffDimension
    (D E : Divisor (GlobalPlace k F)) : ℕ := by
  letI : AddCommGroup (globalAdeleFilter (k := k) (F := F) E) :=
    Submodule.addCommGroup _
  letI : Module k (globalAdeleFilter (k := k) (F := F) E) := Submodule.module _
  exact Module.finrank k
    (globalAdeleFilter (k := k) (F := F) E ⧸
      Submodule.comap (globalAdeleFilter (k := k) (F := F) E).subtype
        (globalAdeleFilter (k := k) (F := F) D))
def zeroGlobalAdele : GlobalAdele (k := k) (F := F) := ⟨0, by simp⟩
noncomputable def globalAdeleUpdate (a : GlobalAdele (k := k) (F := F))
    (P : GlobalPlace k F) (x : F) : GlobalAdele (k := k) (F := F) := by
  classical
  refine ⟨Function.update a.val P x, ?_⟩
  change ∀ᶠ Q : GlobalPlace k F in cofinite,
    Function.update a.val P x Q ∈ Q.valuationRing
  filter_upwards [a.property, Filter.eventually_cofinite_ne P] with Q hQ hQP
  simpa only [Function.update_of_ne hQP] using hQ
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


