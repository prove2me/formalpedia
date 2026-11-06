-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:30:47.635036+00:00
-- url     : https://prove2.me/theorems/bcdb56a5-4a40-43c6-8d0a-13b7d0af953f
-- title:
--   Adele Weil Differential
-- statement:
--   Definitions and structural lemmas for Adele Weil Differential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean

import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_Nonnegative_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleQuotient_finite
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
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
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance globalAdeleWeilAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
attribute [local instance] globalAdeleWeilAlgebra
local instance globalAdeleWeilScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
attribute [local instance] globalAdeleWeilScalarTower
namespace GlobalPlace
local instance globalAdeleWeilRiemannRochFiniteDimensional
    (D : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule D) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
attribute [local instance] globalAdeleWeilRiemannRochFiniteDimensional
variable [IsFullConstantField k F]
instance globalAdeleIsScalarTower :
    IsScalarTower k F (GlobalAdele (k := k) (F := F)) :=
  ⟨fun c x a => Subtype.ext <| funext fun P => by
    change (c • x) * a.val P = c • (x * a.val P)
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]⟩
structure GlobalAdeleWeilDifferential where
  /-- The underlying constant-field linear functional on intrinsic adeles. -/
  toFun : GlobalAdele (k := k) (F := F) →ₗ[k] k
  /-- A divisor filtration piece plus the diagonal lies in its kernel. -/
  vanishes_on : ∃ D : Divisor (GlobalPlace k F),
    ∀ a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F) D,
      toFun a = 0
namespace GlobalAdeleWeilDifferential
variable {k F}
def IsNonzero (omega : GlobalAdeleWeilDifferential k F) : Prop :=
  omega.toFun ≠ 0
end GlobalAdeleWeilDifferential
def globalAdeleDifferentialSpace
    (D : Divisor (GlobalPlace k F)) :
    Submodule k (GlobalAdele (k := k) (F := F) →ₗ[k] k) where
  carrier := {psi | ∀ a ∈ globalAdeleFilterAddDiagonal
    (k := k) (F := F) D, psi a = 0}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    intro a ha
    simp only [LinearMap.add_apply, hf a ha, hg a ha, add_zero]
  smul_mem' c f hf := by
    intro a ha
    simp only [LinearMap.smul_apply, RingHom.id_apply, hf a ha, smul_zero]
theorem globalAdeleDifferentialSpace_eq_dualAnnihilator
    (D : Divisor (GlobalPlace k F)) :
    globalAdeleDifferentialSpace (k := k) (F := F) D =
      (globalAdeleFilterAddDiagonal (k := k) (F := F) D).dualAnnihilator := by
  ext psi
  rw [Submodule.mem_dualAnnihilator]
  rfl
theorem globalAdeleDifferentialSpace_finite
    (D : Divisor (GlobalPlace k F)) :
    Module.Finite k (globalAdeleDifferentialSpace (k := k) (F := F) D) := by
  letI : Module.Finite k (GlobalAdeleQuotient (k := k) (F := F) D) :=
    globalAdeleQuotient_finite
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  rw [globalAdeleDifferentialSpace_eq_dualAnnihilator]
  exact Module.Finite.equiv
    (Submodule.dualQuotEquivDualAnnihilator
      (globalAdeleFilterAddDiagonal (k := k) (F := F) D))
local instance globalAdeleDifferentialSpaceFinite
    (D : Divisor (GlobalPlace k F)) :
    Module.Finite k (globalAdeleDifferentialSpace (k := k) (F := F) D) :=
  globalAdeleDifferentialSpace_finite
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
attribute [local instance] globalAdeleDifferentialSpaceFinite
theorem valuation_eq_exp_neg_principalDivisor
    (x : Fˣ) (P : GlobalPlace k F) :
    P.valuation (x : F) = WithZero.exp
      (-(principalDivisor (k := k) (F := F) x P)) := by
  rw [principalDivisor_apply, order, neg_neg,
    WithZero.exp_log ((P.valuation).ne_zero_iff.mpr x.ne_zero)]
theorem mul_mem_globalAdeleFilterAddDiagonal
    (x : Fˣ) (D : Divisor (GlobalPlace k F))
    {a : GlobalAdele (k := k) (F := F)}
    (ha : a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F)
      (D + principalDivisor (k := k) (F := F) x)) :
    (x : F) • a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F) D := by
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  refine Submodule.mem_sup.mpr ⟨(x : F) • a₁, ?_, (x : F) • a₂, ?_,
    (smul_add (x : F) a₁ a₂).symm⟩
  · intro P
    change P.valuation ((x : F) * a₁.val P) ≤ WithZero.exp (D P)
    rw [map_mul, valuation_eq_exp_neg_principalDivisor]
    have haP := ha₁ P
    simp only [Finsupp.add_apply, WithZero.exp_add] at haP
    calc
      WithZero.exp (-(principalDivisor (k := k) (F := F) x P)) *
          P.valuation (a₁.val P) ≤
          WithZero.exp (-(principalDivisor (k := k) (F := F) x P)) *
            (WithZero.exp (D P) *
              WithZero.exp (principalDivisor (k := k) (F := F) x P)) :=
        mul_le_mul_right haP _
      _ = WithZero.exp (D P) := by
        rw [← WithZero.exp_add, ← WithZero.exp_add]
        congr 1
        ring
  · rcases ha₂ with ⟨f, rfl⟩
    exact ⟨(x : F) * f, by ext P; rfl⟩
namespace GlobalAdeleWeilDifferential
variable {k F}
noncomputable def smulWeil (x : F) (omega : GlobalAdeleWeilDifferential k F) :
    GlobalAdeleWeilDifferential k F := by
  by_cases hx : x = 0
  · exact ⟨0, ⟨0, by simp⟩⟩
  let xu : Fˣ := Units.mk0 x hx
  refine ⟨omega.toFun.comp (mulGlobalAdeleLinear (k := k) (F := F) x), ?_⟩
  obtain ⟨D, hD⟩ := omega.vanishes_on
  refine ⟨D + principalDivisor (k := k) (F := F) xu, fun a ha => hD _ ?_⟩
  change x • a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F) D
  simpa only [xu, Units.val_mk0] using
    (mul_mem_globalAdeleFilterAddDiagonal
      (k := k) (F := F) xu D ha)
@[simp]
theorem smulWeil_toFun_apply (x : F)
    (omega : GlobalAdeleWeilDifferential k F)
    (a : GlobalAdele (k := k) (F := F)) :
    (smulWeil x omega).toFun a = omega.toFun (x • a) := by
  by_cases hx : x = 0
  · simp [smulWeil, hx]
  · simp only [smulWeil, hx, ↓reduceDIte, LinearMap.comp_apply]
    congr 1
instance : Zero (GlobalAdeleWeilDifferential k F) :=
  ⟨⟨0, ⟨0, by simp⟩⟩⟩
instance : Add (GlobalAdeleWeilDifferential k F) where
  add omega eta := ⟨omega.toFun + eta.toFun, by
    obtain ⟨Domega, homega⟩ := omega.vanishes_on
    obtain ⟨Deta, heta⟩ := eta.vanishes_on
    refine ⟨Domega ⊓ Deta, fun a ha => ?_⟩
    have hleft : globalAdeleFilterAddDiagonal (k := k) (F := F)
        (Domega ⊓ Deta) ≤
        globalAdeleFilterAddDiagonal (k := k) (F := F) Domega := by
      exact sup_le_sup
        (globalAdeleFilter_mono (k := k) (F := F) inf_le_left) le_rfl
    have hright : globalAdeleFilterAddDiagonal (k := k) (F := F)
        (Domega ⊓ Deta) ≤
        globalAdeleFilterAddDiagonal (k := k) (F := F) Deta := by
      exact sup_le_sup
        (globalAdeleFilter_mono (k := k) (F := F) inf_le_right) le_rfl
    simp only [LinearMap.add_apply, homega a (hleft ha), heta a (hright ha),
      add_zero]⟩
@[ext]
theorem ext {omega eta : GlobalAdeleWeilDifferential k F}
    (h : omega.toFun = eta.toFun) : omega = eta := by
  cases omega
  cases eta
  cases h
  rfl
instance : Neg (GlobalAdeleWeilDifferential k F) where
  neg omega := ⟨-omega.toFun, by
    obtain ⟨D, hD⟩ := omega.vanishes_on
    exact ⟨D, fun a ha => by simp only [LinearMap.neg_apply, hD a ha, neg_zero]⟩⟩
instance : AddCommGroup (GlobalAdeleWeilDifferential k F) where
  add_assoc _ _ _ := ext (add_assoc _ _ _)
  zero_add _ := ext (zero_add _)
  add_zero _ := ext (add_zero _)
  add_comm _ _ := ext (add_comm _ _)
  nsmul := nsmulRec
  nsmul_zero _ := ext rfl
  nsmul_succ _ _ := ext rfl
  neg := Neg.neg
  neg_add_cancel omega := ext (neg_add_cancel omega.toFun)
  sub := fun omega eta => omega + -eta
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec
@[simp]
theorem add_toFun (omega eta : GlobalAdeleWeilDifferential k F) :
    (omega + eta).toFun = omega.toFun + eta.toFun := rfl
noncomputable instance : SMul F (GlobalAdeleWeilDifferential k F) :=
  ⟨smulWeil⟩
noncomputable instance : Module F (GlobalAdeleWeilDifferential k F) :=
  Module.ofMinimalAxioms
    (fun x omega eta => by
      apply ext
      ext a
      change (smulWeil x (omega + eta)).toFun a =
        ((smulWeil x omega).toFun + (smulWeil x eta).toFun) a
      rw [smulWeil_toFun_apply]
      change (omega.toFun + eta.toFun) (x • a) =
        (smulWeil x omega).toFun a + (smulWeil x eta).toFun a
      rw [LinearMap.add_apply, smulWeil_toFun_apply, smulWeil_toFun_apply])
    (fun x y omega => by
      apply ext
      ext a
      change (smulWeil (x + y) omega).toFun a =
        ((smulWeil x omega).toFun + (smulWeil y omega).toFun) a
      rw [smulWeil_toFun_apply]
      change omega.toFun ((x + y) • a) =
        (smulWeil x omega).toFun a + (smulWeil y omega).toFun a
      rw [smulWeil_toFun_apply, smulWeil_toFun_apply, add_smul, map_add])
    (fun x y omega => by
      apply ext
      ext a
      change (smulWeil (x * y) omega).toFun a =
        (smulWeil x (smulWeil y omega)).toFun a
      rw [smulWeil_toFun_apply, smulWeil_toFun_apply,
        smulWeil_toFun_apply, ← mul_smul, mul_comm x y])
    (fun omega => by
      apply ext
      ext a
      change (smulWeil 1 omega).toFun a = omega.toFun a
      rw [smulWeil_toFun_apply, one_smul])
end GlobalAdeleWeilDifferential
def globalAdeleVanishingDivisors
    (omega : GlobalAdeleWeilDifferential k F) :
    Set (Divisor (GlobalPlace k F)) :=
  {D | ∀ a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F) D,
    omega.toFun a = 0}
theorem le_add_principal_of_mem_riemannRochSubmodule'
    {D₀ D₁ : Divisor (GlobalPlace k F)} {f : F} (hf : f ≠ 0)
    (hmem : f ∈ riemannRochSubmodule (D₁ - D₀)) :
    D₀ ≤ D₁ + principalDivisor (k := k) (F := F) (Units.mk0 f hf) := by
  intro P
  have hP :=
    (mem_riemannRochSubmodule_iff_order_add_nonnegative (D₁ - D₀) hf).mp
      hmem P
  simp only [Finsupp.sub_apply] at hP
  rw [Finsupp.add_apply, principalDivisor_apply]
  simp only [Units.val_mk0]
  omega
theorem smulWeil_toFun_mem_globalAdeleDifferentialSpace
    (omega : GlobalAdeleWeilDifferential k F)
    {D₀ : Divisor (GlobalPlace k F)}
    (hD₀ : D₀ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    {E : Divisor (GlobalPlace k F)} (f : riemannRochSubmodule E) :
    (GlobalAdeleWeilDifferential.smulWeil (f : F) omega).toFun ∈
      globalAdeleDifferentialSpace (k := k) (F := F) (D₀ - E) := by
  intro a ha
  rw [GlobalAdeleWeilDifferential.smulWeil_toFun_apply]
  by_cases hf : (f : F) = 0
  · rw [hf, zero_smul, map_zero]
  · have hmem : (f : F) ∈ riemannRochSubmodule
        (D₀ - (D₀ - E)) := by
      rw [sub_sub_cancel]
      exact f.property
    have hdivle : D₀ - E ≤ D₀ +
        principalDivisor (k := k) (F := F) (Units.mk0 (f : F) hf) :=
      le_add_principal_of_mem_riemannRochSubmodule'
        (k := k) (F := F) hf hmem
    have ha' : a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F)
        (D₀ + principalDivisor (k := k) (F := F)
          (Units.mk0 (f : F) hf)) :=
      (sup_le_sup (globalAdeleFilter_mono (k := k) (F := F) hdivle)
        le_rfl) ha
    exact hD₀ _ (by
      simpa only [Units.val_mk0] using
        (mul_mem_globalAdeleFilterAddDiagonal
          (k := k) (F := F) (Units.mk0 (f : F) hf) D₀ ha'))
noncomputable def globalAdeleSmulIntoDifferentialSpace
    (omega : GlobalAdeleWeilDifferential k F)
    {D₀ : Divisor (GlobalPlace k F)}
    (hD₀ : D₀ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    (E : Divisor (GlobalPlace k F)) :
    riemannRochSubmodule E →ₗ[k]
      globalAdeleDifferentialSpace (k := k) (F := F) (D₀ - E) where
  toFun f := ⟨(GlobalAdeleWeilDifferential.smulWeil (f : F) omega).toFun,
    smulWeil_toFun_mem_globalAdeleDifferentialSpace
      (k := k) (F := F) omega hD₀ f⟩
  map_add' f g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change (GlobalAdeleWeilDifferential.smulWeil
        ((f : F) + (g : F)) omega).toFun a =
      (GlobalAdeleWeilDifferential.smulWeil (f : F) omega).toFun a +
        (GlobalAdeleWeilDifferential.smulWeil (g : F) omega).toFun a
    rw [GlobalAdeleWeilDifferential.smulWeil_toFun_apply,
      GlobalAdeleWeilDifferential.smulWeil_toFun_apply,
      GlobalAdeleWeilDifferential.smulWeil_toFun_apply, add_smul, map_add]
  map_smul' c f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change (GlobalAdeleWeilDifferential.smulWeil
        (c • (f : F)) omega).toFun a =
      c • (GlobalAdeleWeilDifferential.smulWeil (f : F) omega).toFun a
    rw [GlobalAdeleWeilDifferential.smulWeil_toFun_apply,
      GlobalAdeleWeilDifferential.smulWeil_toFun_apply,
      Algebra.smul_def, mul_smul, algebraMap_smul, map_smul]
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


