-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_PullHomeoApply
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_PullHomeoApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:01.051103+00:00
-- url     : https://prove2.me/theorems/78bb45cd-7975-441d-908d-11b90b136035
-- title:
--   Pull Homeo Apply
-- statement:
--   Definitions and structural lemmas for Pull Homeo Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/PullHomeoApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GlobalTheory.SplitWeil
namespace PositivityTheory.PfBern.Frob
abbrev Distr (X : Type*) [TopologicalSpace X] : Type _ := Module.Dual ℂ (SB X)
def SupportedIn {X : Type*} [TopologicalSpace X] (D : Distr X) (C : Set X) : Prop :=
  ∀ f : SB X, Function.support (f : X → ℂ) ⊆ Cᶜ → D f = 0
theorem comp_homeo_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {f : Y → ℂ} (hf : f ∈ SB Y) : (fun x => f (e x)) ∈ SB X :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
def pullHomeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    SB Y →ₗ[ℂ] SB X where
  toFun f := ⟨fun x => (f : Y → ℂ) (e x), comp_homeo_mem e f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp]
theorem pullHomeo_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (f : SB Y) (x : X) : ((pullHomeo e f : SB X) : X → ℂ) x = (f : Y → ℂ) (e x) :=
  rfl
section Transl
variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [ContinuousConstSMul G X]
def transl (g : G) : SB X →ₗ[ℂ] SB X :=
  pullHomeo (Homeomorph.smul g⁻¹)
@[simp]
theorem transl_apply (g : G) (f : SB X) (x : X) :
    ((transl g f : SB X) : X → ℂ) x = (f : X → ℂ) (g⁻¹ • x) :=
  rfl
variable (X) in

def eqv (χ : G →* ℂˣ) : Submodule ℂ (Distr X) where
  carrier := {D | ∀ (g : G) (f : SB X), D (transl g f) = (χ g : ℂ) * D f}
  add_mem' {D E} hD hE g f := by
    simp only [LinearMap.add_apply, hD g f, hE g f, mul_add]
  zero_mem' g f := by simp
  smul_mem' c D hD g f := by
    simp only [LinearMap.smul_apply, hD g f, smul_eq_mul]
    ring
end Transl
section Fibre
variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
  [ContinuousConstSMul G X] {H : Subgroup G}
abbrev Fib (p : X → G ⧸ H) : Type _ := {x : X // p x = ((1 : G) : G ⧸ H)}
omit [TopologicalSpace X] [ContinuousConstSMul G X] in

theorem smul_mem_fib {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (h : H)
    (z : Fib p) : p ((h : G) • z.1) = ((1 : G) : G ⧸ H) := by
  rw [hp, z.2, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
  simp [H.inv_mem h.2]
def fibSmul {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (h : H) (z : Fib p) :
    Fib p :=
  ⟨(h : G) • z.1, smul_mem_fib hp h z⟩
@[simp]
theorem fibSmul_val {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (h : H)
    (z : Fib p) : (fibSmul hp h z).1 = (h : G) • z.1 :=
  rfl
def fibHomeo {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (h : H) :
    Fib p ≃ₜ Fib p where
  toFun := fibSmul hp h
  invFun := fibSmul hp h⁻¹
  left_inv z := Subtype.ext (by simp [smul_smul])
  right_inv z := Subtype.ext (by simp [smul_smul])
  continuous_toFun := ((continuous_const_smul (h : G)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_const_smul ((h⁻¹ : H) : G)).comp continuous_subtype_val).subtype_mk _
def translF {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (h : H) :
    SB (Fib p) →ₗ[ℂ] SB (Fib p) :=
  pullHomeo (fibHomeo hp h⁻¹)
@[simp]
theorem translF_apply {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (h : H)
    (φ : SB (Fib p)) (z : Fib p) :
    ((translF hp h φ : SB (Fib p)) : Fib p → ℂ) z = (φ : Fib p → ℂ) (fibSmul hp h⁻¹ z) :=
  rfl
def eqvF {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (ψ : H →* ℂˣ) :
    Submodule ℂ (Distr (Fib p)) where
  carrier := {D | ∀ (h : H) (φ : SB (Fib p)), D (translF hp h φ) = (ψ h : ℂ) * D φ}
  add_mem' {D E} hD hE h φ := by
    simp only [LinearMap.add_apply, hD h φ, hE h φ, mul_add]
  zero_mem' h φ := by simp
  smul_mem' c D hD h φ := by
    simp only [LinearMap.smul_apply, hD h φ, smul_eq_mul]
    ring
end Fibre
def IsUnimod (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] : Prop :=
  ∀ g : G, MeasureTheory.Measure.modularCharacter g = 1
end PositivityTheory.PfBern.Frob


