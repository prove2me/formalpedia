-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:08.910972+00:00
-- url     : https://prove2.me/theorems/783f6132-f874-407a-bff9-ed3ac0214c75
-- title:
--   Res Adm
-- statement:
--   Definitions and structural lemmas for Res Adm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/ResAdm.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R]
abbrev V (R κ : Type) : Type := (κ → R) × (κ → R)
def IsSp {κ : Type} [Fintype κ] (S : V R κ ≃ₗ[R] V R κ) : Prop :=
  ∀ w w', (S w).1 ⬝ᵥ (S w').2 - (S w').1 ⬝ᵥ (S w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2
def ev0 (R κ : Type) [Zero R] : ((κ → R) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ : κ → R => ℂ) 0
def res (R : Type) [Zero R] {κ₁ κ : Type} (j : κ₁ → κ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun y : κ₁ → R => Function.extend j y 0
def boxL (κ : Type) {κ' : Type} (φ₂ : (κ' → R) → ℂ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) where
  toFun φ := boxFun φ φ₂
  map_add' _ _ := funext fun _ => add_mul _ _ _
  map_smul' _ _ := funext fun _ => mul_assoc _ _ _
variable [Invertible (2 : R)]
structure AxB (C : TestClass R) (ψ : AddChar R ℂ) : Prop where
  schr : ∀ (κ : Type) [Fintype κ] (w : V R κ), ∀ φ ∈ C.sp κ, schr ψ w φ ∈ C.sp κ
  ne : ∀ (κ : Type) [Fintype κ], ∃ φ ∈ C.sp κ, φ ≠ 0
  ev0 : ∀ (κ : Type) [Fintype κ], ev0 R κ ∈ C.adm κ
  res : ∀ (κ₁ κ : Type) [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j → ∀ φ ∈ C.sp κ, res R j φ ∈ C.sp κ₁
  res_adm : ∀ (κ₁ κ : Type) [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j → ∀ l ∈ C.adm κ₁,
    l ∘ₗ Chr.res R j ∈ C.adm κ
  box : ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ', boxFun φ₁ φ₂ ∈ C.sp (κ ⊕ κ')
  box_adm : ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₂ ∈ C.sp κ', ∀ l ∈ C.adm (κ ⊕ κ'), l ∘ₗ boxL κ φ₂ ∈ C.adm κ
def AxDelta (C : TestClass R) (ψ : AddChar R ℂ) : Prop :=
  ∀ (κ : Type) [Fintype κ], ∀ l ∈ C.adm κ, (∀ y : κ → R, ∀ φ ∈ C.sp κ, l (schr ψ (0, y) φ) = l φ) →
    ∃ a : ℂ, ∀ φ ∈ C.sp κ, l φ = a * φ 0
def AxImp (C : TestClass R) (ψ : AddChar R ℂ) : Prop :=
  ∀ (κ : Type) [Fintype κ] (S : V R κ ≃ₗ[R] V R κ), IsSp S → ∃ T : Module.End ℂ ((κ → R) → ℂ),
    (∀ φ ∈ C.sp κ, T φ ∈ C.sp κ) ∧ (∀ l ∈ C.adm κ, l ∘ₗ T ∈ C.adm κ) ∧
    (∀ w, ∀ φ ∈ C.sp κ, T (schr ψ w φ) = schr ψ (S w) (T φ)) ∧ ∀ φ ∈ C.sp κ, T φ = 0 → φ = 0
def AxInt (C : TestClass R) : Prop :=
  ∀ (κ : Type) [Fintype κ], ∃ I ∈ C.adm κ, (∃ φ ∈ C.sp κ, I φ ≠ 0) ∧
    (∀ a : κ → R, ∀ φ ∈ C.sp κ, I (fun x => φ (x + a)) = I φ) ∧
    ∀ g : (κ → R) ≃ₗ[R] (κ → R), ∀ φ ∈ C.sp κ, (fun x => φ (g.symm x)) ∈ C.sp κ →
      I (fun x => φ (g.symm x)) = ((C.modu (LinearEquiv.det g) : ℝ) : ℂ) * I φ
def Rel {κ₁ κ : Type} (S : V R κ ≃ₗ[R] V R κ) (j : κ₁ → κ) (w : V R κ) (w₁ : V R κ₁) : Prop :=
  (S w).1 = Function.extend j w₁.1 0 ∧ (S w).2 ∘ j = w₁.2
end PositivityTheory.ThKF0.Chr


