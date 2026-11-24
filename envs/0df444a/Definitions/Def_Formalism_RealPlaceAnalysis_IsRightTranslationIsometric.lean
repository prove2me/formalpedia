-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_IsRightTranslationIsometric
-- name    : Formalism_RealPlaceAnalysis_IsRightTranslationIsometric
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:39:35.558284+00:00
-- url     : https://prove2.me/theorems/40c25f58-25dc-43f2-a2e9-273a489d3c93
-- title:
--   Is Right Translation Isometric
-- statement:
--   Definitions and structural lemmas for Is Right Translation Isometric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/IsRightTranslationIsometric.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace ENNReal
noncomputable section
namespace Formalism.REAL
def eqvSub {n : ℕ} {ε : Fin n → Bool} (S : Subgroup (UJ ε)) (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (σ : S → E →ₗᵢ[ℂ] E) :
    Submodule ℂ (UJ ε → E) where
  carrier := {F | ∀ (s : S) (g : UJ ε), F ((s : UJ ε) * g) = σ s (F g)}
  add_mem' := by
    intro F F' hF hF' s g
    simp [hF s g, hF' s g]
  zero_mem' := by
    intro s g
    simp
  smul_mem' := by
    intro c F hF s g
    simp [hF s g]
structure HidaSetting (n : ℕ) (ε : Fin n → Bool) where
  E : Type
  [ng : NormedAddCommGroup E]
  [ips : InnerProductSpace ℂ E]
  [cs : CompleteSpace E]
  S : Subgroup (UJ ε)
  σ : S → E →ₗᵢ[ℂ] E
  ν : Measure (UJ ε)
attribute [instance] HidaSetting.ng HidaSetting.ips HidaSetting.cs
def HidaSetting.adm {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) : Submodule ℂ (UJ ε → P.E) :=
  eqvSub P.S P.E P.σ
def Rs {n : ℕ} {ε : Fin n → Bool} {E : Type*} (h : UJ ε) (F : UJ ε → E) : UJ ε → E :=
  fun g => F (g * h)
def IsRightTranslationIsometric {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) : Prop :=
  ∀ F ∈ P.adm, StronglyMeasurable F → ∀ h : UJ ε,
    ∫⁻ g, ‖Rs h F g‖ₑ ^ 2 ∂P.ν = ∫⁻ g, ‖F g‖ₑ ^ 2 ∂P.ν
def IsSettingL2 {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) (F : UJ ε → P.E) : Prop :=
  F ∈ P.adm ∧ StronglyMeasurable F ∧ ∫⁻ g, ‖F g‖ₑ ^ 2 ∂P.ν < ∞
def sInner {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) (F F' : UJ ε → P.E) : ℂ :=
  ∫ g, ⟪F g, F' g⟫_ℂ ∂P.ν
def Rconv {n : ℕ} {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (φ : UJ ε → ℂ) (F : UJ ε → E) : UJ ε → E :=
  fun g => ∫ h, φ h • F (g * h) ∂(muG ε)
def settingG {n : ℕ} (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : HidaSetting n ε :=
  { E := E, S := ⊥, σ := fun _ => LinearIsometry.id, ν := muG ε }
def settingQ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (UJ ε)) (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (σ : S → E →ₗᵢ[ℂ] E) (ph : UJ ε → ℝ≥0∞) : HidaSetting n ε :=
  { E := E, S := S, σ := σ, ν := (muG ε).withDensity ph }
def LogLogRegularisationSetting : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
    IsRightTranslationIsometric (settingG ε E)
def QuotientSetting : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (UJ ε)) (muS : Measure S) (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (σ : S → E →ₗᵢ[ℂ] E) (ph : UJ ε → ℝ≥0∞),
    SFinite muS → muS.IsMulLeftInvariant → Measure.map (fun s : S => s⁻¹) muS = muS → Measurable ph →
    (∀ᵐ g ∂(muG ε), ∫⁻ s, ph ((s : UJ ε) * g) ∂muS = 1) →
    IsRightTranslationIsometric (settingQ ε S E σ ph)
def SettingHilbertFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : HidaSetting n ε), IsRightTranslationIsometric P →
    ∀ (F F' : UJ ε → P.E) (h : UJ ε) (c : ℂ), IsSettingL2 P F → IsSettingL2 P F' →
      IsSettingL2 P (Rs h F) ∧ IsSettingL2 P (F + F') ∧ IsSettingL2 P (c • F) ∧
      Integrable (fun g => ⟪F g, F' g⟫_ℂ) P.ν ∧
      sInner P F F = (((∫⁻ g, ‖F g‖ₑ ^ 2 ∂P.ν).toReal : ℝ) : ℂ) ∧
      sInner P F' F = starRingEnd ℂ (sInner P F F') ∧
      ‖sInner P F F'‖ ^ 2 ≤ (sInner P F F).re * (sInner P F' F').re ∧
      sInner P (Rs h F) (Rs h F') = sInner P F F'
def RconvAdm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : HidaSetting n ε) (φ : UJ ε → ℂ) (F : UJ ε → P.E),
    F ∈ P.adm → Rconv φ F ∈ P.adm
end Formalism.REAL


