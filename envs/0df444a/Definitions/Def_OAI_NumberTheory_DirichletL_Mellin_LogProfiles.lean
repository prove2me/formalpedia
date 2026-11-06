-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
-- name    : OAI_NumberTheory_DirichletL_Mellin_LogProfiles
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:13:34.100764+00:00
-- url     : https://prove2.me/theorems/8f15181d-4fe3-4a3a-a416-fa4e893ed32f
-- title:
--   Log Profiles
-- statement:
--   Definitions and structural lemmas for Log Profiles, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
set_option autoImplicit false
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftMellin
def ExponentialMobiusPowerBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ),
    (23 / 24 : ℝ) < σ → σ < 1 →
      (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
        (fun D : ℝ => D ^ σ)
end ShortDraftMellin
namespace FiniteRingSieve
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
noncomputable local instance logProfilesFintypeMulChar : Fintype (MulChar R ℂ) := Fintype.ofFinite _
attribute [local instance] logProfilesFintypeMulChar
end FiniteRingSieve
namespace FiniteFieldSieve
variable {F : Type*} [Field F] [Fintype F]
end FiniteFieldSieve
namespace ProductResidueSieve
variable {R S : Type*} [CommRing R] [CommRing S]
noncomputable def mulCharProd (χ : MulChar R ℂ) (η : MulChar S ℂ) : MulChar (R × S) ℂ where
  toFun x := χ x.1 * η x.2
  map_one' := by simp
  map_mul' x y := by simp [mul_mul_mul_comm]
  map_nonunit' x hx := by
    rw [Prod.isUnit_iff] at hx
    by_cases h₁ : IsUnit x.1
    · have h₂ : ¬IsUnit x.2 := by tauto
      simp [MulChar.map_nonunit η h₂]
    · simp [MulChar.map_nonunit χ h₁]
noncomputable def addCharProd (ψ : AddChar R ℂ) (φ : AddChar S ℂ) : AddChar (R × S) ℂ where
  toFun x := ψ x.1 * φ x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring
@[simp] theorem mulCharProd_apply (χ : MulChar R ℂ) (η : MulChar S ℂ) (x : R × S) :
    mulCharProd χ η x = χ x.1 * η x.2 := rfl
@[simp] theorem addCharProd_apply (ψ : AddChar R ℂ) (φ : AddChar S ℂ) (x : R × S) :
    addCharProd ψ φ x = ψ x.1 * φ x.2 := rfl
end ProductResidueSieve
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
namespace FourierBridge
noncomputable def logProfile
    (W : ℝ → ℂ) (F : ℝ → ℂ) (R a : ℝ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) : 𝓢(ℝ, ℂ) := by
  let G : ℝ → ℂ := fun y => W y * F (R * Real.exp (a * y))
  have harg : ContDiff ℝ ∞ (fun y : ℝ => R * Real.exp (a * y)) := by
    fun_prop
  have hGs : ContDiff ℝ ∞ G := by
    dsimp [G]
    exact hWs.mul (hFs.comp harg)
  have hGc : HasCompactSupport G := by
    dsimp [G]
    exact hWc.mul_right
  exact hGc.toSchwartzMap hGs
noncomputable def profileDerivativeConstant (n : ℕ) (H CW CF : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * CW *
      ((n - i).factorial * CF * (H ^ 2) ^ (n - i))
noncomputable def profileMomentConstant (K : ℕ) (L H CW CF : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1),
    (1 + L ^ (volume : Measure ℝ).integrablePower) *
      profileDerivativeConstant j H CW CF
noncomputable def coefficientMomentBound (J : ℕ) (C : ℝ) : ℝ :=
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  V * (V * C + (2 : ℝ) ^ (J + p) * (J + p + 1) * V * C)
noncomputable def logPhase (t y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I)
noncomputable def schwartzDerivativeDecayConstant
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) : ℝ :=
  (2 : ℝ) ^ M *
    ∑ i ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 i) F +
        (SchwartzMap.seminorm ℝ M i) F)
end FourierBridge
end OAI


