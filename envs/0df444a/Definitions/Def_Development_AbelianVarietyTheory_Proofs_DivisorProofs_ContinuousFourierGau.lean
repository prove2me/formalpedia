-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:41.344199+00:00
-- url     : https://prove2.me/theorems/2c986030-d000-4c96-a26b-a56e88111e47
-- title:
--   Continuous Fourier Gau
-- statement:
--   Definitions and structural lemmas for Continuous Fourier Gau, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousFourierGau.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
namespace GlobalTheory.RealWeil
section General
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
def gau (u : V) : ℂ := cexp (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2)
def IsHeis (om : V → V → ℝ) (ρ : V → B →L[ℂ] B) : Prop :=
  (∀ f, ρ 0 f = f) ∧ (∀ u v f, ρ u (ρ v f) = cexp (π * I * (om u v : ℂ)) • ρ (u + v) f) ∧
    (∀ u f, ‖ρ u f‖ = ‖f‖) ∧ ∀ f, Continuous fun u => ρ u f
def Sm (ρ : V → B →L[ℂ] B) (f : B) : Prop := ContDiff ℝ ∞ fun v => ρ v f
def IsOsc (ρ : V → B →L[ℂ] B) {G : Type} [Group G] (k : G → V → V) (Ω : G → B → B) : Prop :=
  (∀ g f f', Sm ρ f → Sm ρ f' → Ω g (f + f') = Ω g f + Ω g f') ∧
  (∀ g (a : ℂ) f, Sm ρ f → Ω g (a • f) = a • Ω g f) ∧
  (∀ g f, Sm ρ f → Sm ρ (Ω g f)) ∧
  (∀ f, Sm ρ f → Ω 1 f = f) ∧
  (∀ g g' f, Sm ρ f → Ω (g * g') f = Ω g (Ω g' f)) ∧
  (∀ g v f, Sm ρ f → Ω g (ρ v f) = ρ (k g v) (Ω g f)) ∧
  (∀ g (A : B →L[ℂ] B), (∀ v f, A (ρ v f) = ρ v (A f)) → ∀ f, Sm ρ f → Ω g (A f) = A (Ω g f)) ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H),
    (∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) → ∀ g f, Sm ρ f → ‖Φ (Ω g f)‖ = ‖Φ f‖
theorem continuous_gau : Continuous (gau : V → ℂ) := by unfold gau; fun_prop
end General
def dP {ι : Type} [Fintype ι] [DecidableEq ι] (s g : Matrix ι ι ℂ) : ℂ :=
  ((1 / 2 : ℂ) • ((1 + s) * g) + (1 / 2 : ℂ) • (1 - s)).det
section Inner
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
def omJ (J : V ≃ₗᵢ[ℝ] V) (x y : V) : ℝ := ⟪x, J y⟫
def lam (g : V → V) : ℂ := ∫ u, gau u * gau (g u)
def mu (J : V ≃ₗᵢ[ℝ] V) (g₁ g₂ : V → V) : ℂ :=
  ∫ u, ∫ v, gau u * gau v * (cexp (π * I * (omJ J (g₁ u) (g₂ v) : ℂ)) * gau (g₁ u + g₂ v))
theorem integrable_gau : Integrable (gau : V → ℂ) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (π / 2 : ℂ)) (by simpa using Real.pi_pos) 0 0
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [gau]
variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
omit [CompleteSpace B] in
theorem IsHeis.integrable (h : IsHeis om ρ) (f : B) : Integrable fun u => gau u • ρ u f := by
  refine Integrable.mono' ((integrable_gau (V := V)).norm.mul_const ‖f‖)
    (continuous_gau.smul (h.2.2.2 f)).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_smul, h.2.2.1]
def proj (h : IsHeis om ρ) : B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u, gau u • ρ u f
      map_add' := fun f f' => by
        rw [← integral_add (h.integrable f) (h.integrable f')]
        simp only [map_add, smul_add]
      map_smul' := fun a f => by
        rw [RingHom.id_apply, ← integral_smul]
        simp only [map_smul, smul_comm a] }
    (∫ u : V, ‖gau u‖) fun f => by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp only [norm_smul, h.2.2.1]
      rw [integral_mul_const]
def Good (h : IsHeis om ρ) (f : B) : Prop := ∀ n : ℕ, Integrable fun w => ‖w‖ ^ n * ‖proj h (ρ (-w) f)‖
variable {J : V ≃ₗᵢ[ℝ] V}
end Inner
end GlobalTheory.RealWeil
end


