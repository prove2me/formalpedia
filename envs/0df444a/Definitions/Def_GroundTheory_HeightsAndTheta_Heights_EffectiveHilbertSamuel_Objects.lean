-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Objects
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Objects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:11.590733+00:00
-- url     : https://prove2.me/theorems/45cce93f-04fc-4aa2-a860-71744f0f2473
-- title:
--   Objects
-- statement:
--   Definitions and structural lemmas for Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/Objects.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.EffectiveHS
open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal
noncomputable section
variable {D : ℕ} {U : Type} [TopologicalSpace U]
def jac (A : FinHolAtlas D U) (j k : Fin A.n) (x : U) : ℂ :=
  LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) (A.chart j x) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
def topSections (A : FinHolAtlas D U) (L₂ L : HolLineBundle A) (m : ℕ) :
    Submodule ℂ (Fin A.n → U → ℂ) where
  carrier := {u | (∀ j, A.HoloOn (A.chart j).source (u j)) ∧
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
      u j x = jac A j k x * L₂.g j k x * L.g j k x ^ m * u k x) ∧
    ∀ j, ∀ x ∉ (A.chart j).source, u j x = 0}
  add_mem' := by
    rintro f f' ⟨hf, hc, hz⟩ ⟨hf', hc', hz'⟩
    refine ⟨fun j k => (hf j k).add (hf' j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.add_apply, hc j k x hx, hc' j k x hx]; ring
    · simp [hz j x hx, hz' j x hx]
  zero_mem' := by
    refine ⟨fun j k => ?_, fun j k x _ => by simp, fun j x _ => rfl⟩
    exact analyticOnNhd_const
  smul_mem' := by
    rintro c f ⟨hf, hc, hz⟩
    refine ⟨fun j k => analyticOnNhd_const.mul (hf j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hc j k x hx]; ring
    · simp [hz j x hx]
def piece (A : FinHolAtlas D U) (j : Fin A.n) : Set (Fin D → ℂ) :=
  {y | y ∈ (A.chart j).target ∧ ∀ k < j, (A.chart j).symm y ∉ (A.chart k).source}
def chartIntegral (A : FinHolAtlas D U) (f : Fin A.n → U → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, ∫⁻ y in piece A j, f j ((A.chart j).symm y)
def topNormSq (A : FinHolAtlas D U) (ψ : Fin A.n → U → ℝ) (F : Fin A.n → U → ℂ) : ℝ≥0∞ :=
  chartIntegral A fun j x => ENNReal.ofReal (2 ^ D * ‖F j x‖ ^ 2 * Real.exp (-ψ j x))
def fsWeight {N : ℕ} {A : FinHolAtlas D U} (e : Fin N → Fin A.n → U → ℂ) (j : Fin A.n) (x : U) :
    ℝ :=
  Real.log (∑ i, ‖e i j x‖ ^ 2)
def NoCommonZero {N : ℕ} (A : FinHolAtlas D U) (e : Fin N → Fin A.n → U → ℂ) : Prop :=
  ∀ x, ∃ i, e i (chartIdx A x) x ≠ 0
def lin {N : ℕ} {A : FinHolAtlas D U} (e : Fin N → Fin A.n → U → ℂ) (c : Fin N → ℂ) :
    Fin A.n → U → ℂ :=
  ∑ k, c k • e k
def zeroSet (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) : Set U :=
  {x | ∀ i, s i (chartIdx A x) x = 0}
def sJacMap (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (c : Fin A.n) (x : U) :
    (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) :=
  fderiv ℂ (fun z i => s i c ((A.chart c).symm z)) (A.chart c x)
def sJac (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (c : Fin A.n) (x : U) : ℂ :=
  LinearMap.det (sJacMap A s c x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
def IsNondeg (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) : Prop :=
  ∀ x ∈ zeroSet A s, sJac A s (chartIdx A x) x ≠ 0
def res (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (F : Fin A.n → U → ℂ) (x : U) : ℂ :=
  F (chartIdx A x) x / sJac A s (chartIdx A x) x
def sNormSq (A : FinHolAtlas D U) (S : Set U) (ψ : Fin A.n → U → ℝ) (g : U → ℂ) : ℝ :=
  ∑ᶠ x ∈ S, ‖g x‖ ^ 2 * Real.exp (-ψ (chartIdx A x) x)
def FLBound {N : ℕ} (A : FinHolAtlas D U) (e : Fin N → Fin A.n → U → ℂ)
    (s : Fin D → Fin A.n → U → ℂ) : Prop :=
  ∀ V : Set U, IsOpen V → zeroSet A s ⊆ V → ∃ C : ℝ, ∀ x ∉ V,
    ∑ k, ‖e k (chartIdx A x) x‖ ^ 2 ≤ C * ∑ i, ‖s i (chartIdx A x) x‖ ^ 2
def IsAlgCover (A : FinHolAtlas D U) : Prop :=
  ∃ (MS : Set U) (z : U → Fin D → ℂ) (Δ : MvPolynomial (Fin D) ℂ), IsOpen MS ∧ Δ ≠ 0 ∧
    (∀ i, A.HoloOn MS fun x => z x i) ∧
    (∀ x ∈ MS, MvPolynomial.eval (z x) Δ ≠ 0) ∧
    IsCoveringMapOn (fun p : MS => z p) {y | MvPolynomial.eval y Δ ≠ 0} ∧
    (∀ y, MvPolynomial.eval y Δ ≠ 0 → ((fun p : MS => z p) ⁻¹' {y}).Finite) ∧
    ∀ j, ∃ f : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ f (A.chart j).target ∧
      interior {y | y ∈ (A.chart j).target ∧ f y = 0} = ∅ ∧
      ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ MS → f y = 0
structure TwistWeight (A : FinHolAtlas D U) (L₂ L : HolLineBundle A) (m : ℕ) where

  φ : Fin A.n → U → ℝ
  smooth : ∀ j, A.SmoothOn (A.chart j).source (φ j)
  compat : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
    φ j x = φ k x + Real.log (‖L₂.g j k x‖ ^ 2) + m * Real.log (‖L.g j k x‖ ^ 2)
  psh : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w : Fin D → ℂ, 0 ≤ levi (φ j ∘ (A.chart j).symm) y w
def Vnat (A : FinHolAtlas D U) (L₂ L : HolLineBundle A) (φA φ : Fin A.n → U → ℝ) (j : ℕ) :
    Set (Fin A.n → U → ℂ) :=
  {F | F ∈ topSections A L₂ L (D + j) ∧ topNormSq A (fun k x => φA k x + j * φ k x) F < ⊤}
def IsFil (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (F : Fin A.n → U → ℂ) (a : ℕ) :
    Prop :=
  ∀ x ∈ zeroSet A s, ∀ k < a, iteratedFDeriv ℂ k (F (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm)
    (A.chart (chartIdx A x) x) = 0
def SymEq (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (F : Fin A.n → U → ℂ) (a : ℕ)
    (g : (Fin D → ℕ) → U → ℂ) : Prop :=
  ∀ x ∈ zeroSet A s, ∀ w : Fin D → ℂ,
    iteratedFDeriv ℂ a (F (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm)
        (A.chart (chartIdx A x) x) (fun _ => w) / (a.factorial : ℂ) =
      sJac A s (chartIdx A x) x * ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        (∏ i, (sJacMap A s (chartIdx A x) x w i) ^ α i) * g α x
def sPow {A : FinHolAtlas D U} (s : Fin D → Fin A.n → U → ℂ) (α : Fin D → ℕ) :
    Fin A.n → U → ℂ :=
  ∏ i, s i ^ α i
def Pspace {A : FinHolAtlas D U} (s : Fin D → Fin A.n → U → ℂ)
    (VD : Submodule ℂ (Fin A.n → U → ℂ)) (T : ℕ) : Submodule ℂ (Fin A.n → U → ℂ) :=
  Submodule.span ℂ {F | ∃ α ∈ Finset.Nat.antidiagonalTuple D (T - D), ∃ h ∈ VD, F = sPow s α * h}
def Vpp {N : ℕ} {A : FinHolAtlas D U} (e : Fin N → Fin A.n → U → ℂ)
    (s : Fin D → Fin A.n → U → ℂ) (V₀ VD : Submodule ℂ (Fin A.n → U → ℂ)) (T : ℕ) :
    Submodule ℂ (Fin A.n → U → ℂ) :=
  Submodule.span ℂ {F | ∃ (α : Fin D → ℕ) (j : ℕ) (ι : Fin j → Fin N), ∃ m ∈ V₀,
      ∑ i, α i + j = T ∧ ∑ i, α i ≤ T - D - 1 ∧ F = sPow s α * (∏ l, e (ι l)) * m} ⊔
    Pspace s VD T
def rSq {N : ℕ} (c : Fin D → Fin N → ℂ) : ℝ := ∑ i, ∑ k, ‖c i k‖ ^ 2
def wtNormSq {N : ℕ} (A : FinHolAtlas D U) (c : Fin D → Fin N → ℂ) (S : Set U)
    (ψ : Fin A.n → U → ℝ) (a : ℕ) (g : (Fin D → ℕ) → U → ℂ) : ℝ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple D a, (∏ i, (∑ k, ‖c i k‖ ^ 2) ^ α i) * sNormSq A S ψ (g α)
end
end GroundTheory.Heights₂.Heights.EffectiveHS


