-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:30.525044+00:00
-- url     : https://prove2.me/theorems/17d0faa5-4114-48d1-a2dc-3ad0762b4e19
-- title:
--   Bergman Objects
-- statement:
--   Definitions and structural lemmas for Bergman Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanObjects.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X]
structure HolLineBundle (A : FinHolAtlas D X) where

  g : Fin A.n → Fin A.n → X → ℂ
  holo : ∀ j k, A.HoloOn ((A.chart j).source ∩ (A.chart k).source) (g j k)
  ne_zero : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, g j k x ≠ 0
  cocycle : ∀ j k l, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source ∩ (A.chart l).source,
    g j l x = g j k x * g k l x
namespace HolLineBundle
variable {A : FinHolAtlas D X} (L : HolLineBundle A)
def sections (n : ℕ) : Submodule ℂ (Fin A.n → X → ℂ) where
  carrier := {f | (∀ j, A.HoloOn (A.chart j).source (f j)) ∧
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = L.g j k x ^ n * f k x) ∧
    ∀ j, ∀ x ∉ (A.chart j).source, f j x = 0}
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
end HolLineBundle
structure Weight {A : FinHolAtlas D X} (L : HolLineBundle A) where

  φ : Fin A.n → X → ℝ
  smooth : ∀ j, A.SmoothOn (A.chart j).source (φ j)
  compat : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
    φ j x = φ k x + Real.log (‖L.g j k x‖ ^ 2)
namespace Weight
variable {A : FinHolAtlas D X} {L : HolLineBundle A}
def IsSemipositive (W : Weight L) : Prop :=
  ∀ j, ∀ y ∈ (A.chart j).target, ∀ w : Fin D → ℂ, 0 ≤ levi (W.φ j ∘ (A.chart j).symm) y w
def lerp (W₀ W₁ : Weight L) (t : ℝ) : Weight L where
  φ j x := W₀.φ j x + t * (W₁.φ j x - W₀.φ j x)
  smooth j k := (W₀.smooth j k).add (contDiffOn_const.mul ((W₁.smooth j k).sub (W₀.smooth j k)))
  compat j k x hx := by rw [W₀.compat j k x hx, W₁.compat j k x hx]; ring
def diff (W₁ W₀ : Weight L) (x : X) : ℝ :=
  W₁.φ (chartIdx A x) x - W₀.φ (chartIdx A x) x
end Weight
structure SmoothVolume [MeasurableSpace X] (A : FinHolAtlas D X) where

  μ : Measure X
  isProb : IsProbabilityMeasure μ

  dens : Fin A.n → (Fin D → ℂ) → ℝ
  smooth : ∀ j, ContDiffOn ℝ ∞ (dens j) (A.chart j).target
  pos : ∀ j, ∀ y ∈ (A.chart j).target, 0 < dens j y
  chart_lintegral : ∀ j (g : X → ℝ≥0∞), Measurable g →
    ∫⁻ x in (A.chart j).source, g x ∂μ =
      ∫⁻ y in (A.chart j).target, g ((A.chart j).symm y) * ENNReal.ofReal (dens j y)
variable {A : FinHolAtlas D X} {L : HolLineBundle A}
def ptNormSq (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) : ℝ :=
  ‖s (chartIdx A x) x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x)
variable [MeasurableSpace X]
def sectionL2NormSq (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) : ℝ :=
  ∫ x, ptNormSq W n s x ∂dV.μ
def bergman (W : Weight L) (dV : SmoothVolume A) (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ)
    (x : X) : ℝ :=
  ⨆ s : V, ptNormSq W n (s : Fin A.n → X → ℂ) x / sectionL2NormSq W dV n s
def chernTopDens (W : Weight L) (j : Fin A.n) (y : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * ((((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ j ∘ (A.chart j).symm) y).det).re
def bergmanDens (W : Weight L) (dV : SmoothVolume A) (x : X) : ℝ :=
  chernTopDens W (chartIdx A x) (A.chart (chartIdx A x) x) /
    ((D.factorial : ℝ) * dV.dens (chartIdx A x) (A.chart (chartIdx A x) x))
def gram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} (e : ι → Fin A.n → X → ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun a b => ∫ x, e a (chartIdx A x) x * conj (e b (chartIdx A x) x) *
    ((Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) : ℝ) : ℂ) ∂dV.μ
def chiGram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Fin A.n → X → ℂ) : ℝ :=
  -(1 / 2) * Real.log (gram W dV n e).det.re
end
noncomputable def gaussDiscMass (lam R : ℝ) : ℝ :=
  if lam = 0 then Real.pi * R ^ 2 else Real.pi * (1 - Real.exp (-lam * R ^ 2)) / lam
end GroundTheory.Heights₂.Heights.HilbertSamuel


