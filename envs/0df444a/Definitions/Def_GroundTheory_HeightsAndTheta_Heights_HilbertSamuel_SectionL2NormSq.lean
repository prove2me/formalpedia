-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_SectionL2NormSq
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_SectionL2NormSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:03.269808+00:00
-- url     : https://prove2.me/theorems/48534018-e79b-4470-a0bf-fa1255eaa934
-- title:
--   Section L2 Norm Sq
-- statement:
--   Definitions and structural lemmas for Section L2 Norm Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/SectionL2NormSq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MeasureTheory Filter Topology Set
open scoped ContDiff ComplexConjugate
open ReciprocityTheory.AnForm (levi hessC)
open ReciprocityTheory.AnForm.M (FinHolAtlas chartIdx)
noncomputable section
namespace Bergman
def polydisc (D : ℕ) (r : ℝ) : Set (Fin D → ℂ) := {z | ∀ j, ‖z j‖ < r}
def gaussDiscMass (lam R : ℝ) : ℝ :=
  if lam = 0 then Real.pi * R ^ 2 else Real.pi * (1 - Real.exp (-(lam * R ^ 2))) / lam
variable {D : ℕ} {X : Type*} [TopologicalSpace X]
structure HolLineBundle (A : FinHolAtlas D X) where

  g : Fin A.n → Fin A.n → X → ℂ
  holo : ∀ j k, A.HoloOn ((A.chart j).source ∩ (A.chart k).source) (g j k)
  ne_zero : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, g j k x ≠ 0
  cocycle : ∀ j k l, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source ∩ (A.chart l).source,
    g j k x * g k l x = g j l x
variable {A : FinHolAtlas D X}
def IsSection (L : HolLineBundle A) (n : ℕ) (f : Fin A.n → X → ℂ) : Prop :=
  (∀ j, A.HoloOn (A.chart j).source (f j)) ∧
  (∀ j, ∀ x ∉ (A.chart j).source, f j x = 0) ∧
  ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = L.g j k x ^ n * f k x
theorem holoOn_zero' (U : Set X) : A.HoloOn U (fun _ => (0 : ℂ)) := fun _ => analyticOnNhd_const
theorem holoOn_add' {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U (f + g) := fun j => (hf j).add (hg j)
theorem holoOn_smul' {U : Set X} (c : ℂ) {f : X → ℂ} (hf : A.HoloOn U f) :
    A.HoloOn U (c • f) := fun j => (analyticOnNhd_const (v := c)).mul (hf j)
def sectionSpace (L : HolLineBundle A) (n : ℕ) : Submodule ℂ (Fin A.n → X → ℂ) where
  carrier := {f | IsSection L n f}
  add_mem' := by
    rintro f h ⟨hf1, hf2, hf3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun j => holoOn_add' (hf1 j) (hh1 j), fun j x hx => ?_, fun j k x hx => ?_⟩
    · simp [hf2 j x hx, hh2 j x hx]
    · simp only [Pi.add_apply, hf3 j k x hx, hh3 j k x hx]; ring
  zero_mem' := ⟨fun j => holoOn_zero' _, fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨fun j => holoOn_smul' c (hf1 j), fun j x hx => ?_, fun j k x hx => ?_⟩
    · simp [hf2 j x hx]
    · simp only [Pi.smul_apply, smul_eq_mul, hf3 j k x hx]; ring
def IsWeight (L : HolLineBundle A) (φ : Fin A.n → X → ℝ) : Prop :=
  (∀ j, A.SmoothOn (A.chart j).source (φ j)) ∧
  ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
    φ j x = φ k x + Real.log (‖L.g j k x‖ ^ 2)
def IsSemipositive (A : FinHolAtlas D X) (φ : Fin A.n → X → ℝ) : Prop :=
  ∀ j l, ReciprocityTheory.AnForm.A.IsLeviPsh ((A.chart l).target ∩ (A.chart l).symm ⁻¹' (A.chart j).source)
    (φ j ∘ (A.chart l).symm)
def interp (φ₀ φ₁ : Fin A.n → X → ℝ) (t : ℝ) : Fin A.n → X → ℝ :=
  fun j x => φ₀ j x + t * (φ₁ j x - φ₀ j x)
def weightDiff (A : FinHolAtlas D X) (φ₀ φ₁ : Fin A.n → X → ℝ) (x : X) : ℝ :=
  φ₁ (chartIdx A x) x - φ₀ (chartIdx A x) x
def ptNormSq (A : FinHolAtlas D X) (φ : Fin A.n → X → ℝ) (n : ℕ) (f : Fin A.n → X → ℂ) (x : X) :
    ℝ :=
  ‖f (chartIdx A x) x‖ ^ 2 * Real.exp (-((n : ℝ) * φ (chartIdx A x) x))
def ptInner (A : FinHolAtlas D X) (φ : Fin A.n → X → ℝ) (n : ℕ) (f f' : Fin A.n → X → ℂ) (x : X) :
    ℂ :=
  f (chartIdx A x) x * conj (f' (chartIdx A x) x) *
    ((Real.exp (-((n : ℝ) * φ (chartIdx A x) x)) : ℝ) : ℂ)
structure SmoothVolume [MeasurableSpace X] (A : FinHolAtlas D X) where

  μ : Measure X
  isProb : IsProbabilityMeasure μ

  dens : Fin A.n → (Fin D → ℂ) → ℝ
  smooth : ∀ j, ContDiffOn ℝ ∞ (dens j) (A.chart j).target
  pos : ∀ j, ∀ y ∈ (A.chart j).target, 0 < dens j y
  chart_eq : ∀ j, ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (dens j y)).map (A.chart j).symm = μ.restrict (A.chart j).source
variable [MeasurableSpace X]
def sectionL2NormSq (V : SmoothVolume A) (φ : Fin A.n → X → ℝ) (n : ℕ) (f : Fin A.n → X → ℂ) : ℝ :=
  ∫ x, ptNormSq A φ n f x ∂V.μ
def gram (V : SmoothVolume A) (φ : Fin A.n → X → ℝ) (n : ℕ) {ι : Type*}
    (s : ι → Fin A.n → X → ℂ) : Matrix ι ι ℂ :=
  fun a b => ∫ x, ptInner A φ n (s a) (s b) x ∂V.μ
def chi (V : SmoothVolume A) (φ : Fin A.n → X → ℝ) (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Fin A.n → X → ℂ) : ℝ :=
  -(1 / 2) * Real.log (gram V φ n s).det.re
def bergman (V : SmoothVolume A) (φ : Fin A.n → X → ℝ) (n : ℕ)
    (W : Submodule ℂ (Fin A.n → X → ℂ)) (x : X) : ℝ :=
  ⨆ s : {s : W // s ≠ 0}, ptNormSq A φ n (s.1 : Fin A.n → X → ℂ) x /
    sectionL2NormSq V φ n (s.1 : Fin A.n → X → ℂ)
def chernDet (A : FinHolAtlas D X) (φ : Fin A.n → X → ℝ) (x : X) : ℝ :=
  (((Real.pi : ℂ)⁻¹ • hessC (φ (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm)
    (A.chart (chartIdx A x) x)).det).re
def chernRatio (V : SmoothVolume A) (φ : Fin A.n → X → ℝ) (x : X) : ℝ :=
  chernDet A φ x / V.dens (chartIdx A x) (A.chart (chartIdx A x) x)
end Bergman
open Bergman
def PolydiscSubmean.Statement : Prop :=
  ∀ (D n : ℕ), 0 < n → ∀ R : ℝ, 0 < R → ∀ lam : Fin D → ℝ, (∀ j, 0 ≤ lam j) →
    ∀ f : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ f (polydisc D (R / Real.sqrt n)) →
      ENNReal.ofReal (‖f 0‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R) ≤
        ∫⁻ z in polydisc D (R / Real.sqrt n),
          ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2)))
def LocalBergmanBound.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (φ : Fin A.n → X → ℝ)
    (V : SmoothVolume A) (W : ℕ → Submodule ℂ (Fin A.n → X → ℂ)),
    1 ≤ D → IsWeight L φ → IsSemipositive A φ → (∀ n, W n ≤ sectionSpace L n) →
    (∀ n, FiniteDimensional ℂ (W n)) →
    ∀ x : X, ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) ^ D)⁻¹ * bergman V φ n (W n) x ≤ chernRatio V φ x + ε
def UniformBergmanBound.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (φ₀ φ₁ : Fin A.n → X → ℝ)
    (V : SmoothVolume A) (W : ℕ → Submodule ℂ (Fin A.n → X → ℂ)),
    1 ≤ D → IsWeight L φ₀ → IsWeight L φ₁ → IsSemipositive A φ₀ → IsSemipositive A φ₁ →
    (∀ n, W n ≤ sectionSpace L n) → (∀ n, FiniteDimensional ℂ (W n)) →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : X,
      ((n : ℝ) ^ D)⁻¹ * bergman V (interp φ₀ φ₁ t) n (W n) x ≤ C
def IntegralOfBergman.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (φ : Fin A.n → X → ℝ)
    (V : SmoothVolume A) (n : ℕ) (W : Submodule ℂ (Fin A.n → X → ℂ)),
    1 ≤ D → IsWeight L φ → W ≤ sectionSpace L n → FiniteDimensional ℂ W →
    ∫ x, bergman V φ n W x ∂V.μ = (Module.finrank ℂ W : ℝ)
def L1Convergence.Statement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (g : ℕ → Ω → ℝ)
    (b : Ω → ℝ) (C : ℝ),
    (∀ n, AEStronglyMeasurable (g n) μ) → Integrable b μ →
    (∀ n x, 0 ≤ g n x) → (∀ n x, g n x ≤ C) →
    (∀ x, ∀ ε > 0, ∀ᶠ n in atTop, g n x ≤ b x + ε) →
    (∀ ε > 0, ∀ᶠ n in atTop, ∫ x, b x ∂μ - ε ≤ ∫ x, g n x ∂μ) →
    Tendsto (fun n => ∫ x, |g n x - b x| ∂μ) atTop (𝓝 0)
def MetricChange.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (φ₀ φ₁ : Fin A.n → X → ℝ)
    (V : SmoothVolume A) (W : ℕ → Submodule ℂ (Fin A.n → X → ℂ))
    (s : ∀ n, Module.Basis (Fin (Module.finrank ℂ (W n))) ℂ (W n)),
    1 ≤ D → IsWeight L φ₀ → IsWeight L φ₁ → IsSemipositive A φ₀ → IsSemipositive A φ₁ →
    (∀ n, W n ≤ sectionSpace L n) → (∀ n, FiniteDimensional ℂ (W n)) →
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      (∫ x, chernRatio V (interp φ₀ φ₁ t) x ∂V.μ - ε) * (n : ℝ) ^ D ≤ Module.finrank ℂ (W n)) →
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      |chi V φ₁ n (fun a => ((s n a : W n) : Fin A.n → X → ℂ)) -
          chi V φ₀ n (fun a => ((s n a : W n) : Fin A.n → X → ℂ)) -
          (n : ℝ) ^ (D + 1) / 2 *
            ∫ t in (0 : ℝ)..1, ∫ x, weightDiff A φ₀ φ₁ x * chernRatio V (interp φ₀ φ₁ t) x ∂V.μ| ≤
        ε * (n : ℝ) ^ (D + 1)
def SupNormAgainstL2.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (φ : Fin A.n → X → ℝ)
    (V : SmoothVolume A),
    1 ≤ D → IsWeight L φ → IsSemipositive A φ →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s ∈ sectionSpace L n,
      (∀ x, Real.sqrt (ptNormSq A φ n s x) ≤ C * Real.sqrt n ^ D * Real.sqrt (sectionL2NormSq V φ n s)) ∧
      ∀ M : ℝ, (∀ x, Real.sqrt (ptNormSq A φ n s x) ≤ M) → Real.sqrt (sectionL2NormSq V φ n s) ≤ M
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel


