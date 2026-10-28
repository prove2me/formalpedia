-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient
-- name    : KLSModular_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:46:26.753635+00:00
-- url     : https://prove2.me/theorems/104a43fa-5f01-4d82-8d6c-f1badbd8f00a
-- title:
--   Bielecki type synonym and separation quotient
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `SBoundedProcess.WithBielecki` is a type synonym for `SBoundedProcess` carrying a phantom weight $\beta$ so distinct Bielecki edist instances can coexist; `of` and `get` are inverse wrappers. Its `PseudoEMetricSpace` edist is `bieleckiEDist`, and `SBoundedProcess.AEQuot` is the `SeparationQuotient` of this pseudo-emetric space, with the induced genuine emetric-space structure. The zero process supplies nonempty instances for both types.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.PicardSpaceBieleckiEDist
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def SBoundedProcess.WithBielecki (n : ℕ) (P : Measure Ω)
--       [IsProbabilityMeasure P] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       (T β : ℝ) : Type _ :=
--     let _ := β  -- silence "unused variable β" — phantom parameter
--     SBoundedProcess (n := n) P ℱ T
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/PicardSpaceBieleckiEDist`](https://prove2.me/theorems/05866989-aa21-4449-a10e-1a50e813f6af).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardSpaceBieleckiQuotient.lean) · `LevyStochCalc.Ito.PicardSpaceBieleckiQuotient` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSpaceBieleckiQuotient.lean#L37-L365 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSpaceBieleckiQuotient`, definition bundle `KLSModular_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSpaceBieleckiEDist

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSpaceBieleckiQuotient.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Type synonym for `SBoundedProcess` carrying the Bielecki β-weighted
pseudo-edist instance.** Two `SBoundedProcess`es that agree P-a.s. at
every `t` have Bielecki pseudo-distance zero; this synonym carries the
pseudo-metric, and `SBoundedProcess.AEQuot` (the `SeparationQuotient`)
carries the genuine metric.

The phantom `β` allows different Bielecki β-values to define distinct
typeclass instances on the same underlying type. The `β` parameter is
intentionally unused in the type definition (it only affects the
distinct `EDist` instance that downstream registers on it). -/
def SBoundedProcess.WithBielecki (n : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (T β : ℝ) : Type _ :=
  let _ := β  -- silence "unused variable β" — phantom parameter
  SBoundedProcess (n := n) P ℱ T
namespace SBoundedProcess
namespace WithBielecki
variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ}
/-- **Constructor.** Wrap a `SBoundedProcess` as the Bielecki-flavored type. -/
def of (X : SBoundedProcess (n := n) P ℱ T) :
    SBoundedProcess.WithBielecki (n := n) P ℱ T β := X
/-- **Underlying `SBoundedProcess` extractor.** -/
def get (X : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    SBoundedProcess (n := n) P ℱ T := X
@[simp] lemma get_of (X : SBoundedProcess (n := n) P ℱ T) :
    SBoundedProcess.WithBielecki.get (SBoundedProcess.WithBielecki.of (n := n) (β := β) X) = X
    := rfl
@[simp] lemma of_get (X : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    SBoundedProcess.WithBielecki.of (n := n) (β := β)
      (SBoundedProcess.WithBielecki.get X) = X := rfl
end WithBielecki
end SBoundedProcess
noncomputable instance instEDistWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    EDist (SBoundedProcess.WithBielecki (n := n) P ℱ T β) where
  edist X Y := bieleckiEDist β T
    (SBoundedProcess.WithBielecki.get X)
    (SBoundedProcess.WithBielecki.get Y)
@[simp] lemma edist_WithBielecki_def
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ}
    (X Y : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    edist X Y = bieleckiEDist β T
      (SBoundedProcess.WithBielecki.get X) (SBoundedProcess.WithBielecki.get Y) := rfl
/-- **Slice-AEMeasurability of the Bielecki inner integrand.** From joint
measurability of `(t, ω) ↦ X t ω`, the per-`t` slice `ω ↦ X t ω` is
measurable; composing with the continuous `r ↦ ‖r‖₊²` and finite sum
preserves measurability; the (1/2)-rpow is measurable; pushing through
gives AEMeasurable of the inner Bielecki expression. -/
lemma bieleckiNorm_inner_aemeasurable
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X)) (t : ℝ) :
    AEMeasurable
      (fun ω => (∑ i, (‖X t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P := by
  -- Slice-measurability of `ω ↦ X t ω` via `Measurable.of_uncurry_left`.
  have h_slice : Measurable (fun ω => X t ω) :=
    Measurable.of_uncurry_left hX_meas
  -- Each component `ω ↦ X t ω i` is measurable (composition with
  -- evaluation).
  have h_comp : ∀ i, Measurable (fun ω => X t ω i) := fun i =>
    h_slice.eval
  -- Each summand `ω ↦ ‖X t ω i‖₊²` is measurable.
  have h_summand : ∀ i, Measurable
      (fun ω => ((‖X t ω i‖₊ : ℝ≥0∞)) ^ 2) := by
    intro i
    refine (Measurable.pow_const ?_ _)
    refine (ENNReal.continuous_coe.measurable.comp ?_)
    exact ((h_comp i).nnnorm)
  -- Finite sum is measurable.
  have h_sum : Measurable (fun ω => ∑ i, ((‖X t ω i‖₊ : ℝ≥0∞)) ^ 2) :=
    Finset.measurable_sum _ (fun i _ => h_summand i)
  -- Composing with the continuous `x ↦ x ^ (1/2)`.
  exact (h_sum.pow_const ((1 : ℝ) / 2)).aemeasurable
/-- **AEMeasurability of the Bielecki inner integrand for the path
difference of two `SBoundedProcess`es.** Follows from
`bieleckiNorm_inner_aemeasurable` applied to `X.X - Y.X` after showing
the difference is jointly measurable. -/
lemma SBoundedProcess.pathDiff_aemeasurable
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X Y : SBoundedProcess (n := n) P ℱ T) (t : ℝ) :
    AEMeasurable (fun ω => (∑ i, (‖(X.X t ω - Y.X t ω) i‖₊ : ℝ≥0∞) ^ 2)
        ^ ((1 : ℝ) / 2)) P := by
  -- The pointwise difference `fun t ω => X.X t ω - Y.X t ω` is jointly
  -- measurable as the difference of two jointly measurable functions.
  have h_diff_meas : Measurable
      (Function.uncurry (fun t ω => X.X t ω - Y.X t ω)) := by
    have : Function.uncurry (fun t ω => X.X t ω - Y.X t ω)
        = fun p : ℝ × Ω => X.X p.1 p.2 - Y.X p.1 p.2 := by
      funext p
      rfl
    rw [this]
    exact X.measurable_path.sub Y.measurable_path
  exact bieleckiNorm_inner_aemeasurable
    (fun t ω => X.X t ω - Y.X t ω) h_diff_meas t
/-- **Triangle inequality for the Bielecki β-norm pseudo-edist.**
For `SBoundedProcess`es X, Y, Z, applying `bieleckiNorm_add_le` to
`Y₁ = X.X - Y.X`, `Y₂ = Y.X - Z.X` gives the triangle inequality. -/
lemma bieleckiEDist_triangle
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {β T : ℝ}
    (X Y Z : SBoundedProcess (n := n) P ℱ T) :
    bieleckiEDist β T X Z
      ≤ bieleckiEDist β T X Y + bieleckiEDist β T Y Z := by
  -- (X.X - Z.X) = (X.X - Y.X) + (Y.X - Z.X) pointwise.
  have h_id : (fun t ω => X.X t ω - Z.X t ω)
      = fun t ω => (X.X t ω - Y.X t ω) + (Y.X t ω - Z.X t ω) := by
    funext t ω
    funext i
    change X.X t ω i - Z.X t ω i = (X.X t ω i - Y.X t ω i) + (Y.X t ω i - Z.X t ω i)
    ring
  -- Apply `bieleckiNorm_add_le`.
  have h := bieleckiNorm_add_le (P := P) β T
    (fun t ω => X.X t ω - Y.X t ω) (fun t ω => Y.X t ω - Z.X t ω)
    (fun t => SBoundedProcess.pathDiff_aemeasurable X Y t)
    (fun t => SBoundedProcess.pathDiff_aemeasurable Y Z t)
  -- Conclude via the pointwise identity.
  change bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff X Z)
    ≤ bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff X Y)
      + bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff Y Z)
  unfold SBoundedProcess.pathDiff
  rw [h_id]
  exact h
noncomputable instance instPseudoEMetricSpaceWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    PseudoEMetricSpace (SBoundedProcess.WithBielecki (n := n) P ℱ T β) where
  edist_self X := by
    change bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
      (SBoundedProcess.WithBielecki.get X) = 0
    exact bieleckiEDist_self _
  edist_comm X Y := by
    change bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
        (SBoundedProcess.WithBielecki.get Y)
      = bieleckiEDist β T (SBoundedProcess.WithBielecki.get Y)
        (SBoundedProcess.WithBielecki.get X)
    exact bieleckiEDist_comm _ _
  edist_triangle X Y Z := by
    change bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
        (SBoundedProcess.WithBielecki.get Z)
      ≤ bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
        (SBoundedProcess.WithBielecki.get Y)
        + bieleckiEDist β T (SBoundedProcess.WithBielecki.get Y)
          (SBoundedProcess.WithBielecki.get Z)
    exact bieleckiEDist_triangle _ _ _
/-- **AE-quotient of `SBoundedProcess` by P-null-set equivalence.**

  `AEQuot β T := SeparationQuotient (SBoundedProcess.WithBielecki β T)`.

Mathlib's `SeparationQuotient` of a `PseudoEMetricSpace` is automatically
a genuine `EMetricSpace` (separated) — and hence a `MetricSpace` once we
project the edist down to a real-valued distance. This is the literature
Banach space `S²([0, T]; ℝⁿ)` modulo P-null-set equivalence. -/
def SBoundedProcess.AEQuot
    (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T β : ℝ) : Type _ :=
  SeparationQuotient (SBoundedProcess.WithBielecki (n := n) P ℱ T β)
/-- Mathlib auto-derives `EMetricSpace` on the `SeparationQuotient`.
Re-export under the project's namespace. -/
noncomputable instance instEMetricSpaceAEQuot
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    EMetricSpace (SBoundedProcess.AEQuot (n := n) P ℱ T β) :=
  instEMetricSpaceSeparationQuotient
end Picard
end Ito
end LevyStochCalc
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- **Nonemptiness of `WithBielecki β T`.** The constant-zero
`SBoundedProcess` (from `PicardSpace.lean`) witnesses inhabitedness
of the underlying type, which inhabits the type synonym. -/
noncomputable instance instNonemptyWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    Nonempty (SBoundedProcess.WithBielecki (n := n) P ℱ T β) :=
  ⟨SBoundedProcess.WithBielecki.of (β := β) (constantZeroProcess (n := n) P ℱ T)⟩
/-- **Nonemptiness of `AEQuot β T`.** Lifts from the constant-zero process
via `SeparationQuotient.mk`. -/
noncomputable instance instNonemptyAEQuot
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    Nonempty (SBoundedProcess.AEQuot (n := n) P ℱ T β) :=
  ⟨SeparationQuotient.mk (SBoundedProcess.WithBielecki.of (β := β)
    (constantZeroProcess (n := n) P ℱ T))⟩
end Picard
end Ito
end LevyStochCalc


