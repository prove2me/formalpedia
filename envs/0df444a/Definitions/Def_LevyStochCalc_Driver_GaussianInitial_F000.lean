-- Prove2me | Definitions.Def_LevyStochCalc_Driver_GaussianInitial_F000
-- name    : LevyStochCalc_Driver_GaussianInitial_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:42:40.313429+00:00
-- url     : https://prove2.me/theorems/23f6c62b-d75d-498b-9037-a30ee50d493e
-- title:
--   Source declarations: LevyStochCalc.Driver.GaussianInitial
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.GaussianInitial. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Existence_F000
import Mathlib.Probability.HasLaw

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A Lévy driver with an independent Gaussian initial value

A Lévy driver pulls back along a measure-preserving map `φ : Ω' → Ω`: its Brownian motion and
Poisson random measure are read off `φ`, and the joint natural filtration of the pullback is the
comap of the joint natural filtration, `(D.comap hφ).filtration t = (D.filtration t).comap φ`.

On the product space `Ω × ℝ` under `P ⊗ 𝒩(m₀, v)`, the pullback of `D` along the first projection
is a Lévy driver whose whole filtration `⨆ t, ℱ_t` factors through the first coordinate, while the
second coordinate has law `𝒩(m₀, v)`. Coordinates of a product probability space are
independent, so the second coordinate is an initial value independent of the driver.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.comap`: the pullback of a Lévy driver along a
  measure-preserving map.
* `LevyStochCalc.Driver.LevyDriver.prodGaussian`: the pullback of `D` to `Ω × ℝ` under
  `P ⊗ 𝒩(m₀, v)` along the first projection.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.filtration_comap`: the joint filtration of the pullback is the
  comap of the joint filtration.
* `LevyStochCalc.Driver.hasLaw_snd_prod_gaussianReal`: under `P ⊗ 𝒩(m₀, v)` the second
  coordinate has law `𝒩(m₀, v)`.
* `LevyStochCalc.Driver.LevyDriver.indep_comap_snd_iSup_filtration_prodGaussian`: the σ-algebra of
  the second coordinate is independent of `⨆ t, ℱ_t` for the driver `D.prodGaussian m₀ v`.
* `LevyStochCalc.Driver.LevyDriver.exists_gaussianInitial`: for every `d`, every σ-finite
  intensity `ν`, and every `m₀`, `v`, some probability space carries a Lévy driver and a real
  random variable of law `𝒩(m₀, v)` whose σ-algebra is independent of `⨆ t, ℱ_t`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyStochCalc.Driver

universe u v w

section Comap

variable {Ω : Type u} [MeasurableSpace Ω] {Ω' : Type u} [MeasurableSpace Ω']
  {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ν : Measure E} [SigmaFinite ν] {d : ℕ} {φ : Ω' → Ω}

/-- The σ-algebra of a Brownian motion pulled back along `φ` is the comap along `φ` of its
σ-algebra. -/
lemma _root_.LevyStochCalc.Brownian.sigmaBrownian_comap (W : Brownian.BrownianMotion P)
    (hφ : MeasurePreserving φ P' P) :
    Brownian.sigmaBrownian (W.comap hφ) = (Brownian.sigmaBrownian W).comap φ := by
  simp only [Brownian.sigmaBrownian, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl
/-- The natural filtration of a Brownian motion pulled back along `φ` is the comap along `φ` of
its natural filtration. -/
lemma _root_.LevyStochCalc.Brownian.Martingale.naturalFiltration_comap
    (W : Brownian.BrownianMotion P) (hφ : MeasurePreserving φ P' P) (s : ℝ) :
    Brownian.Martingale.naturalFiltration (W.comap hφ) s
      = (Brownian.Martingale.naturalFiltration W s).comap φ := by
  change (⨆ j ≤ s, MeasurableSpace.comap ((W.comap hφ).W j) inferInstance)
    = (⨆ j ≤ s, MeasurableSpace.comap (W.W j) inferInstance).comap φ
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl
/-- The joint natural filtration of a `d`-dimensional Brownian motion pulled back along `φ` is
the comap along `φ` of its joint natural filtration. -/
lemma _root_.LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_comap
    (W : Brownian.Multidim.MultidimBrownianMotion P d) (hφ : MeasurePreserving φ P' P)
    (s : ℝ) : (W.comap hφ).naturalFiltration s = (W.naturalFiltration s).comap φ := by
  rw [Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_apply,
    Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_apply,
    MeasurableSpace.comap_iSup]
  exact iSup_congr fun i => Brownian.Martingale.naturalFiltration_comap (W.W i) hφ s
/-- The σ-algebra of a Poisson random measure pulled back along `φ` is the comap along `φ` of
its σ-algebra. -/
lemma sigmaPoisson_comap (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν)
    (hφ : MeasurePreserving φ P' P) :
    sigmaPoisson (N.comap hφ) = (sigmaPoisson N).comap φ := by
  simp only [sigmaPoisson, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl
/-- The natural filtration of a Poisson random measure pulled back along `φ` is the comap along
`φ` of its natural filtration. -/
lemma _root_.LevyStochCalc.Poisson.naturalFiltration_comap
    (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν) (hφ : MeasurePreserving φ P' P) (s : ℝ) :
    Poisson.naturalFiltration (N.comap hφ) s = (Poisson.naturalFiltration N s).comap φ := by
  change (⨆ B ∈ {C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C},
      MeasurableSpace.comap (fun ω' => (N.comap hφ).N ω' B) inferInstance)
    = (⨆ B ∈ {C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C},
      MeasurableSpace.comap (fun ω => N.N ω B) inferInstance).comap φ
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl
namespace LevyDriver

/-- The Lévy driver `ω' ↦ (W (φ ω'), N (φ ω'))` obtained by pulling a Lévy driver back along a
measure-preserving map `φ`. -/
noncomputable def comap (D : LevyDriver.{u, v, w} P d ν) (hφ : MeasurePreserving φ P' P) :
    LevyDriver.{u, v, w} P' d ν where
  W := D.W.comap hφ
  N := D.N.comap hφ
  indep := by
    have hW : (⨆ i, Brownian.sigmaBrownian ((D.W.comap hφ).W i))
        = (⨆ i, Brownian.sigmaBrownian (D.W.W i)).comap φ := by
      rw [MeasurableSpace.comap_iSup]
      exact iSup_congr fun i => Brownian.sigmaBrownian_comap (D.W.W i) hφ
    rw [hW, sigmaPoisson_comap]
    exact Probability.indep_comap_of_measurePreserving hφ
      (iSup_le fun i => Brownian.sigmaBrownian_le (D.W.W i)) (sigmaPoisson_le D.N) D.indep
@[simp]
lemma comap_W (D : LevyDriver.{u, v, w} P d ν) (hφ : MeasurePreserving φ P' P) :
    (D.comap hφ).W = D.W.comap hφ := rfl
@[simp]
lemma comap_N (D : LevyDriver.{u, v, w} P d ν) (hφ : MeasurePreserving φ P' P) :
    (D.comap hφ).N = D.N.comap hφ := rfl
/-- The joint filtration of a Lévy driver pulled back along `φ` is the comap along `φ` of its
joint filtration. -/
theorem filtration_comap (D : LevyDriver.{u, v, w} P d ν) (hφ : MeasurePreserving φ P' P)
    (s : ℝ) : (D.comap hφ).filtration s = (D.filtration s).comap φ := by
  rw [filtration_apply, filtration_apply, MeasurableSpace.comap_sup, comap_W, comap_N,
    Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_comap,
    Poisson.naturalFiltration_comap]
/-- The σ-algebra generated by the whole joint filtration of a Lévy driver pulled back along `φ`
is the comap along `φ` of the σ-algebra generated by its joint filtration. -/
theorem iSup_filtration_comap (D : LevyDriver.{u, v, w} P d ν)
    (hφ : MeasurePreserving φ P' P) :
    ⨆ s, (D.comap hφ).filtration s = (⨆ s, D.filtration s).comap φ := by
  rw [MeasurableSpace.comap_iSup]
  exact iSup_congr fun s => D.filtration_comap hφ s
end LevyDriver

end Comap

section Gaussian

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- Under `P ⊗ 𝒩(m₀, v)` the second coordinate has law `𝒩(m₀, v)`. -/
theorem hasLaw_snd_prod_gaussianReal (m₀ : ℝ) (v : ℝ≥0) :
    HasLaw (Prod.snd : Ω × ℝ → ℝ) (gaussianReal m₀ v) (P.prod (gaussianReal m₀ v)) :=
  (measurePreserving_snd (μ := P) (ν := gaussianReal m₀ v)).hasLaw
namespace LevyDriver

/-- The Lévy driver on `Ω × ℝ` under `P ⊗ 𝒩(m₀, v)` read off the first coordinate. -/
noncomputable def prodGaussian (D : LevyDriver.{u, v, w} P d ν) (m₀ : ℝ) (v : ℝ≥0) :
    LevyDriver.{u, v, w} (P.prod (gaussianReal m₀ v)) d ν :=
  D.comap (measurePreserving_fst (μ := P) (ν := gaussianReal m₀ v))
/-- The joint filtration of `D.prodGaussian m₀ v` is the comap along the first projection of the
joint filtration of `D`. -/
theorem filtration_prodGaussian (D : LevyDriver.{u, v, w} P d ν) (m₀ : ℝ) (v : ℝ≥0) (s : ℝ) :
    (D.prodGaussian m₀ v).filtration s = (D.filtration s).comap Prod.fst :=
  D.filtration_comap _ s
/-- Under `P ⊗ 𝒩(m₀, v)` the σ-algebra of the second coordinate is independent of the
σ-algebra generated by the whole joint filtration of `D.prodGaussian m₀ v`. -/
theorem indep_comap_snd_iSup_filtration_prodGaussian (D : LevyDriver.{u, v, w} P d ν)
    (m₀ : ℝ) (v : ℝ≥0) :
    Indep (MeasurableSpace.comap (Prod.snd : Ω × ℝ → ℝ) inferInstance)
      (⨆ t, (D.prodGaussian m₀ v).filtration t) (P.prod (gaussianReal m₀ v)) := by
  have hprod : Indep (MeasurableSpace.comap (Prod.snd : Ω × ℝ → ℝ) inferInstance)
      (MeasurableSpace.comap (Prod.fst : Ω × ℝ → Ω) inferInstance)
      (P.prod (gaussianReal m₀ v)) :=
    (indepFun_prod (μ := P) (ν := gaussianReal m₀ v) (X := id) (Y := id)
      measurable_id measurable_id).symm
  refine indep_of_indep_of_le_right hprod (iSup_le fun t => ?_)
  rw [D.filtration_prodGaussian]
  exact MeasurableSpace.comap_mono (D.filtration.le t)
/-- **A Lévy driver with an independent Gaussian initial value.** For every `d`, every σ-finite
intensity `ν` on a measurable mark space, every `m₀ : ℝ` and every `v : ℝ≥0`, some probability
space carries a Lévy driver `D` and a measurable real random variable `X₀` of law `𝒩(m₀, v)`
whose σ-algebra is independent of the σ-algebra generated by the joint filtration of `D`. -/
theorem exists_gaussianInitial (d : ℕ) (E : Type u) [MeasurableSpace E] (ν : Measure E)
    [SigmaFinite ν] (m₀ : ℝ) (v : ℝ≥0) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver.{u, u, w} P d ν) (X₀ : Ω → ℝ),
      Measurable X₀ ∧ HasLaw X₀ (gaussianReal m₀ v) P ∧
        Indep (MeasurableSpace.comap X₀ inferInstance) (⨆ t, D.filtration t) P := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyDriver.exists.{u, w} d E ν
  exact ⟨Ω × ℝ, inferInstance, P.prod (gaussianReal m₀ v), inferInstance, D.prodGaussian m₀ v,
    Prod.snd, measurable_snd, hasLaw_snd_prod_gaussianReal m₀ v,
    D.indep_comap_snd_iSup_filtration_prodGaussian m₀ v⟩
end LevyDriver

end Gaussian

end LevyStochCalc.Driver


