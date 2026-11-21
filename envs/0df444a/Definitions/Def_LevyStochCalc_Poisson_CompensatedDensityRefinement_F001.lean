-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F001
-- name    : LevyStochCalc_Poisson_CompensatedDensityRefinement_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:53:36.304228+00:00
-- url     : https://prove2.me/theorems/f7ec68fc-e51e-4e47-bb2d-3dfd29b66f21
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityRefinement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityRefinement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F002
import Definitions.Def_SourceProof_38bd2809fbf8ffc383f84cb8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob `L²` bricks and dyadic cross-resolution refinement

Two preparations for the passage to the limit: the submartingale property of `‖M‖` and the
discrete tail maximal inequality for a martingale, and the re-expression of a dyadic step
integrand at level `n` on a finer dyadic level `m ≥ n`. The refinement keeps the integrand
adapted and its compensated integral unchanged, so integrands of different resolutions can be
compared on a common grid.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Doob `L²` machinery (toward the càdlàg conjunct of #6)

Mathlib has only the discrete *tail* maximal inequality (`maximal_ineq`), the
layer-cake formula, and conditional Jensen. The continuous-time Doob `L²` maximal
inequality and the càdlàg regularization are built here from those pieces. -/

/-- **Step-integral isometry (per-piece marks).** The textbook L²-Itô-Lévy isometry
`E[(∑ᵢ∑_{k₀} ciₖ Ñ((pᵢ,pᵢ₊₁]×Biₖ))²] = E[∫_E∫_{[0,T]} (eval)²]` for a step approximant
with **per-time-piece** mark families. Collects the marks into the shared form
(`exists_sharedMark_blockDiag`), then applies `markSumProcess_isometry_L2`. -/
lemma markStepIntegral_isometry
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ) {N₀ : ℕ} (p : Fin (N₀ +
      1) → ℝ)
    (hp0 : p 0 = 0) (hpmono : StrictMono p) {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    {Ki : Fin N₀ → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hBif : ∀ i k, ν (Bi i k) ≠ ⊤)
    (hcib : ∀ i k, ∃ M, ∀ ω, |ci i k ω| ≤ M) (hcim : ∀ i k, Measurable (ci i k))
    (hcia : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ci i k)) :
    ∫ ω, (∑ i : Fin N₀, ∑ k₀, ci i k₀ ω
        * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi i k₀) ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * ∑ k₀, ci i k₀ ω * (Bi i k₀).indicator (fun _ => (1 : ℝ)) e) ^ 2
        ∂volume ∂ν) ∂P := by
  obtain ⟨K, B, ξ, hBm, hBf, hξb, hξm, hξa, hF⟩ :=
    _root_.Prove2MeSourceProof.h_38bd2809fbf8ffc383f84cb8 N ℱ p Bi ci hBim hBif hcib hcim hcia
  have key := markSumProcess_isometry_L2 p hp0 hpmono hpleT N ℱ hℱ B hBm hBf ξ hξb hξm hξa
  have hint : ∀ ω, (∑ i : Fin N₀, ∑ k, ξ i k ω
        * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
      = ∑ i : Fin N₀, ∑ k₀, ci i k₀ ω
        * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi i k₀) ω := fun ω =>
    Finset.sum_congr rfl (fun i _ =>
      hF i ω (fun B' => N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B') ω))
  have hev : ∀ ω e s, (∑ i : Fin N₀,
        (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * ∑ k, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)
      = ∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * ∑ k₀, ci i k₀ ω * (Bi i k₀).indicator (fun _ => (1 : ℝ)) e := fun ω e s =>
    Finset.sum_congr rfl (fun i _ => by
      rw [hF i ω (fun B' => (B').indicator (fun _ => (1 : ℝ)) e)])
  simp only [hint, hev] at key
  exact key
/-! ### Cross-resolution refinement (toward the `L²(P)` Cauchy property)

To compare the step integrals of two density approximants at *different* dyadic
levels, both are re-expressed on the common (finer) dyadic refinement. The basic
brick is additivity of the compensated integral over a split time-interval. -/

end LevyStochCalc.Poisson.Compensated


