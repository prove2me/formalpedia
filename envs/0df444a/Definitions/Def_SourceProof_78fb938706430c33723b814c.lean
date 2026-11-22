-- Prove2me | Definitions.Def_SourceProof_78fb938706430c33723b814c
-- name    : SourceProof_78fb938706430c33723b814c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:10:35.781224+00:00
-- url     : https://prove2.me/theorems/e1df41c9-8d9a-4b4c-a9e1-c768479a0d3b
-- title:
--   LevyStochCalc source module: SourceProof_78fb938706430c33723b814c
-- statement:
--   The original source theorem `LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun₂_eq` comes from the `LevyStochCalc.Ito.CutoffJumpTransfer` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffJumpTransfer_F000
import Definitions.Def_SourceProof_2bacfe260b21496ede907710
import Definitions.Def_SourceProof_388a40baa407d0b0ae15b23c
import Definitions.Def_SourceProof_6cdc47526d2ae213604fd2f4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump side of the Itô–Lévy formula under the state cut-off

Along a path confined to a ball the state cut-off moves the jump increment and the
compensator-drift integrand by the same quantity, and that quantity vanishes at every atom of the
random measure. An integrand vanishing at the atoms has compensated integral minus its
compensator, so the two moves cancel: the *sum* of the compensated integral of the jump increment
and the compensator-drift integral is the same for a state function and for its cut-off, even
though neither term is.

## Main definitions

* `jumpIncrLeft` — the jump increment of a state function along a path, read at the left limits.

## Main statements

* `measurable_jumpIncrLeft`, `markedProgressivelyMeasurable_jumpIncrLeft`,
  `markedPredictable_zeroExtPos_jumpIncrLeft` — its admissibility and the predictability of its
  zero extension.
* `ae_jumpSide_cutoffFun₂_eq` — the jump side is unchanged by the cut-off on the event that the
  path stays in the ball.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Ito.JumpFormula LevyStochCalc.Ito.JumpFormulaCutoff
open LevyStochCalc.Ito.JumpSplitting LevyStochCalc.Ito.JumpSide
open LevyStochCalc.Probability

universe u v

section Integrand

variable {Ω : Type u} {E : Type v} {n d : ℕ}

end Integrand

section Regularity

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {n d : ℕ}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}
  {w : ℝ → (Fin n → ℝ) → ℝ}

variable {ν : Measure E} [SigmaFinite ν]

end Regularity

section Transfer

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_78fb938706430c33723b814c
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : IsPoissonFiltration N ℱ)
    {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : 0 < m) (hTm : T < 3 * (m : ℝ))
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L))
    (hmv : Measurable fun p : Ω × ℝ × E =>
      jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp p.1 p.2.1 p.2.2)
    (hpv : MarkedProgressivelyMeasurable ℱ
      (jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp))
    (hqv : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤)
    (hmu : Measurable fun p : Ω × ℝ × E => jumpIncrLeft u coeffs Xp p.1 p.2.1 p.2.2)
    (hpu : MarkedProgressivelyMeasurable ℱ (jumpIncrLeft u coeffs Xp))
    (hqu : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖jumpIncrLeft u coeffs Xp ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hCdv : ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      IntegrableOn (fun q : ℝ × E => compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ)))
          coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν))
    (hCdu : ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      IntegrableOn (fun q : ℝ × E => compensatorDriftIntegrand u
          coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν))
    (hjump : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ k, θ k ∈ Set.Ioc (0 : ℝ) T ∧ ε k ∈ spanningSets ν j) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, g p ∂(N.N ω)
        = ∑ k : Fin K, g (θ k, ε k)) ∧
      ∀ k : Fin K,
        Xp (θ k) ω
          = leftLimPathAt Xp (θ k) ω + coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k)) :
    ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      Compensated.stochasticIntegral N ℱ hℱN
            (jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp) hmv hpv hqv T ω
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
              compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ q.1
                (leftLimPathAt Xp q.1 ω) q.2 ∂(referenceIntensity ν)
        = Compensated.stochasticIntegral N ℱ hℱN (jumpIncrLeft u coeffs Xp) hmu hpu hqu T ω
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
              compensatorDriftIntegrand u coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2
                ∂(referenceIntensity ν) := by
  classical
  set Ψ : Ω → ℝ → E → ℝ := fun ω s e =>
    LevyStochCalc.Ito.CutoffPath.jumpIncrLeft (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp ω s e - LevyStochCalc.Ito.CutoffPath.jumpIncrLeft u coeffs Xp ω s e
    with hΨdef
  have hvC : ContDiff ℝ 2 (Function.uncurry (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ)))) :=
    LevyStochCalc.Ito.JumpFormulaCutoff.contDiff_uncurry_cutoffFun₂ hu _
  have hms : Measurable fun p : Ω × ℝ × E => Ψ p.1 p.2.1 p.2.2 := hmv.sub hmu
  have hps : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ Ψ := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_sub hpv hpu
  have hqs : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖Ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun T' hT' => _root_.Prove2MeSourceProof.h_388a40baa407d0b0ae15b23c hmv hmu
      (hqv T' hT') (hqu T' hT')
  have hpred : LevyStochCalc.Probability.MarkedPredictable ℱ ν (LevyStochCalc.Ito.JumpFormula.zeroExtPos Ψ) :=
    _root_.Prove2MeSourceProof.h_5650dc54a894019ea9a2b291 Xp ℱ hXadapt
      (fun ω t _ j => hXleft ω t j)
      (F := fun s y e => (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ)) s (y + coeffs.γ s y e)
          - LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ)) s y) - (u s (y + coeffs.γ s y e) - u s y))
      ((LevyStochCalc.Ito.CutoffPath.measurable_stateIncr hvC.continuous hγ).sub (LevyStochCalc.Ito.CutoffPath.measurable_stateIncr hu.continuous hγ))
  -- the difference vanishes at the atoms of every finite-intensity window
  have hatoms : ∀ᵐ ω ∂P, ω ∈ LevyStochCalc.Brownian.Ito.boundedPathSet Xp T m → ∀ j : ℕ,
      ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, LevyStochCalc.Ito.JumpFormula.zeroExtPos Ψ ω q.1 q.2 ∂(N.N ω) = 0 := by
    have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ω ∈ LevyStochCalc.Brownian.Ito.boundedPathSet Xp T m →
        ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, LevyStochCalc.Ito.JumpFormula.zeroExtPos Ψ ω q.1 q.2
          ∂(N.N ω) = 0 := by
      refine MeasureTheory.ae_all_iff.mpr fun j => ?_
      filter_upwards [LevyStochCalc.Ito.CutoffPath.ae_setIntegral_jumpIncrement_sub_eq_zero coeffs N Xp (spanningSets ν j)
        u hm hTm (hjump j)
        (Filter.Eventually.of_forall fun ω t i => hXleft ω t i)]
        with ω hω hG
      refine Eq.trans ?_ (hω hG)
      refine setIntegral_congr_fun (measurableSet_Ioc.prod (measurableSet_spanningSets ν j))
        fun q hq => ?_
      exact LevyStochCalc.Ito.JumpFormula.zeroExtPos_of_pos Ψ ω hq.1.1 q.2
    filter_upwards [hall] with ω hω hG j
    exact hω j hG
  -- the difference is the difference of the compensator-drift integrands, hence integrable
  have hpt : ∀ (ω : Ω), ω ∈ LevyStochCalc.Brownian.Ito.boundedPathSet Xp T m →
      ∀ q : ℝ × E, q ∈ Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E) →
        LevyStochCalc.Ito.JumpFormula.zeroExtPos Ψ ω q.1 q.2
          = LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ q.1
              (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp q.1 ω) q.2
            - LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ q.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp q.1 ω) q.2 := by
    intro ω hG q hq
    rw [LevyStochCalc.Ito.JumpFormula.zeroExtPos_of_pos Ψ ω hq.1.1 q.2]
    exact LevyStochCalc.Ito.CutoffPath.jumpIncrement_sub_eq_compensatorDrift_sub_of_boundedPath u hm hTm hG hq.1
      (fun i => hXleft ω q.1 i) q.2
  have hint : ∀ᵐ ω ∂P, ω ∈ LevyStochCalc.Brownian.Ito.boundedPathSet Xp T m →
      IntegrableOn (fun q : ℝ × E => LevyStochCalc.Ito.JumpFormula.zeroExtPos Ψ ω q.1 q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (LevyStochCalc.Poisson.referenceIntensity ν) := by
    filter_upwards [hCdv, hCdu] with ω h1 h2 hG
    exact ((h1 hG).sub (h2 hG)).congr_fun (fun q hq => (hpt ω hG q hq).symm)
      (measurableSet_Ioc.prod MeasurableSet.univ)
  -- the three identities
  have hmainΨ := _root_.Prove2MeSourceProof.h_2bacfe260b21496ede907710 N ℱ hℱN
    (LevyStochCalc.Ito.JumpFormula.zeroExtPos Ψ) (_root_.Prove2MeSourceProof.h_5485fe6f4cdb15f21984b687 hms) (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_zeroExtPos hps)
    (LevyStochCalc.Ito.JumpFormula.energy_zeroExtPos_lt_top hqs) hpred (fun ω s e hs => LevyStochCalc.Ito.JumpFormula.zeroExtPos_of_nonpos Ψ ω hs e) hT
    (LevyStochCalc.Brownian.Ito.boundedPathSet Xp T m) hint hatoms
  have hze := LevyStochCalc.Ito.JumpFormula.compensated_zeroExtPos_congr N ℱ hℱN Ψ hms hps hqs hT
  have hsub := _root_.Prove2MeSourceProof.h_6cdc47526d2ae213604fd2f4 N hℱN hmv hmu hpv hpu hqv hqu hms hps hqs hT
  filter_upwards [hmainΨ, hze, hsub, hCdv, hCdu] with ω h1 h2 h3 h4 h5 hG
  have hI : ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), LevyStochCalc.Ito.JumpFormula.zeroExtPos Ψ ω q.1 q.2
        ∂(LevyStochCalc.Poisson.referenceIntensity ν)
      = (∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
          LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ q.1
            (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp q.1 ω) q.2 ∂(LevyStochCalc.Poisson.referenceIntensity ν))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
            LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ q.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp q.1 ω) q.2
              ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
    rw [← integral_sub (h4 hG) (h5 hG)]
    exact setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ)
      fun q hq => hpt ω hG q hq
  rw [h1 hG, hI] at h2
  linarith [h2, h3]
end Transfer

end LevyStochCalc.Ito.CutoffPath


