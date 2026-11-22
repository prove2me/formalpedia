-- Prove2me | Definitions.Def_SourceProof_5480422f0c02d5366a6c8d44
-- name    : SourceProof_5480422f0c02d5366a6c8d44
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:58:02.980185+00:00
-- url     : https://prove2.me/theorems/49d69852-3594-47f7-928f-1af75b3bcdd2
-- title:
--   LevyStochCalc source module: SourceProof_5480422f0c02d5366a6c8d44
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.solvesOn_cadlagRep` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F001
import Definitions.Def_SourceProof_a73d9c684890e7b4cda92e32

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg representative of a solution path

The Itô–Lévy formula at bounded derivatives asks for left limits of the solution at every sample
point and every time, while the well-posedness theorem produces paths that are càdlàg only on a
measurable set `G` of full measure. `cadlagRep G X` is the path map that agrees with `X` on `G` at
nonnegative times, is the constant zero path off `G`, and is frozen at the zero state before time
zero. It is càdlàg at every sample point and every time, adapted whenever `G` belongs to the
initial σ-algebra, progressively measurable because it is right-continuous everywhere, and solves
the equation on every window, because both stochastic integrals depend only on the class of their
integrand.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section CadlagRep

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

variable {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}

variable (hGp : ∀ ω ∈ G, ∀ t : ℝ, 0 ≤ t →
  Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
    ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))

end CadlagRep

section Representative

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E) {x₀ : Fin n → ℝ}
  {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}


theorem _root_.Prove2MeSourceProof.h_5480422f0c02d5366a6c8d44 (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hσq : ∀ (i : Fin n) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hXm : Measurable (Function.uncurry X))
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = x₀)
    (hGp : ∀ ω ∈ G, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (hXsol : ∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) (T : ℝ) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ (cadlagRep G X) T := by
  have hG : MeasurableSet[ℱ 0] G := by
    simpa using (hnull Gᶜ hGm.compl hG0).compl
  have hXad : ∀ t : ℝ, Measurable[ℱ t] (X t) := LevyStochCalc.Ito.JumpFormula.measurable_of_progressivelyMeasurable ℱ hXa
  have hYm : Measurable (Function.uncurry (LevyStochCalc.Ito.JumpFormula.cadlagRep G X)) := _root_.Prove2MeSourceProof.h_a73d9c684890e7b4cda92e32 hGm hXm
  have hYa : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => LevyStochCalc.Ito.JumpFormula.cadlagRep G X s ω i :=
    fun i => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_cadlagRep hGp hG hXad i
  have hσm : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => coeffs.σ s (LevyStochCalc.Ito.JumpFormula.cadlagRep G X s ω) i j) :=
    fun i j => ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσmeas)).comp
      (measurable_snd.prodMk (hYm.comp (measurable_snd.prodMk measurable_fst)))
  have hσp : ∀ i : Fin n, ∀ j : Fin d,
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (LevyStochCalc.Ito.JumpFormula.cadlagRep G X s ω) i j :=
    fun i j => LevyStochCalc.Ito.Picard.progressivelyMeasurable_comp_state hYa (f := fun s x => coeffs.σ s x i j)
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσmeas))
  have hσq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (LevyStochCalc.Ito.JumpFormula.cadlagRep G X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i j T' hT' => (LevyStochCalc.Ito.JumpFormula.lintegral_sq_comp_cadlagRep hG0 (fun s x => coeffs.σ s x i j) T').trans_lt
      (hσq i j T' hT')
  have hγm : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (LevyStochCalc.Ito.JumpFormula.cadlagRep G X p.2.1 p.1) p.2.2 i :=
    fun i => ((measurable_pi_apply i).comp hγmeas).comp
      ((measurable_fst.comp measurable_snd).prodMk
        ((hYm.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
          (measurable_snd.comp measurable_snd)))
  have hγp : ∀ i : Fin n,
      LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpFormula.cadlagRep G X s ω) e i :=
    fun i => _root_.Prove2MeSourceProof.h_ac85444679aa3a412d1927d4 hYa (g := fun s x e => coeffs.γ s x e i)
      ((measurable_pi_apply i).comp hγmeas)
  have hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (LevyStochCalc.Ito.JumpFormula.cadlagRep G X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun i T' hT' => (LevyStochCalc.Ito.JumpFormula.lintegral_sq_marked_comp_cadlagRep hG0 (fun s x e => coeffs.γ s x e i)
      T').trans_lt (hγq i T' hT')
  refine ⟨hσm, hσp, hσq, hγm, hγp, hγq, fun t ht => ?_⟩
  rcases ht.1.lt_or_eq with ht0 | ht0
  · -- at a positive time, the step reads the two paths on `[0, t]`, where they agree a.s.
    have hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        LevyStochCalc.Ito.JumpFormula.cadlagRep G X s ω = X s ω := by
      filter_upwards [LevyStochCalc.Ito.JumpFormula.ae_forall_cadlagRep_eq (P := P) hG0] with ω hω
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact hω s hs.1
    have hstep := LevyStochCalc.Ito.Picard.picardStep_congr_ae W N ℱ hℱW hℱN coeffs (LevyStochCalc.Ito.JumpFormula.cadlagRep G X) X x₀ hσm hσp hσq
      hγm hγp hγq (hXsol T).h_σ_meas (hXsol T).h_σ_progMeas (hXsol T).h_σ_sq
      (hXsol T).h_γ_meas (hXsol T).h_γ_progMeas (hXsol T).h_γ_sq ht0 hXY
    filter_upwards [hstep, (hXsol T).eqn t ht, LevyStochCalc.Ito.JumpFormula.ae_forall_cadlagRep_eq (P := P) hG0]
      with ω hω heq hagree
    intro i
    rw [hagree t ht.1, heq i, hω]
  · -- at time zero both sides are the initial state
    subst ht0
    filter_upwards [LevyStochCalc.Ito.JumpFormula.ae_cadlagRep_zero hG0 hX0,
      _root_.Prove2MeSourceProof.h_217f44132bf28379085aa30a W N ℱ hℱW hℱN coeffs (LevyStochCalc.Ito.JumpFormula.cadlagRep G X) x₀ hσm hσp hσq hγm hγp hγq]
      with ω h0 hstep
    intro i
    rw [h0, hstep i]
end Representative

end LevyStochCalc.Ito.JumpFormula


