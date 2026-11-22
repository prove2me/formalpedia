-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F001
-- name    : LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:52:35.3661+00:00
-- url     : https://prove2.me/theorems/db4f09e1-e3f7-445d-acf9-f8bf5ee1bbfd
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F000

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

omit [MeasurableSpace Ω] in
include hGp in
/-- The representative is right-continuous at every sample point and every time, when the
original paths are càdlàg on the good set. -/
theorem cadlagRep_rightContinuous (ω : Ω) (t : ℝ) :
    Tendsto (fun s => cadlagRep G X s ω) (𝓝[>] t) (𝓝 (cadlagRep G X t ω)) := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [cadlagRep_of_neg ht]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
    exact (cadlagRep_of_neg (Set.mem_Iio.mp hs) ω).symm
  · rw [cadlagRep_of_nonneg ht]
    refine (repairOn_cadlag hGp ω t ht).1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (cadlagRep_of_nonneg (ht.trans (le_of_lt (Set.mem_Ioi.mp hs))) ω).symm
omit [MeasurableSpace Ω] in
include hGp in
/-- Every coordinate of the representative has a left limit at every sample point and every
time, when the original paths are càdlàg on the good set. -/
theorem cadlagRep_leftLim (ω : Ω) (t : ℝ) (i : Fin n) :
    ∃ L : ℝ, Tendsto (fun s => cadlagRep G X s ω i) (𝓝[<] t) (𝓝 L) := by
  rcases le_or_gt t 0 with ht | ht
  · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [cadlagRep_of_neg (lt_of_lt_of_le (Set.mem_Iio.mp hs) ht)]
    rfl
  · obtain ⟨L, hL⟩ := (repairOn_cadlag hGp ω t ht.le).2 i
    refine ⟨L, hL.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    rw [cadlagRep_of_nonneg hs.1.le]
omit [MeasurableSpace Ω] in
include hGp in
/-- The representative is càdlàg at every sample point and every time. -/
theorem cadlagRep_cadlag (ω : Ω) (t : ℝ) :
    Tendsto (fun s => cadlagRep G X s ω) (𝓝[>] t) (𝓝 (cadlagRep G X t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => cadlagRep G X s ω i) (𝓝[<] t) (𝓝 L) :=
  ⟨cadlagRep_rightContinuous hGp ω t, cadlagRep_leftLim hGp ω t⟩
/-- The representative is adapted whenever the original path is adapted and the good set belongs
to the initial σ-algebra. -/
theorem measurable_cadlagRep {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hG : MeasurableSet[ℱ 0] G) (hX : ∀ t : ℝ, Measurable[ℱ t] (X t)) (t : ℝ) :
    Measurable[ℱ t] (cadlagRep G X t) := by
  classical
  rcases lt_or_ge t 0 with ht | ht
  · have hz : cadlagRep G X t = fun _ => 0 := funext fun ω => cadlagRep_of_neg ht ω
    rw [hz]
    exact measurable_const
  · have hite : cadlagRep G X t = fun ω => if ω ∈ G then X t ω else 0 := by
      funext ω
      rw [cadlagRep_of_nonneg ht]
      by_cases hω : ω ∈ G <;> simp [repairOn, hω]
    rw [hite]
    exact Measurable.ite (ℱ.mono ht _ hG) (hX t) measurable_const
include hGp in
/-- The representative is progressively measurable: it is adapted and right-continuous. -/
theorem progressivelyMeasurable_cadlagRep {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hG : MeasurableSet[ℱ 0] G) (hX : ∀ t : ℝ, Measurable[ℱ t] (X t)) (i : Fin n) :
    ProgressivelyMeasurable ℱ fun ω s => cadlagRep G X s ω i :=
  _root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421
    (fun t => (measurable_pi_apply i).comp (measurable_cadlagRep hG hX t))
    (fun ω t => ((continuous_apply i).tendsto _).comp (cadlagRep_rightContinuous hGp ω t))
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

/-- A path map adapted to the initial σ-algebra at time `0` is adapted at every time, once it is
progressively measurable. -/
theorem measurable_of_progressivelyMeasurable
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i) (t : ℝ) :
    Measurable[ℱ t] (X t) := by
  letI : MeasurableSpace Ω := ℱ t
  exact measurable_pi_lambda _ fun i => ((hXa i).stronglyMeasurable_eval t).measurable
omit [IsProbabilityMeasure P] in
/-- The representative starts at the initial state almost surely. -/
theorem ae_cadlagRep_zero (hG0 : P Gᶜ = 0) (hX0 : ∀ᵐ ω ∂P, X 0 ω = x₀) :
    ∀ᵐ ω ∂P, cadlagRep G X 0 ω = x₀ := by
  filter_upwards [mem_ae_iff.mpr hG0, hX0] with ω hω h0
  rw [cadlagRep_eq_of_mem le_rfl hω, h0]
omit [IsProbabilityMeasure P] in
/-- The representative agrees with the original path at every nonnegative time, almost surely. -/
theorem ae_forall_cadlagRep_eq (hG0 : P Gᶜ = 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → cadlagRep G X s ω = X s ω := by
  filter_upwards [mem_ae_iff.mpr hG0] with ω hω s hs
  exact cadlagRep_eq_of_mem hs hω
omit [IsProbabilityMeasure P] in
/-- The representative has the same running second moment as the original path. -/
theorem lintegral_iSup_cadlagRep (hG0 : P Gᶜ = 0) (T' : ℝ) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖cadlagRep G X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P
      = ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_cadlagRep_eq (P := P) hG0] with ω hω
  exact iSup_congr fun t => by rw [hω t t.2.1]
omit [IsProbabilityMeasure P] in
/-- A function of the time and the state has the same window energy along the representative as
along the original path. -/
theorem lintegral_sq_comp_cadlagRep (hG0 : P Gᶜ = 0) (f : ℝ → (Fin n → ℝ) → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (cadlagRep G X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_cadlagRep_eq (P := P) hG0] with ω hω
  exact setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [hω s hs.1]
omit [IsProbabilityMeasure P] in
/-- A marked function of the time and the state has the same window energy along the
representative as along the original path. -/
theorem lintegral_sq_marked_comp_cadlagRep {E : Type*} [MeasurableSpace E] {ν : Measure E}
    (hG0 : P Gᶜ = 0) (g : ℝ → (Fin n → ℝ) → E → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖g s (cadlagRep G X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g s (X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_cadlagRep_eq (P := P) hG0] with ω hω
  exact setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [hω s hs.1]
end Representative

end LevyStochCalc.Ito.JumpFormula


