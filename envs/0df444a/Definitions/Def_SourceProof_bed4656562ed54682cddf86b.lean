-- Prove2me | Definitions.Def_SourceProof_bed4656562ed54682cddf86b
-- name    : SourceProof_bed4656562ed54682cddf86b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:19:55.403749+00:00
-- url     : https://prove2.me/theorems/34b2e3e5-d5b2-4cbd-a9b1-2b266270ef99
-- title:
--   LevyStochCalc source module: SourceProof_bed4656562ed54682cddf86b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift` comes from the `LevyStochCalc.Ito.ItoFormulaGridShift` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGridShift_F000
import Definitions.Def_SourceProof_e6dcd6270ba2ccc8443bc922
import Definitions.Def_SourceProof_ec9b353ac49d35cb2a8d9aa5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula between two stopping times of unrestricted range

A stopping time is approximated from above by the stopping time that stops at the first point of
a uniform grid strictly beyond it, which takes finitely many values below the horizon. Itô's
formula for the increment of a path between two such discretisations, for a `C²` function
translated by a random vector, passes to the limit: the boundary term converges by continuity of
the function and of the path, the two Lebesgue terms converge along almost every path by
domination, and the stochastic term converges in `L²` because the energy of the difference of two
increments is at most twice the sum of the two energies, hence almost surely along a subsequence
common to the finitely many Brownian channels.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurableSpace_le_gridStop` — the σ-algebra of a stopping time is
  contained in that of its upward grid discretisation.
* `LevyStochCalc.Brownian.Ito.tendsto_stopped_gridStop` — the integrand cut off at the grid
  discretisations converges pointwise at every positive time of the window.
* `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_gridStop` — the Lebesgue terms
  converge along the path.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_sub_gridStop` — the increments cut off at the
  grid discretisations converge in the energy of the window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift` — Itô's formula for the increment of a
  path between two stopping times of unrestricted range.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section GridMeasurableSpace

variable {Ω : Type u} [MeasurableSpace Ω]

end GridMeasurableSpace

section PointwiseLimit

variable {Ω : Type u}

end PointwiseLimit

section LebesgueTerm

variable {Ω : Type u} [MeasurableSpace Ω]

end LebesgueTerm

section EnergyTerm

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end EnergyTerm

section GridShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')


theorem _root_.Prove2MeSourceProof.h_bed4656562ed54682cddf86b
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (hXc : ∀ ω, Continuous fun s : ℝ => X s ω)
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ K₂ : ℝ} (hK₁ : ∀ (p : Fin n) (z : Fin n → ℝ), |coordDeriv f' p z| ≤ K₁)
    (hK₂ : ∀ (p q : Fin n) (z : Fin n → ℝ) (ω : Ω) (s : ℝ),
      |coordDeriv₂ f'' p q z| * |∑ k : Fin d, H p k ω s * H q k ω s|
        ≤ K₂ * |∑ k : Fin d, H p k ω s * H q k ω s|)
    {T : ℝ} (hT : 0 < T)
    {c : Ω → Fin n → ℝ} (hc : Measurable c)
    (hbint : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (fun s => bdrift p ω s) (Set.Ioc (0 : ℝ) T) volume)
    (hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Ioc (0 : ℝ) T) volume)
    (hmSc : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSc : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSc : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStop τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStop σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped (gridStop τ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped (gridStop σ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped (gridStop σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hbase : ∀ m : ℕ,
      (fun ω : Ω => f (X (clipTime (gridStop τ T m) T ω) ω + c ω)
          - f (X (clipTime (gridStop σ T m) T ω) ω + c ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (gridStop τ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
              - Probability.stopped (gridStop σ T m)
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped (gridStop τ T m)
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                    - Probability.stopped (gridStop σ T m)
                        (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
                (hmSm m p k) (hpSm m p k) (hqSm m p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped (gridStop τ T m)
                  (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped (gridStop σ T m)
                    (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                      * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c ω) - f (X (clipTime σ T ω) ω + c ω))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSc p k) (hpSc p k) (hqSc p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
  classical
  have hfc : Continuous f := Differentiable.continuous fun z => (hf z).differentiableAt
  have hf'c : Continuous f' := Differentiable.continuous fun z => (hf' z).differentiableAt
  have hf''c : Continuous f'' := by
    have h1 : f' = fderiv ℝ f := funext fun z => (hf z).fderiv.symm
    have h2 : f'' = fderiv ℝ f' := funext fun z => (hf' z).fderiv.symm
    rw [h2, h1]
    exact ((hfC.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuous
  have hXcm : Measurable (Function.uncurry fun ω s => X s ω + c ω) :=
    hXm.add (hc.comp measurable_fst)
  have hmG : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s) :=
    fun p k => ((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp hXcm).mul (hHm p k)
  have hmD : ∀ p : Fin n, Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * bdrift p ω s) :=
    fun p => ((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp hXcm).mul (hbm p)
  have hmQ : ∀ p q : Fin n, Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + c ω)
        * ∑ k : Fin d, H p k ω s * H q k ω s) := by
    intro p q
    refine ((LevyStochCalc.continuous_coordDeriv₂ hf''c p q).measurable.comp hXcm).mul ?_
    exact Finset.measurable_sum _ fun k _ => (hHm p k).mul (hHm q k)
  have hqG : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p k
    refine LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le_mul (le_trans (abs_nonneg _) (hK₁ p 0)) ?_ (hHs p k) T hT
    intro ω s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  have hdrift : ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun m : ℕ =>
      ∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ T m)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
          - LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop σ T m)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped τ
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
          - LevyStochCalc.Probability.stopped σ
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)) := by
    filter_upwards [hbint] with ω hω p
    refine LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_gridStop hσ hτ (hmD p) (bdrift p) K₁
      (fun ω s => ?_) hT (hω p)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  have hquad : ∀ᵐ ω ∂P, ∀ p q : Fin n, Filter.Tendsto (fun m : ℕ =>
      ∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ T m)
            (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + c ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop σ T m)
              (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + c ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - LevyStochCalc.Probability.stopped σ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + c ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)) := by
    filter_upwards [hQint] with ω hω p q
    refine LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_gridStop hσ hτ (hmQ p q)
      (fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) K₂ (fun ω s => ?_) hT (hω p q)
    rw [abs_mul]
    exact hK₂ p q _ ω s
  obtain ⟨ms, hmsge, hSI⟩ := _root_.Prove2MeSourceProof.h_e6dcd6270ba2ccc8443bc922
    (fun i : Fin n × Fin d => W.W i.2) ℱ' (fun i => hcoord i.2)
    (fun m i ω s => LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ T m)
        (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s
      - LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop σ T m)
          (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s)
    (fun i ω s => LevyStochCalc.Probability.stopped τ
        (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s
      - LevyStochCalc.Probability.stopped σ
          (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s)
    (fun m i => hmSm m i.1 i.2) (fun m i => hpSm m i.1 i.2) (fun m i => hqSm m i.1 i.2)
    (fun i => hmSc i.1 i.2) (fun i => hpSc i.1 i.2) (fun i => hqSc i.1 i.2) hT
    (fun i => LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_sub_gridStop hσ hτ (hmG i.1 i.2) hT (hqG i.1 i.2))
  have hmsTop : Filter.Tendsto ms Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hmsge Filter.tendsto_id
  refine LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_comp_of_forall_ae_eq ms hbase ?_ ?_
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hXτ : Filter.Tendsto (fun m : ℕ => X (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Brownian.Ito.gridStop τ T m) T ω) ω + c ω)
        Filter.atTop (𝓝 (X (LevyStochCalc.Brownian.Ito.clipTime τ T ω) ω + c ω)) :=
      (((hXc ω).tendsto _).comp (_root_.Prove2MeSourceProof.h_ec9b353ac49d35cb2a8d9aa5 τ hτ0 hT ω)).add tendsto_const_nhds
    have hXσ : Filter.Tendsto (fun m : ℕ => X (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Brownian.Ito.gridStop σ T m) T ω) ω + c ω)
        Filter.atTop (𝓝 (X (LevyStochCalc.Brownian.Ito.clipTime σ T ω) ω + c ω)) :=
      (((hXc ω).tendsto _).comp (_root_.Prove2MeSourceProof.h_ec9b353ac49d35cb2a8d9aa5 σ hσ0 hT ω)).add tendsto_const_nhds
    exact ((hfc.continuousAt.tendsto.comp hXτ).sub
      (hfc.continuousAt.tendsto.comp hXσ)).comp hmsTop
  · filter_upwards [hdrift, hquad, hSI] with ω h1 h2 h3
    refine ((tendsto_finsetSum _ fun p _ => (h1 p).comp hmsTop).add
      (tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun k _ => h3 (p, k))).add ?_
    exact (tendsto_finsetSum _ fun p _ =>
      tendsto_finsetSum _ fun q _ => (h2 p q).comp hmsTop).const_mul _
end GridShift

end LevyStochCalc.Brownian.Ito


