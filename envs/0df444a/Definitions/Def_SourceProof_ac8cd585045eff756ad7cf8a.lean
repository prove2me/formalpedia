-- Prove2me | Definitions.Def_SourceProof_ac8cd585045eff756ad7cf8a
-- name    : SourceProof_ac8cd585045eff756ad7cf8a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:01:46.060188+00:00
-- url     : https://prove2.me/theorems/7257abb5-eefe-4392-885f-a028d9501be5
-- title:
--   LevyStochCalc source module: SourceProof_ac8cd585045eff756ad7cf8a
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift` comes from the `LevyStochCalc.Ito.ItoFormulaGeneralShift` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F000
import Definitions.Def_SourceProof_25e3d60ed503f0b298015a7e
import Definitions.Def_SourceProof_89a50fe7a0a3957d21cf10a4
import Definitions.Def_SourceProof_e25c34e865fb96c79ac03480
import Definitions.Def_SourceProof_e6dcd6270ba2ccc8443bc922

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for an increment translated by a general random vector

A random vector approached pointwise by random vectors for which Itô's formula between two
stopping times already holds carries the formula itself: the boundary term converges by
continuity of the function, the two Lebesgue terms converge along almost every path by
domination, and the stochastic term converges in `L²` because the energy of the difference of
two increments is at most four times the energy of the difference of the integrands, hence
almost surely along a subsequence common to the finitely many Brownian channels.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_stopped_sub_diff_le` — the energy of the difference of
  the increments of two integrands is at most four times the energy of their difference.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_of_energy` — a path of finite energy is almost
  surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_sum_mul` — the pointwise inner product of two
  families of paths of finite energy is almost surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift` — Itô's formula for the increment
  of a path between two stopping times, for a function translated by a general random vector.
* `LevyStochCalc.Brownian.Ito.dyadicShift` — the dyadic lattice point of a given resolution below
  a vector, coordinate by coordinate.
* `LevyStochCalc.Brownian.Ito.exists_simpleShift_approx` — a bounded random vector known at a
  stopping time is a pointwise limit of finitely valued random vectors known at that time.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section IncrementEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end IncrementEnergy

section WindowIntegrability

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end WindowIntegrability

section GeneralShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')


theorem _root_.Prove2MeSourceProof.h_ac8cd585045eff756ad7cf8a
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
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
    {cm : ℕ → Ω → Fin n → ℝ} (hcm : ∀ m, Measurable (cm m))
    (hlim : ∀ ω, Filter.Tendsto (fun m => cm m ω) Filter.atTop (𝓝 (c ω)))
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
    (hmScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s))
    (hpScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s)
    (hqScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hbase : ∀ m : ℕ,
      (fun ω : Ω => f (X (clipTime τ T ω) ω + cm m ω) - f (X (clipTime σ T ω) ω + cm m ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ
                (fun ω s => coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped τ
                      (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
                    - Probability.stopped σ
                        (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s)
                (hmScm m p k) (hpScm m p k) (hqScm m p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + cm m ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + cm m ω)
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
  have hmDm : ∀ (m : ℕ) (p : Fin n), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) := fun m p =>
    ((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp
      (hXm.add ((hcm m).comp measurable_fst))).mul (hbm p)
  have hmQm : ∀ (m : ℕ) (p q : Fin n), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + cm m ω)
        * ∑ k : Fin d, H p k ω s * H q k ω s) := by
    intro m p q
    refine ((LevyStochCalc.continuous_coordDeriv₂ hf''c p q).measurable.comp
      (hXm.add ((hcm m).comp measurable_fst))).mul ?_
    exact Finset.measurable_sum _ fun k _ => (hHm p k).mul (hHm q k)
  have hEnergy : ∀ i : Fin n × Fin d, Filter.Tendsto (fun m => ∫⁻ ω,
      ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Probability.stopped τ
                (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + cm m ω) * H i.1 i.2 ω s) ω s
              - LevyStochCalc.Probability.stopped σ
                  (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + cm m ω) * H i.1 i.2 ω s) ω s)
            - (LevyStochCalc.Probability.stopped τ
                  (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s
                - LevyStochCalc.Probability.stopped σ
                    (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s)‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
    rintro ⟨p, k⟩
    have hraw := _root_.Prove2MeSourceProof.h_e25c34e865fb96c79ac03480 (X := X) (LevyStochCalc.continuous_coordDeriv hf'c p)
      (hK₁ p) (hHm p k) hXm hcm hc hlim (hHs p k T hT).ne
    have hub : Filter.Tendsto (fun m => (4 : ℝ≥0∞) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s
          - LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (𝓝 (4 * 0)) :=
      ENNReal.Tendsto.const_mul hraw (Or.inr (by simp))
    rw [mul_zero] at hub
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
      (fun _ => zero_le) fun m => ?_
    exact LevyStochCalc.Brownian.Ito.lintegral_sq_stopped_sub_diff_le σ τ
      (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s)
      (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s) T
  obtain ⟨ms, hmsge, hSI⟩ := _root_.Prove2MeSourceProof.h_e6dcd6270ba2ccc8443bc922
    (fun i : Fin n × Fin d => W.W i.2) ℱ' (fun i => hcoord i.2)
    (fun m i ω s => LevyStochCalc.Probability.stopped τ
        (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + cm m ω) * H i.1 i.2 ω s) ω s
      - LevyStochCalc.Probability.stopped σ
          (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + cm m ω) * H i.1 i.2 ω s) ω s)
    (fun i ω s => LevyStochCalc.Probability.stopped τ
        (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s
      - LevyStochCalc.Probability.stopped σ
          (fun ω s => LevyStochCalc.coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s)
    (fun m i => hmScm m i.1 i.2) (fun m i => hpScm m i.1 i.2) (fun m i => hqScm m i.1 i.2)
    (fun i => hmSc i.1 i.2) (fun i => hpSc i.1 i.2) (fun i => hqSc i.1 i.2) hT hEnergy
  have hmsTop : Filter.Tendsto ms Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hmsge Filter.tendsto_id
  have hdrift : ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun m => ∫ s in Set.Ioc (0 : ℝ) T,
      (LevyStochCalc.Probability.stopped τ
          (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) ω s
        - LevyStochCalc.Probability.stopped σ
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped τ
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
          - LevyStochCalc.Probability.stopped σ
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)) := by
    filter_upwards [hbint] with ω hω p
    refine _root_.Prove2MeSourceProof.h_89a50fe7a0a3957d21cf10a4 (LevyStochCalc.continuous_coordDeriv hf'c p) (hK₁ p)
      (hlim ω) (hω p) fun m => ?_
    exact (Measurable.of_uncurry_left
      (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmDm m p))).aestronglyMeasurable
  have hquad : ∀ᵐ ω ∂P, ∀ p q : Fin n, Filter.Tendsto (fun m => ∫ s in Set.Ioc (0 : ℝ) T,
      (LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + cm m ω)
          * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
        - LevyStochCalc.Probability.stopped σ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + cm m ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + c ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - LevyStochCalc.Probability.stopped σ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + c ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)) := by
    filter_upwards [hQint] with ω hω p q
    refine _root_.Prove2MeSourceProof.h_25e3d60ed503f0b298015a7e (LevyStochCalc.continuous_coordDeriv₂ hf''c p q)
      (fun z s => hK₂ p q z ω s) (hlim ω) (hω p q) fun m => ?_
    exact (Measurable.of_uncurry_left
      (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmQm m p q))).aestronglyMeasurable
  refine LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_comp_of_forall_ae_eq ms hbase ?_ ?_
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hshift : ∀ z : Fin n → ℝ, Filter.Tendsto (fun m => z + cm m ω) Filter.atTop
        (𝓝 (z + c ω)) := fun z => Filter.Tendsto.const_add z (hlim ω)
    exact ((hfc.continuousAt.tendsto.comp (hshift (X (LevyStochCalc.Brownian.Ito.clipTime τ T ω) ω))).sub
      (hfc.continuousAt.tendsto.comp (hshift (X (LevyStochCalc.Brownian.Ito.clipTime σ T ω) ω)))).comp hmsTop
  · filter_upwards [hdrift, hquad, hSI] with ω h1 h2 h3
    refine ((tendsto_finsetSum _ fun p _ => (h1 p).comp hmsTop).add
      (tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun k _ => h3 (p, k))).add ?_
    exact (tendsto_finsetSum _ fun p _ =>
      tendsto_finsetSum _ fun q _ => (h2 p q).comp hmsTop).const_mul _
end GeneralShift

section DyadicApproximation

variable {Ω : Type u} [MeasurableSpace Ω]

end DyadicApproximation

end LevyStochCalc.Brownian.Ito


