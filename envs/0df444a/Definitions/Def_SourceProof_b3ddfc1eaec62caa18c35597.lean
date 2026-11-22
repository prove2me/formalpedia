-- Prove2me | Definitions.Def_SourceProof_b3ddfc1eaec62caa18c35597
-- name    : SourceProof_b3ddfc1eaec62caa18c35597
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:27:56.547339+00:00
-- url     : https://prove2.me/theorems/1229cca4-d3c6-4d2b-9a46-c4f062f0ae9b
-- title:
--   LevyStochCalc source module: SourceProof_b3ddfc1eaec62caa18c35597
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.itoFormula_between_boundedShift` comes from the `LevyStochCalc.Ito.ItoFormulaMeasurableShift` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
import Definitions.Def_SourceProof_065e60a1696464e96f1fa2c5
import Definitions.Def_SourceProof_7fa7fe0bc88fc930b0470bf0
import Definitions.Def_SourceProof_ac8cd585045eff756ad7cf8a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula between two stopping times for a shift known at the earlier time

A random variable known at a stopping time, cut to the event that the time has already occurred by
a deterministic time, is measurable for the σ-algebra at that deterministic time; multiplying by
such a variable therefore preserves progressive measurability of a process that vanishes up to the
stopping time. Reading an integrand along a mark taking finitely many values splits the increment
of the integrand between two ordered stopping times over the values of the mark, so that increment
is progressively measurable as soon as the mark is known at the earlier time. The dyadic lattice
points below a bounded random vector known at the earlier stopping time form such marks and
converge to it, and truncating a random vector on the event that its norm exceeds a level produces
bounded vectors eventually equal to it, so Itô's formula for the increment holds for a shift that
is merely known at the earlier stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stoppingTimeWeight_mul` — a random variable
  known at a stopping time times a progressively measurable process vanishing up to that time is
  progressively measurable.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_of_measurableShift` — the
  increment between two ordered stopping times of an integrand read along a mark taking finitely
  many values and known at the earlier time is progressively measurable.
* `LevyStochCalc.Brownian.Ito.exists_simpleShift_approx_measurableSpace` — a bounded random vector
  known at a stopping time is a pointwise limit of random vectors taking finitely many values and
  known at that stopping time.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_boundedShift` — Itô's formula for the increment of
  a path between two stopping times, for a function translated by a bounded random vector known at
  the earlier time.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_measurableShift` — the same for a function
  translated by a random vector known at the earlier time and subject to no bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Weight

variable {Ω : Type u} [MeasurableSpace Ω]

end Weight

section MarkDecomposition

variable {Ω : Type u} {α : Type*}

end MarkDecomposition

section SimpleMark

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*} [MeasurableSpace α]
  [MeasurableSingletonClass α]

end SimpleMark

section TwoPieceMark

variable {Ω : Type u}

end TwoPieceMark

section Approximation

variable {Ω : Type u} [MeasurableSpace Ω]

end Approximation

section MeasurableShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')


theorem _root_.Prove2MeSourceProof.h_b3ddfc1eaec62caa18c35597
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ) (hστ : ∀ ω, σ ω ≤ τ ω)
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
    {c : Ω → Fin n → ℝ} (hc : Measurable[hσ.measurableSpace] c)
    {M : ℝ} (hcb : ∀ ω, ‖c ω‖ ≤ M)
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
          ∂volume ∂P < ⊤) :
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
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := h.measurable_uncurry
  have hcmeas : Measurable c := hc.mono hσ.measurableSpace_le le_rfl
  have hf'c : Continuous f' := Differentiable.continuous fun z => (hf' z).differentiableAt
  have hpG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * H p k ω s := fun v p k =>
    (h.progressivelyMeasurable_comp (φ := fun z => LevyStochCalc.coordDeriv f' p (z + v))
      ((LevyStochCalc.continuous_coordDeriv hf'c p).comp (continuous_id.add continuous_const))).mul (hHp p k)
  obtain ⟨cm, Vs, hcmσ, hcmVs, hlim⟩ := LevyStochCalc.Brownian.Ito.exists_simpleShift_approx_measurableSpace hσ hc hcb
  have hcmm : ∀ m, Measurable (cm m) := fun m => (hcmσ m).mono hσ.measurableSpace_le le_rfl
  have hmGcm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s) := fun m p k =>
    ((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp
      (hXm.add ((hcmm m).comp measurable_fst))).mul (hHm p k)
  have hqGcm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro m p k
    refine LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le_mul (le_trans (abs_nonneg _) (hK₁ p 0)) ?_ (hHs p k)
    intro ω s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  have hmScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
        - LevyStochCalc.Probability.stopped σ
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s) :=
    fun m p k => LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmGcm m p k)
  have hpScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
          - LevyStochCalc.Probability.stopped σ
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s :=
    fun m p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_of_measurableShift hσ hτ hστ (hcmσ m)
      (hcmVs m) (fun v ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * H p k ω s) (fun v => hpG v p k)
      (Kc := fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s) fun _ _ => rfl
  have hqScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.Probability.stopped τ
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
            - LevyStochCalc.Probability.stopped σ
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun m p k => LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top hσ hτ (hmGcm m p k) (hqGcm m p k)
  have hbint : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (fun s => bdrift p ω s) (Set.Ioc (0 : ℝ) T) volume :=
    MeasureTheory.ae_all_iff.mpr fun p => LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_of_energy (hbm p) (hbq p T hT)
  have hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Ioc (0 : ℝ) T) volume :=
    _root_.Prove2MeSourceProof.h_065e60a1696464e96f1fa2c5 hHm fun p k => hHs p k T hT
  exact _root_.Prove2MeSourceProof.h_ac8cd585045eff756ad7cf8a W ℱ' hcoord hXm hHm hHs hbm hσ hτ hfC hf hf' hK₁ hK₂ hT
    hcmeas hcmm hlim hbint hQint hmSc hpSc hqSc hmScm hpScm hqScm fun m =>
      _root_.Prove2MeSourceProof.h_7fa7fe0bc88fc930b0470bf0 W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq
        hσ hτ hστ hσ0 hτ0 hfC hf hf' hK₁ hK₂ hT (hcmσ m) (hcmVs m) (hmScm m) (hpScm m) (hqScm m)
end MeasurableShift

end LevyStochCalc.Brownian.Ito


