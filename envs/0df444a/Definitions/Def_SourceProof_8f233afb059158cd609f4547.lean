-- Prove2me | Definitions.Def_SourceProof_8f233afb059158cd609f4547
-- name    : SourceProof_8f233afb059158cd609f4547
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:45:47.667054+00:00
-- url     : https://prove2.me/theorems/66232257-e8a6-46d5-82cf-7b93d13836d0
-- title:
--   LevyStochCalc source module: SourceProof_8f233afb059158cd609f4547
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.itoFormula_chain` comes from the `LevyStochCalc.Ito.JumpFormulaAssembly` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaAssembly_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a chain of stopping times

A path that evolves continuously between the members of a chain of times and is translated by a
vector held fixed on each of the intervals they cut out satisfies, after composition with a
function of the state, a telescoping identity: the increment over the whole window is the sum of
the increments with the translation frozen on each interval plus the sum of the increments of the
translation at the right endpoints. Where the translated path agrees with a second path, the
integrands of the per-interval Itô formulas coincide with the integrands built from that second
path, so the per-interval Lebesgue and Itô integrals collapse into single integrals over the
window.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_range_shift_telescope` — the pathwise telescoping identity.
* `LevyStochCalc.Brownian.Ito.stopped_sub_congr` — the increment of a cut-off integrand between
  two times depends on the integrand only between them.
* `LevyStochCalc.Brownian.Ito.stopped_sub_shift_funext` — the increment of the cut-off integrand
  of a translated path is the increment of the cut-off integrand of the path it agrees with.
* `LevyStochCalc.Brownian.Ito.sum_range_integral_stopped_sub_of_chain` — the Lebesgue integrals
  of the increments along a chain covering `(0, T]` sum to the integral over that window.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sum_range_stopped_sub_of_chain` — the
  Itô integrals of those increments sum to the Itô integral over that window.
* `LevyStochCalc.Brownian.Ito.itoFormula_chain` — Itô's formula over the window for a path
  translated piecewise along a chain, with the per-interval increments as a hypothesis.
* `LevyStochCalc.Brownian.Ito.itoFormula_chain_path` — the same with the two endpoints
  identified with the values of the path the translations agree with.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

section Pathwise

variable {Ω : Type*}

end Pathwise

section Support

variable {Ω : Type*}

end Support

section Collapse

variable {Ω : Type*}

end Collapse

section ItoCollapse

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end ItoCollapse

section Algebra

end Algebra

section Assembly

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ j : Fin d, IsBrownianFiltration (W.W j) ℱ')

include hcoord in

theorem _root_.Prove2MeSourceProof.h_8f233afb059158cd609f4547
    {H : Fin n → Fin d → Ω → ℝ → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
    {V X : ℝ → Ω → Fin n → ℝ} {c : ℕ → Ω → Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    {σ : ℕ → Ω → WithTop ℝ} (hσ : ∀ k, MeasureTheory.IsStoppingTime ℱ' (σ k))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hmG : ∀ (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p j ω s))
    (hpG : ∀ (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
    (hqG : ∀ (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmD : ∀ p : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s))
    (hqD : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmQ : ∀ p q : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s))
    (hmV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (σ (k + 1))
          (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
        - Probability.stopped (σ k)
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s))
    (hpV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped (σ (k + 1))
          (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
        - Probability.stopped (σ k)
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
    (hqV : ∀ (k : ℕ) (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖Probability.stopped (σ (k + 1))
              (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
            - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s)
      (Set.Ioc (0 : ℝ) T) volume)
    {m : ℕ} (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V s ω + c k ω = X s ω)
    (hcont : ∀ k < m, (fun ω : Ω => f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)
          - f (V (clipTime (σ k) T ω) ω + c k ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (σ (k + 1))
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s
              - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
              (fun ω s => Probability.stopped (σ (k + 1))
                  (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
                - Probability.stopped (σ k)
                    (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
              (hmV k p j)
              (hpV k p j)
              (hqV k p j) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped (σ (k + 1)) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
                - Probability.stopped (σ k) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
                    * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume) :
    ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) ≤ σ m ω →
      f (V T ω + c m ω) - f (V 0 ω + c 0 ω) =
      ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
              (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
              (hmG p j) (hpG p j) (hqG p j) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * (∑ j : Fin d, H p j ω s * H q j ω s) ∂volume)
        + ∑ k ∈ Finset.range m, (f (V (clipTime (σ (k + 1)) T ω) ω + c (k + 1) ω)
            - f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)) := by
  classical
  have hBfun : ∀ (k : ℕ) (p : Fin n) (j : Fin d),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => LevyStochCalc.Probability.stopped (σ (k + 1))
              (fun ω s => LevyStochCalc.coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
            - LevyStochCalc.Probability.stopped (σ k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
          (hmV k p j)
          (hpV k p j)
          (hqV k p j) T
        =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => LevyStochCalc.Probability.stopped (σ (k + 1))
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s) ω s
            - LevyStochCalc.Probability.stopped (σ k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s) ω s)
          (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) (hmG p j))
          (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) (hpG p j))
          (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmG p j) (hqG p j)) T := by
    intro k p j
    refine _root_.Prove2MeSourceProof.h_c2510fef121a9f6103ef8e5e (W.W j) ℱ' (hcoord j) _ _ _ _ _ _ hT ?_
    filter_upwards [hshift] with ω hω
    filter_upwards [MeasureTheory.ae_restrict_of_ae (LevyStochCalc.Brownian.Ito.ae_coe_ne (σ (k + 1) ω))] with s hs
    exact LevyStochCalc.Brownian.Ito.stopped_sub_shift_apply_of_lt (hmono k ω) (LevyStochCalc.coordDeriv f' p) (H p j) (hω k) hs
  have hBfunAll := (MeasureTheory.ae_all_iff (ι := ℕ)).2 fun k =>
    (MeasureTheory.ae_all_iff (ι := Fin n)).2 fun p =>
      (MeasureTheory.ae_all_iff (ι := Fin d)).2 fun j => hBfun k p j
  have hDint : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : ℕ), MeasureTheory.IntegrableOn
      (LevyStochCalc.Probability.stopped (σ k) (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω)
      (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc (hσ k) (hmD p) (hqD p) hT
  have hQstop : ∀ᵐ ω ∂P, ∀ (p q : Fin n) (k : ℕ), MeasureTheory.IntegrableOn
      (LevyStochCalc.Probability.stopped (σ k) (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
        * ∑ j : Fin d, H p j ω s * H q j ω s) ω) (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro q
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc_of_ae_integrableOn (hσ k) (hmQ p q)
      (by filter_upwards [hQint] with ω hω using hω p q)
  have hBcol : ∀ᵐ ω ∂P, ∀ (p : Fin n) (j : Fin d), ((T : ℝ) : WithTop ℝ) ≤ σ m ω →
      (∑ k ∈ Finset.range m, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => LevyStochCalc.Probability.stopped (σ (k + 1))
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s) ω s
            - LevyStochCalc.Probability.stopped (σ k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s) ω s)
          (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) (hmG p j))
          (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) (hpG p j))
          (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmG p j) (hqG p j)) T ω)
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
            (hmG p j) (hpG p j) (hqG p j) T ω := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sum_range_stopped_sub_of_chain (W.W j) ℱ' (hcoord j)
      σ hσ (hmG p j) (hpG p j) (hqG p j) (fun ω => le_of_eq (h0 ω)) hT
  have hcontAll := LevyStochCalc.Brownian.Ito.ae_forall_lt hcont
  filter_upwards [hcontAll, hBcol, hDint, hQstop, hBfunAll, hshift] with
    ω hcω hBω hDω hQω hBfω hshiftω hmTω
  have hAk : ∀ (k : ℕ) (p : Fin n), (∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped (σ (k + 1))
            (fun ω s => LevyStochCalc.coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s
          - LevyStochCalc.Probability.stopped (σ k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s) ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped (σ (k + 1))
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω s
          - LevyStochCalc.Probability.stopped (σ k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω s) ∂volume :=
    fun k p => MeasureTheory.integral_congr_ae (by
      filter_upwards [MeasureTheory.ae_restrict_of_ae (LevyStochCalc.Brownian.Ito.ae_coe_ne (σ (k + 1) ω))] with s hs
      exact LevyStochCalc.Brownian.Ito.stopped_sub_shift_apply_of_lt (hmono k ω) (LevyStochCalc.coordDeriv f' p) (bdrift p)
        (hshiftω k) hs)
  have hQk : ∀ (k : ℕ) (p q : Fin n), (∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped (σ (k + 1)) (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (V s ω + c k ω)
            * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
          - LevyStochCalc.Probability.stopped (σ k) (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (V s ω + c k ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped (σ (k + 1)) (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
            * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
          - LevyStochCalc.Probability.stopped (σ k) (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume :=
    fun k p q => MeasureTheory.integral_congr_ae (by
      filter_upwards [MeasureTheory.ae_restrict_of_ae (LevyStochCalc.Brownian.Ito.ae_coe_ne (σ (k + 1) ω))] with s hs
      exact LevyStochCalc.Brownian.Ito.stopped_sub_shift_apply_of_lt (hmono k ω) (LevyStochCalc.coordDeriv₂ f'' p q)
        (fun ω s => ∑ j : Fin d, H p j ω s * H q j ω s) (hshiftω k) hs)
  have hA : ∀ p : Fin n, (∑ k ∈ Finset.range m, ∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped (σ (k + 1))
            (fun ω s => LevyStochCalc.coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s
          - LevyStochCalc.Probability.stopped (σ k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s) ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume := by
    intro p
    have hstep := Finset.sum_congr (s₂ := Finset.range m) rfl
      fun k (_ : k ∈ Finset.range m) => hAk k p
    rw [hstep]
    exact LevyStochCalc.Brownian.Ito.sum_range_integral_stopped_sub_of_chain σ
      (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s)
      (le_of_eq (h0 ω)) hmTω fun k => hDω p k
  have hC : ∀ p q : Fin n, (∑ k ∈ Finset.range m, ∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped (σ (k + 1)) (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (V s ω + c k ω)
            * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
          - LevyStochCalc.Probability.stopped (σ k) (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (V s ω + c k ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * (∑ j : Fin d, H p j ω s * H q j ω s) ∂volume := by
    intro p q
    have hstep := Finset.sum_congr (s₂ := Finset.range m) rfl
      fun k (_ : k ∈ Finset.range m) => hQk k p q
    rw [hstep]
    exact LevyStochCalc.Brownian.Ito.sum_range_integral_stopped_sub_of_chain σ
      (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s)
      (le_of_eq (h0 ω)) hmTω fun k => hQω p q k
  have hB : ∀ (p : Fin n) (j : Fin d), (∑ k ∈ Finset.range m,
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => LevyStochCalc.Probability.stopped (σ (k + 1))
              (fun ω s => LevyStochCalc.coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
            - LevyStochCalc.Probability.stopped (σ k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
          (hmV k p j)
          (hpV k p j)
          (hqV k p j) T ω)
      = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
          (hmG p j) (hpG p j) (hqG p j) T ω := by
    intro p j
    have hstep := Finset.sum_congr (s₂ := Finset.range m) rfl
      fun k (_ : k ∈ Finset.range m) => hBfω k p j
    rw [hstep]
    exact hBω p j hmTω
  have htel : f (V (LevyStochCalc.Brownian.Ito.clipTime (σ m) T ω) ω + c m ω) - f (V (LevyStochCalc.Brownian.Ito.clipTime (σ 0) T ω) ω + c 0 ω)
      = (∑ k ∈ Finset.range m, (f (V (LevyStochCalc.Brownian.Ito.clipTime (σ (k + 1)) T ω) ω + c k ω)
            - f (V (LevyStochCalc.Brownian.Ito.clipTime (σ k) T ω) ω + c k ω)))
        + ∑ k ∈ Finset.range m, (f (V (LevyStochCalc.Brownian.Ito.clipTime (σ (k + 1)) T ω) ω + c (k + 1) ω)
            - f (V (LevyStochCalc.Brownian.Ito.clipTime (σ (k + 1)) T ω) ω + c k ω)) :=
    LevyStochCalc.Brownian.Ito.sum_range_shift_telescope f V c (fun k ω => LevyStochCalc.Brownian.Ito.clipTime (σ k) T ω) m ω
  rw [LevyStochCalc.Brownian.Ito.clipTime_of_le hmTω, LevyStochCalc.Brownian.Ito.clipTime_eq_zero hT.le (h0 ω)] at htel
  have hsub := Finset.sum_congr (s₂ := Finset.range m) rfl
    fun k (hk : k ∈ Finset.range m) => hcω k (Finset.mem_range.mp hk)
  rw [htel, hsub, LevyStochCalc.Brownian.Ito.sum_range_itoTerms hA hB hC]
end Assembly

end LevyStochCalc.Brownian.Ito


