-- Prove2me | Definitions.Def_SourceProof_bec416f96d2158f67c5c93e0
-- name    : SourceProof_bec416f96d2158f67c5c93e0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:24:22.397908+00:00
-- url     : https://prove2.me/theorems/358c3383-23cf-4dc2-a8aa-349f24474648
-- title:
--   LevyStochCalc source module: SourceProof_bec416f96d2158f67c5c93e0
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general` comes from the `LevyStochCalc.Ito.ItoFormulaStoppedLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_d98ac01e208c6728591ec0a2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a path stopped at an arbitrary stopping time

A stopping time is approximated from above by the stopping times that stop at the first point of
a uniform grid strictly beyond it, which take finitely many values. The horizons clipped at the
approximations converge to the horizon clipped at the stopping time, the integrands cut off at the
approximations converge in the energy of a window to the integrand cut off at the stopping time,
and Itô's formula along the finite-range stopped paths passes to the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop` — the clipped horizons converge.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_gridStop` — the cut-off integrands converge
  in the energy of the window.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped_general` — the process stopped at a
  stopping time is the vector Itô process of the stopped coefficients.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general` — Itô's formula along the stopped path.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section ClipLimit

variable {Ω : Type u}

end ClipLimit

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Energy

section StoppedGeneral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

include hcoord in

theorem _root_.Prove2MeSourceProof.h_bec416f96d2158f67c5c93e0
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume := by
  classical
  have hstop := _root_.Prove2MeSourceProof.h_d98ac01e208c6728591ec0a2 W ℱ' hcoord h hbm hbq hτ hτ0
  have hG : ∀ (p : Fin n) (k : Fin d),
      (fun ω s => LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω)
          * LevyStochCalc.Probability.stopped τ (H p k) ω s)
        = LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s) :=
    fun p k => LevyStochCalc.Brownian.Ito.stopped_comp_eq τ (LevyStochCalc.coordDeriv f' p) (H p k)
  have hGb : ∀ p : Fin n,
      (fun ω s => LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω)
          * LevyStochCalc.Probability.stopped τ (bdrift p) ω s)
        = LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) :=
    fun p => LevyStochCalc.Brownian.Ito.stopped_comp_eq τ (LevyStochCalc.coordDeriv f' p) (bdrift p)
  have hGq : ∀ p q : Fin n,
      (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω)
          * ∑ k : Fin d, LevyStochCalc.Probability.stopped τ (H p k) ω s
              * LevyStochCalc.Probability.stopped τ (H q k) ω s)
        = LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) :=
    fun p q => LevyStochCalc.Brownian.Ito.stopped_comp₂_eq τ (LevyStochCalc.coordDeriv₂ f'' p q) (fun k => H p k) (fun k => H q k)
  have hmgτ : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω)
        * LevyStochCalc.Probability.stopped τ (H p k) ω s) := by
    intro p k
    rw [hG p k]
    exact hmg p k
  have hpgτ : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      fun ω s => LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω)
        * LevyStochCalc.Probability.stopped τ (H p k) ω s := by
    intro p k
    rw [hG p k]
    exact hpg p k
  have hqgτ : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω)
          * LevyStochCalc.Probability.stopped τ (H p k) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p k
    have hthis := hqg p k
    rw [← hG p k] at hthis
    exact hthis
  have hres := LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded W ℱ' hcoord hstop hℱ0 hnull hX₀
    (fun p => LevyStochCalc.Probability.measurable_uncurry_stopped hτ (hbm p))
    (fun p => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ (hbp p))
    (fun p T' hT' => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le
      (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ (bdrift p) ω s) (hbq p) T' hT')
    hfC hf hf' hmgτ hpgτ hqgτ hT
  have hSI : ∀ (p : Fin n) (k : Fin d),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω)
            * LevyStochCalc.Probability.stopped τ (H p k) ω s)
          (hmgτ p k) (hpgτ p k) (hqgτ p k) T
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (LevyStochCalc.Probability.stopped τ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
          (hmg p k) (hpg p k) (hqg p k) T :=
    fun p k => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun (W.W k) ℱ' (hcoord k) (hG p k)
      (hmgτ p k) (hpgτ p k) (hqgτ p k) (hmg p k) (hpg p k) (hqg p k) T
  filter_upwards [hres] with ω hω
  rw [LevyStochCalc.Brownian.Ito.clipTime_of_le (hτ0 ω)] at hω
  have e1 : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω) * LevyStochCalc.Probability.stopped τ (bdrift p) ω s ∂volume)
      = ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω s
          ∂volume := by
    refine Finset.sum_congr rfl fun p _ => ?_
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      fun s _ => congrFun (congrFun (hGb p) ω) s
  have e2 : (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s => LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω)
          * LevyStochCalc.Probability.stopped τ (H p k) ω s) (hmgτ p k) (hpgτ p k) (hqgτ p k) T ω)
      = ∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (LevyStochCalc.Probability.stopped τ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
        (hmg p k) (hpg p k) (hqg p k) T ω :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => congrFun (hSI p k) ω
  have e3 : (1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.clipTime τ s ω) ω)
          * ∑ k : Fin d, LevyStochCalc.Probability.stopped τ (H p k) ω s
              * LevyStochCalc.Probability.stopped τ (H q k) ω s ∂volume)
      = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
          * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume := by
    refine congrArg (fun x => 1 / 2 * x) ?_
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      fun s _ => congrFun (congrFun (hGq p q) ω) s
  rw [hω, e1, e2, e3]
end StoppedGeneral

end LevyStochCalc.Brownian.Ito


