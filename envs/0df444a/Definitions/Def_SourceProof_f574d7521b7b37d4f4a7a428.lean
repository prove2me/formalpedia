-- Prove2me | Definitions.Def_SourceProof_f574d7521b7b37d4f4a7a428
-- name    : SourceProof_f574d7521b7b37d4f4a7a428
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:38:16.090479+00:00
-- url     : https://prove2.me/theorems/c37eed6b-b3d2-4360-b380-3dbcc6314761
-- title:
--   LevyStochCalc source module: SourceProof_f574d7521b7b37d4f4a7a428
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_of_isItoLevyProcess` comes from the `LevyStochCalc.Ito.SecondMomentQuadratic` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F002
import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F003
import Definitions.Def_SourceProof_07b9943ba0f4880793c268df
import Definitions.Def_SourceProof_1b671b96dc934c6fb0df20bc
import Definitions.Def_SourceProof_20d586a8e09491862e290520
import Definitions.Def_SourceProof_39285c9e8cb91346b858af97
import Definitions.Def_SourceProof_52bc6f9c5c34d4f858067e35
import Definitions.Def_SourceProof_da55a4195e0b45ce7b0016e9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic second moment of an Itô–Lévy process

For an Itô–Lévy process `X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ` over a Lévy
driver, with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift, the second moment at a time `T > 0` is

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`,

the expectation form of the quadratic Itô formula, under the `L²` hypotheses alone: no fourth
moment and no pathwise formula is used. Summing over the coordinates gives the vector form, and
the cross witness carried by the driver gives the form over its augmented joint natural
filtration. The polarised isometry for the compensated integral, the expected product of two
compensated integrals at a time being the expected time integral of the product of their
integrands against the Lévy measure, is proved here alongside.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section PolarisedMarked

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

end PolarisedMarked

section Scalar

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}


theorem _root_.Prove2MeSourceProof.h_f574d7521b7b37d4f4a7a428
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + 2 * (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b s ω ∂P)
        + (∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal := by
  classical
  -- the three pieces of the decomposition
  set S : Fin d → ℝ → Ω → ℝ := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j)
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) with hSdef
  set C : ℝ → Ω → ℝ :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq
    with hCdef
  set Dr : ℝ → Ω → ℝ := fun t ω => ∫ s in Set.Icc (0 : ℝ) t, b s ω with hDrdef
  have hdec : ∀ t, 0 ≤ t → ∀ᵐ ω ∂P,
      X t ω = X₀ ω + Dr t ω + (∑ j, S j t ω) + C t ω := fun t ht => h.decomposition t ht
  -- square integrability of every piece
  have hS2 : ∀ (j : Fin d) (t : ℝ), MemLp (S j t) 2 P := fun j t =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t
  have hSsum2 : ∀ t, MemLp (fun ω => ∑ j, S j t ω) 2 P := fun t =>
    memLp_finsetSum Finset.univ fun j _ => hS2 j t
  have hC2 : ∀ t, MemLp (C t) 2 P := fun t =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq t
  have hbq' : ∀ t, 0 ≤ t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun t ht => LevyStochCalc.Ito.SecondMoment.energy_lt_top_of_nonneg (f := fun ω s => b s ω) hbq ht
  have hDr2 : ∀ t, 0 ≤ t → MemLp (Dr t) 2 P := fun t ht =>
    LevyStochCalc.Ito.SecondMoment.memLp_two_setIntegral (f := fun ω s => b s ω) hbm ht (hbq' t ht)
  -- the isometries
  have hSiso : ∀ j, ∫ ω, S j T ω * S j T ω ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    intro j
    rw [LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_toReal (hS2 j T)]
    congr 1
    exact _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) hT
  have hCiso : ∫ ω, C T ω * C T ω ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal := by
    rw [LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_toReal (hC2 T)]
    congr 1
    exact LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq T hT
  -- the orthogonalities
  have hSS : ∀ j k, j ≠ k → ∫ ω, S j T ω * S k T ω ∂P = 0 := fun j k hjk =>
    _root_.Prove2MeSourceProof.h_52bc6f9c5c34d4f858067e35
      D.W hjk hℱW (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) (h.σ_meas k) (h.σ_prog k) (h.σ_sq k) hT.le
  have hSC : ∀ j, ∫ ω, S j T ω * C T ω ∂P = 0 := fun j =>
    _root_.Prove2MeSourceProof.h_da55a4195e0b45ce7b0016e9 𝒲 hℱW hℱN
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) h.γ_meas h.γ_prog h.γ_sq hT.le
  have hSsum_sq : ∫ ω, (∑ j, S j T ω) * (∑ j, S j T ω) ∂P
      = ∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    have hexp : (fun ω => (∑ j, S j T ω) * (∑ j, S j T ω))
        = fun ω => ∑ j, ∑ k, S j T ω * S k T ω := by
      funext ω
      exact Finset.sum_mul_sum _ _ _ _
    have hint : ∀ j k, Integrable (fun ω => S j T ω * S k T ω) P := fun j k =>
      (hS2 j T).integrable_mul (hS2 k T)
    have hint' : ∀ j, Integrable (fun ω => ∑ k, S j T ω * S k T ω) P := fun j =>
      integrable_finsetSum _ fun k _ => hint j k
    rw [hexp, integral_finsetSum _ fun j _ => hint' j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hint j k,
      Finset.sum_eq_single j (fun k _ hkj => hSS j k (Ne.symm hkj))
        (fun hj => absurd (Finset.mem_univ j) hj)]
    exact hSiso j
  have hSsum_C : ∫ ω, (∑ j, S j T ω) * C T ω ∂P = 0 := by
    have hexp : (fun ω => (∑ j, S j T ω) * C T ω) = fun ω => ∑ j, S j T ω * C T ω := by
      funext ω
      exact Finset.sum_mul _ _ _
    have hint : ∀ j, Integrable (fun ω => S j T ω * C T ω) P := fun j =>
      (hS2 j T).integrable_mul (hC2 T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hSC j
  -- the martingale pieces are orthogonal to the initial value
  have hX₀S : ∀ j, ∫ ω, X₀ ω * S j T ω ∂P = 0 := fun j =>
    LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq_zero
      (_root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 (D.W.W j) ℱ
        (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j))
      hT.le (hX₀.mono (ℱ.le_rightCont 0)) hX₀2 (hS2 j T)
      (_root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 (D.W.W j) ℱ
        (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) le_rfl)
  have hX₀Ssum : ∫ ω, X₀ ω * (∑ j, S j T ω) ∂P = 0 := by
    have hexp : (fun ω => X₀ ω * (∑ j, S j T ω)) = fun ω => ∑ j, X₀ ω * S j T ω := by
      funext ω
      exact Finset.mul_sum _ _ _
    have hint : ∀ j, Integrable (fun ω => X₀ ω * S j T ω) P := fun j =>
      hX₀2.integrable_mul (hS2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hX₀S j
  have hCproc : ∀ t, C t =ᵐ[P]
      LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq t :=
    fun t => LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN γ
      h.γ_meas h.γ_prog h.γ_sq t
  have hproc2 : ∀ t, MemLp (LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq t) 2 P := fun t =>
    LevyStochCalc.Poisson.Compensated.process_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq t
  have hmartC := _root_.Prove2MeSourceProof.h_278d2487462db88d9db97988 D.N ℱ hℱN γ h.γ_meas
    h.γ_prog h.γ_sq
  have hproc0 := _root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 D.N ℱ hℱN γ
    h.γ_meas h.γ_prog h.γ_sq (le_refl (0 : ℝ))
  have hX₀C : ∫ ω, X₀ ω * C T ω ∂P = 0 := by
    have h1 : (fun ω => X₀ ω * C T ω) =ᵐ[P] fun ω => X₀ ω
        * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T ω := by
      filter_upwards [hCproc T] with ω hω
      rw [hω]
    rw [integral_congr_ae h1]
    exact LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq_zero hmartC hT.le hX₀ hX₀2 (hproc2 T) hproc0
  -- the drift pairings at the horizon, as time integrals
  have hDrS : ∀ j, ∫ ω, Dr T ω * S j T ω ∂P
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * S j T ω ∂P :=
    fun j => LevyStochCalc.Ito.SecondMoment.integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) (hS2 j T)
  have hDrC : ∫ ω, Dr T ω * C T ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * C T ω ∂P :=
    LevyStochCalc.Ito.SecondMoment.integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) (hC2 T)
  have hDrX₀ : ∫ ω, Dr T ω * X₀ ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * X₀ ω ∂P :=
    LevyStochCalc.Ito.SecondMoment.integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) hX₀2
  have hDrDr : ∫ ω, Dr T ω * Dr T ω ∂P
      = 2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Dr s ω ∂P := by
    have hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s => b s ω) (Set.Icc (0 : ℝ) T) volume := by
      filter_upwards [LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
        (f := fun ω s => b s ω) hbm hbq] with ω hω
      exact hω T
    have hR := _root_.Prove2MeSourceProof.h_20d586a8e09491862e290520 (P := P) hbm (hbq T hT)
    have hint : Integrable (fun p : Ω × ℝ => b p.2 p.1 * LevyStochCalc.Ito.SecondMoment.running b T p)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
      (LevyStochCalc.Ito.SecondMoment.memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul hR
    have hpath : ∀ᵐ ω ∂P, Dr T ω * Dr T ω
        = 2 * ∫ s in Set.Icc (0 : ℝ) T, b s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) := by
      filter_upwards [hbint] with ω hω
      simp only [hDrdef]
      rw [_root_.Prove2MeSourceProof.h_1b671b96dc934c6fb0df20bc hω]
      congr 1
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      rw [LevyStochCalc.Ito.SecondMoment.running_eq hs, mul_comm]
    calc ∫ ω, Dr T ω * Dr T ω ∂P
        = ∫ ω, (2 * ∫ s in Set.Icc (0 : ℝ) T, b s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s)) ∂P :=
          integral_congr_ae hpath
      _ = 2 * ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, b s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) ∂volume ∂P :=
          integral_const_mul _ _
      _ = 2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) ∂P := by
          rw [integral_integral_swap (f := fun ω s => b s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s)) hint]
      _ = 2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Dr s ω ∂P := by
          congr 1
          refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          exact congrArg (fun x => b s ω * x) (LevyStochCalc.Ito.SecondMoment.running_eq hs)
  -- at almost every time of the window, the pairing of the path with the drift expands
  have hbs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (fun ω => b s ω) 2 P :=
    LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b s ω) hbm (hbq T hT)
  have hsw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hXb : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫ ω, X s ω * b s ω ∂P
      = ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * Dr s ω ∂P
        + (∑ j, ∫ ω, b s ω * S j T ω ∂P) + ∫ ω, b s ω * C T ω ∂P := by
    filter_upwards [hbs, hsw] with s hs2 hs
    have hs0 : 0 ≤ s := hs.1
    have hbsm : StronglyMeasurable[ℱ.rightCont s] fun ω => b s ω :=
      (hbp.stronglyMeasurable_eval s).mono (ℱ.le_rightCont s)
    have hbsm' : StronglyMeasurable[ℱ s] fun ω => b s ω := hbp.stronglyMeasurable_eval s
    have h1 : ∫ ω, X s ω * b s ω ∂P
        = ∫ ω, (X₀ ω + Dr s ω + (∑ j, S j s ω) + C s ω) * b s ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hdec s hs0] with ω hω
      rw [hω]
    have hexp : (fun ω => (X₀ ω + Dr s ω + (∑ j, S j s ω) + C s ω) * b s ω)
        = fun ω => b s ω * X₀ ω + b s ω * Dr s ω + (∑ j, b s ω * S j s ω) + b s ω * C s ω := by
      funext ω
      rw [← Finset.mul_sum]
      ring
    have i1 : Integrable (fun ω => b s ω * X₀ ω) P := hs2.integrable_mul hX₀2
    have i2 : Integrable (fun ω => b s ω * Dr s ω) P := hs2.integrable_mul (hDr2 s hs0)
    have i3 : ∀ j, Integrable (fun ω => b s ω * S j s ω) P := fun j =>
      hs2.integrable_mul (hS2 j s)
    have i3' : Integrable (fun ω => ∑ j, b s ω * S j s ω) P :=
      integrable_finsetSum _ fun j _ => i3 j
    have i4 : Integrable (fun ω => b s ω * C s ω) P := hs2.integrable_mul (hC2 s)
    have i12 : Integrable (fun ω => b s ω * X₀ ω + b s ω * Dr s ω) P := i1.add i2
    have i123 : Integrable
        (fun ω => b s ω * X₀ ω + b s ω * Dr s ω + ∑ j, b s ω * S j s ω) P := i12.add i3'
    have hSj : ∀ j, ∫ ω, b s ω * S j s ω ∂P = ∫ ω, b s ω * S j T ω ∂P := fun j =>
      (LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq
        (_root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 (D.W.W j) ℱ
          (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j)) hs.2 hbsm hs2 (hS2 j T)).symm
    have hCs : ∫ ω, b s ω * C s ω ∂P = ∫ ω, b s ω * C T ω ∂P := by
      have e1 : (fun ω => b s ω * C s ω) =ᵐ[P] fun ω => b s ω
          * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq s ω := by
        filter_upwards [hCproc s] with ω hω
        rw [hω]
      have e2 : (fun ω => b s ω * C T ω) =ᵐ[P] fun ω => b s ω
          * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T ω := by
        filter_upwards [hCproc T] with ω hω
        rw [hω]
      rw [integral_congr_ae e1, integral_congr_ae e2]
      exact (LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq hmartC hs.2 hbsm' hs2 (hproc2 T)).symm
    rw [h1, hexp, integral_add i123 i4, integral_add i12 i3', integral_add i1 i2,
      integral_finsetSum _ fun j _ => i3 j, hCs]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun j _ => hSj j
  -- integrability in time of the pieces
  have hint_s : ∀ (g : Ω → ℝ), MemLp g 2 P →
      Integrable (fun s => ∫ ω, b s ω * g ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun g hg => ((LevyStochCalc.Ito.SecondMoment.memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
      (LevyStochCalc.Ito.SecondMoment.memLp_two_prod_fst hg)).integral_prod_right
  have hint_Dr : Integrable (fun s => ∫ ω, b s ω * Dr s ω ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have h1 : Integrable (fun s => ∫ ω, b s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      ((LevyStochCalc.Ito.SecondMoment.memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
        (_root_.Prove2MeSourceProof.h_20d586a8e09491862e290520 (P := P) hbm (hbq T hT))).integral_prod_right
    refine h1.congr ?_
    filter_upwards [hsw] with s hs
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact congrArg (fun x => b s ω * x) (LevyStochCalc.Ito.SecondMoment.running_eq hs)
  have hXs_int : ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b s ω ∂P
      = ∫ ω, Dr T ω * X₀ ω ∂P + (1 / 2) * ∫ ω, Dr T ω * Dr T ω ∂P
        + (∑ j, ∫ ω, Dr T ω * S j T ω ∂P) + ∫ ω, Dr T ω * C T ω ∂P := by
    have i1 := hint_s X₀ hX₀2
    have i3 : ∀ j, Integrable (fun s => ∫ ω, b s ω * S j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := fun j => hint_s _ (hS2 j T)
    have i3' : Integrable (fun s => ∑ j, ∫ ω, b s ω * S j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := integrable_finsetSum _ fun j _ => i3 j
    have i4 := hint_s _ (hC2 T)
    have i12 : Integrable (fun s => ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * Dr s ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := i1.add hint_Dr
    have i123 : Integrable (fun s => ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * Dr s ω ∂P
        + ∑ j, ∫ ω, b s ω * S j T ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) := i12.add i3'
    rw [integral_congr_ae hXb, integral_add i123 i4, integral_add i12 i3', integral_add i1 hint_Dr,
      integral_finsetSum _ fun j _ => i3 j, hDrX₀, hDrDr, hDrC,
      Finset.sum_congr rfl fun j _ => hDrS j]
    ring
  -- the pairing of the initial value with the drift, and the drift with the Brownian sum
  have hcomm : ∫ ω, X₀ ω * Dr T ω ∂P = ∫ ω, Dr T ω * X₀ ω ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have hDrSsum : ∫ ω, Dr T ω * (∑ j, S j T ω) ∂P = ∑ j, ∫ ω, Dr T ω * S j T ω ∂P := by
    have hexp : (fun ω => Dr T ω * (∑ j, S j T ω)) = fun ω => ∑ j, Dr T ω * S j T ω := by
      funext ω
      exact Finset.mul_sum _ _ _
    have hint : ∀ j, Integrable (fun ω => Dr T ω * S j T ω) P := fun j =>
      (hDr2 T hT.le).integrable_mul (hS2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
  -- expand the square of the decomposition at the horizon
  have hL : ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, (X₀ ω + Dr T ω + ((∑ j, S j T ω) + C T ω))
          * (X₀ ω + Dr T ω + ((∑ j, S j T ω) + C T ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hdec T hT.le] with ω hω
    rw [hω]
    ring
  have hf1 : MemLp (fun ω => X₀ ω + Dr T ω) 2 P := hX₀2.add (hDr2 T hT.le)
  have hg1 : MemLp (fun ω => (∑ j, S j T ω) + C T ω) 2 P := (hSsum2 T).add (hC2 T)
  rw [hL, LevyStochCalc.Ito.SecondMoment.integral_mul_self_add hf1 hg1, LevyStochCalc.Ito.SecondMoment.integral_mul_self_add hX₀2 (hDr2 T hT.le),
    LevyStochCalc.Ito.SecondMoment.integral_mul_self_add (hSsum2 T) (hC2 T),
    _root_.Prove2MeSourceProof.h_07b9943ba0f4880793c268df hX₀2 (hDr2 T hT.le) (hSsum2 T) (hC2 T),
    hSsum_sq, hCiso, hSsum_C, hX₀Ssum, hX₀C, hXs_int, hcomm, hDrSsum]
  ring
end Scalar

section Vector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

end Vector

section Augmented

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end Augmented

end LevyStochCalc.Ito.SecondMoment


