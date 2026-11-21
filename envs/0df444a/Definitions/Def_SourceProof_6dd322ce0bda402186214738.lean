-- Prove2me | Definitions.Def_SourceProof_6dd322ce0bda402186214738
-- name    : SourceProof_6dd322ce0bda402186214738
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:51:32.875576+00:00
-- url     : https://prove2.me/theorems/5f8af53d-6f40-461e-acb5-21c1c1014ad5
-- title:
--   LevyStochCalc source module: SourceProof_6dd322ce0bda402186214738
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.integral_mul_eq_of_isItoLevyProcess` comes from the `LevyStochCalc.Ito.SecondMomentBilinear` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_SourceProof_07b9943ba0f4880793c268df
import Definitions.Def_SourceProof_20d586a8e09491862e290520
import Definitions.Def_SourceProof_39285c9e8cb91346b858af97
import Definitions.Def_SourceProof_52bc6f9c5c34d4f858067e35
import Definitions.Def_SourceProof_5875d84842d3e5613d1c768d
import Definitions.Def_SourceProof_b4f6afa5f19da9f228b3652e
import Definitions.Def_SourceProof_bddd1e967f1506b034b38002
import Definitions.Def_SourceProof_da55a4195e0b45ce7b0016e9
import Definitions.Def_SourceProof_ea708e0a6ffe599032f388e2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The bilinear second moment of two Itô–Lévy processes

For two Itô–Lévy processes `X` and `Y` over the same Lévy driver, with coefficients
`(X₀, b, σ, γ)` and `(Y₀, b', σ', γ')` satisfying the `L²` hypotheses, the expected product at a
time `T > 0` is

`𝔼[X_T Y_T] = 𝔼[X₀ Y₀] + ∫_0^T 𝔼[X_s b'_s + Y_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j σ'_j ds
  + 𝔼 ∫_0^T ∫_E γ γ' dν ds`,

the expectation form of the bilinear Itô formula, obtained from the polarised isometries of the
two stochastic integrals and the polarised drift identity. The drift term is the time integral of
the expected pairing; at every time the pairing is expanded along the decomposition, and the two
martingale pieces are read at the horizon by the martingale property.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Bilinear

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}


theorem _root_.Prove2MeSourceProof.h_6dd322ce0bda402186214738
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    {Y : ℝ → Ω → ℝ} {Y₀ : Ω → ℝ} {b' : ℝ → Ω → ℝ} {σ' : ℝ → Ω → Fin d → ℝ}
    {γ' : Ω → ℝ → E → ℝ}
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN Y Y₀ b' σ' γ')
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hY₀ : StronglyMeasurable[ℱ 0] Y₀) (hY₀2 : MemLp Y₀ 2 P)
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hb'p : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b' s ω)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, X T ω * Y T ω ∂P
      = ∫ ω, X₀ ω * Y₀ ω ∂P
        + (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b' s ω + Y s ω * b s ω ∂P)
        + (∑ j : Fin d, ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, σ s ω j * σ' s ω j ∂volume ∂P)
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, γ ω s e * γ' ω s e ∂ν ∂volume ∂P := by
  classical
  -- the pieces of the two decompositions
  set S : Fin d → ℝ → Ω → ℝ := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j)
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) with hSdef
  set S' : Fin d → ℝ → Ω → ℝ := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) (fun ω s => σ' s ω j)
      (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j) with hS'def
  set C : ℝ → Ω → ℝ :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq
    with hCdef
  set C' : ℝ → Ω → ℝ :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ' h'.γ_meas h'.γ_prog h'.γ_sq
    with hC'def
  set Dr : ℝ → Ω → ℝ := fun t ω => ∫ s in Set.Icc (0 : ℝ) t, b s ω with hDrdef
  set Dr' : ℝ → Ω → ℝ := fun t ω => ∫ s in Set.Icc (0 : ℝ) t, b' s ω with hDr'def
  have hdec : ∀ᵐ ω ∂P, X T ω = X₀ ω + Dr T ω + (∑ j, S j T ω) + C T ω :=
    h.decomposition T hT.le
  have hdec' : ∀ᵐ ω ∂P, Y T ω = Y₀ ω + Dr' T ω + (∑ j, S' j T ω) + C' T ω :=
    h'.decomposition T hT.le
  -- square integrability of every piece
  have hS2 : ∀ (j : Fin d) (t : ℝ), MemLp (S j t) 2 P := fun j t =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t
  have hS'2 : ∀ (j : Fin d) (t : ℝ), MemLp (S' j t) 2 P := fun j t =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j) t
  have hSsum2 : MemLp (fun ω => ∑ j, S j T ω) 2 P := memLp_finsetSum Finset.univ fun j _ => hS2 j T
  have hS'sum2 : MemLp (fun ω => ∑ j, S' j T ω) 2 P :=
    memLp_finsetSum Finset.univ fun j _ => hS'2 j T
  have hC2 : ∀ t, MemLp (C t) 2 P := fun t =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq t
  have hC'2 : ∀ t, MemLp (C' t) 2 P := fun t =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ' h'.γ_meas h'.γ_prog
      h'.γ_sq t
  have hDr2 : ∀ t, 0 ≤ t → MemLp (Dr t) 2 P := fun t ht =>
    LevyStochCalc.Ito.SecondMoment.memLp_two_setIntegral (f := fun ω s => b s ω) hbm ht
      (LevyStochCalc.Ito.SecondMoment.energy_lt_top_of_nonneg (f := fun ω s => b s ω) hbq ht)
  have hDr'2 : ∀ t, 0 ≤ t → MemLp (Dr' t) 2 P := fun t ht =>
    LevyStochCalc.Ito.SecondMoment.memLp_two_setIntegral (f := fun ω s => b' s ω) hb'm ht
      (LevyStochCalc.Ito.SecondMoment.energy_lt_top_of_nonneg (f := fun ω s => b' s ω) hb'q ht)
  -- the polarised isometries and the orthogonalities
  have hSjj : ∀ j, ∫ ω, S j T ω * S' j T ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, σ s ω j * σ' s ω j ∂volume ∂P := fun j =>
    _root_.Prove2MeSourceProof.h_ea708e0a6ffe599032f388e2 (D.W.W j) ℱ (hℱW j) (h.σ_meas j) (h.σ_prog j)
      (h.σ_sq j) (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j) hT
  have hCC' : ∫ ω, C T ω * C' T ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, γ ω s e * γ' ω s e ∂ν ∂volume ∂P :=
    _root_.Prove2MeSourceProof.h_bddd1e967f1506b034b38002 D.N ℱ hℱN h.γ_meas h.γ_prog h.γ_sq h'.γ_meas h'.γ_prog
      h'.γ_sq hT
  have hSS' : ∀ j k, j ≠ k → ∫ ω, S j T ω * S' k T ω ∂P = 0 := fun j k hjk =>
    _root_.Prove2MeSourceProof.h_52bc6f9c5c34d4f858067e35
      D.W hjk hℱW (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) (h'.σ_meas k) (h'.σ_prog k) (h'.σ_sq k)
      hT.le
  have hSC' : ∀ j, ∫ ω, S j T ω * C' T ω ∂P = 0 := fun j =>
    _root_.Prove2MeSourceProof.h_da55a4195e0b45ce7b0016e9 𝒲 hℱW hℱN
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) h'.γ_meas h'.γ_prog h'.γ_sq hT.le
  have hCS' : ∀ j, ∫ ω, C T ω * S' j T ω ∂P = 0 := by
    intro j
    rw [integral_congr_ae (Eventually.of_forall fun ω => mul_comm (C T ω) (S' j T ω))]
    exact _root_.Prove2MeSourceProof.h_da55a4195e0b45ce7b0016e9 𝒲
      hℱW hℱN (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j) h.γ_meas h.γ_prog h.γ_sq hT.le
  have hSsumS' : ∫ ω, (∑ j, S j T ω) * (∑ j, S' j T ω) ∂P
      = ∑ j : Fin d, ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, σ s ω j * σ' s ω j ∂volume ∂P := by
    have hexp : (fun ω => (∑ j, S j T ω) * (∑ j, S' j T ω))
        = fun ω => ∑ j, ∑ k, S j T ω * S' k T ω := by
      funext ω
      exact Finset.sum_mul_sum _ _ _ _
    have hint : ∀ j k, Integrable (fun ω => S j T ω * S' k T ω) P := fun j k =>
      (hS2 j T).integrable_mul (hS'2 k T)
    have hint' : ∀ j, Integrable (fun ω => ∑ k, S j T ω * S' k T ω) P := fun j =>
      integrable_finsetSum _ fun k _ => hint j k
    rw [hexp, integral_finsetSum _ fun j _ => hint' j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hint j k,
      Finset.sum_eq_single j (fun k _ hkj => hSS' j k (Ne.symm hkj))
        (fun hj => absurd (Finset.mem_univ j) hj)]
    exact hSjj j
  have hSsumC' : ∫ ω, (∑ j, S j T ω) * C' T ω ∂P = 0 := by
    have hexp : (fun ω => (∑ j, S j T ω) * C' T ω) = fun ω => ∑ j, S j T ω * C' T ω := by
      funext ω
      exact Finset.sum_mul _ _ _
    have hint : ∀ j, Integrable (fun ω => S j T ω * C' T ω) P := fun j =>
      (hS2 j T).integrable_mul (hC'2 T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hSC' j
  have hCS'sum : ∫ ω, C T ω * (∑ j, S' j T ω) ∂P = 0 := by
    have hexp : (fun ω => C T ω * (∑ j, S' j T ω)) = fun ω => ∑ j, C T ω * S' j T ω := by
      funext ω
      exact Finset.mul_sum _ _ _
    have hint : ∀ j, Integrable (fun ω => C T ω * S' j T ω) P := fun j =>
      (hC2 T).integrable_mul (hS'2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hCS' j
  -- the martingale pieces are orthogonal to the initial values
  have hX₀S' : ∀ j, ∫ ω, X₀ ω * S' j T ω ∂P = 0 := fun j =>
    LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq_zero
      (_root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 (D.W.W j) ℱ
        (hℱW j) _ (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j))
      hT.le (hX₀.mono (ℱ.le_rightCont 0)) hX₀2 (hS'2 j T)
      (_root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 (D.W.W j) ℱ
        (hℱW j) _ (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j) le_rfl)
  have hY₀S : ∀ j, ∫ ω, Y₀ ω * S j T ω ∂P = 0 := fun j =>
    LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq_zero
      (_root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 (D.W.W j) ℱ
        (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j))
      hT.le (hY₀.mono (ℱ.le_rightCont 0)) hY₀2 (hS2 j T)
      (_root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 (D.W.W j) ℱ
        (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) le_rfl)
  have hX₀S'sum : ∫ ω, X₀ ω * (∑ j, S' j T ω) ∂P = 0 := by
    have hexp : (fun ω => X₀ ω * (∑ j, S' j T ω)) = fun ω => ∑ j, X₀ ω * S' j T ω := by
      funext ω
      exact Finset.mul_sum _ _ _
    have hint : ∀ j, Integrable (fun ω => X₀ ω * S' j T ω) P := fun j =>
      hX₀2.integrable_mul (hS'2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hX₀S' j
  have hSsumY₀ : ∫ ω, (∑ j, S j T ω) * Y₀ ω ∂P = 0 := by
    have hexp : (fun ω => (∑ j, S j T ω) * Y₀ ω) = fun ω => ∑ j, Y₀ ω * S j T ω := by
      funext ω
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hint : ∀ j, Integrable (fun ω => Y₀ ω * S j T ω) P := fun j =>
      hY₀2.integrable_mul (hS2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hY₀S j
  have hproc : ∀ t, C t =ᵐ[P]
      LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq t := fun t =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq t
  have hproc' : ∀ t, C' t =ᵐ[P]
      LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ' h'.γ_meas h'.γ_prog h'.γ_sq t :=
    fun t => LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN γ'
      h'.γ_meas h'.γ_prog h'.γ_sq t
  have hX₀C' : ∫ ω, X₀ ω * C' T ω ∂P = 0 := by
    have e : (fun ω => X₀ ω * C' T ω) =ᵐ[P] fun ω => X₀ ω
        * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ' h'.γ_meas h'.γ_prog h'.γ_sq
          T ω := by
      filter_upwards [hproc' T] with ω hω
      rw [hω]
    rw [integral_congr_ae e]
    exact LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq_zero
      (_root_.Prove2MeSourceProof.h_278d2487462db88d9db97988 D.N ℱ hℱN γ' h'.γ_meas h'.γ_prog
        h'.γ_sq) hT.le hX₀ hX₀2
      (LevyStochCalc.Poisson.Compensated.process_memLp D.N ℱ hℱN γ' h'.γ_meas h'.γ_prog h'.γ_sq T)
      (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 D.N ℱ hℱN γ' h'.γ_meas
        h'.γ_prog h'.γ_sq (le_refl (0 : ℝ)))
  have hCY₀ : ∫ ω, C T ω * Y₀ ω ∂P = 0 := by
    have e : (fun ω => C T ω * Y₀ ω) =ᵐ[P] fun ω => Y₀ ω
        * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T ω := by
      filter_upwards [hproc T] with ω hω
      rw [hω, mul_comm]
    rw [integral_congr_ae e]
    exact LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq_zero
      (_root_.Prove2MeSourceProof.h_278d2487462db88d9db97988 D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq)
      hT.le hY₀ hY₀2
      (LevyStochCalc.Poisson.Compensated.process_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T)
      (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 D.N ℱ hℱN γ h.γ_meas h.γ_prog
        h.γ_sq (le_refl (0 : ℝ)))
  -- the drift pairings at the horizon, as time integrals
  have hDrS' : ∀ j, ∫ ω, Dr T ω * S' j T ω ∂P
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * S' j T ω ∂P :=
    fun j => LevyStochCalc.Ito.SecondMoment.integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) (hS'2 j T)
  have hDrS'sum : ∫ ω, Dr T ω * (∑ j, S' j T ω) ∂P
      = ∑ j, ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * S' j T ω ∂P := by
    have hexp : (fun ω => Dr T ω * (∑ j, S' j T ω)) = fun ω => ∑ j, Dr T ω * S' j T ω := by
      funext ω
      exact Finset.mul_sum _ _ _
    have hint : ∀ j, Integrable (fun ω => Dr T ω * S' j T ω) P := fun j =>
      (hDr2 T hT.le).integrable_mul (hS'2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_congr rfl fun j _ => hDrS' j
  have hDrC' : ∫ ω, Dr T ω * C' T ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * C' T ω ∂P :=
    LevyStochCalc.Ito.SecondMoment.integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) (hC'2 T)
  have hDrY₀ : ∫ ω, Dr T ω * Y₀ ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Y₀ ω ∂P :=
    LevyStochCalc.Ito.SecondMoment.integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) hY₀2
  have hDr'S : ∀ j, ∫ ω, Dr' T ω * S j T ω ∂P
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * S j T ω ∂P :=
    fun j => LevyStochCalc.Ito.SecondMoment.integral_setIntegral_mul (f := fun ω s => b' s ω) hb'm (hb'q T hT) (hS2 j T)
  have hSsumDr' : ∫ ω, (∑ j, S j T ω) * Dr' T ω ∂P
      = ∑ j, ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * S j T ω ∂P := by
    have hexp : (fun ω => (∑ j, S j T ω) * Dr' T ω) = fun ω => ∑ j, Dr' T ω * S j T ω := by
      funext ω
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hint : ∀ j, Integrable (fun ω => Dr' T ω * S j T ω) P := fun j =>
      (hDr'2 T hT.le).integrable_mul (hS2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_congr rfl fun j _ => hDr'S j
  have hCDr' : ∫ ω, C T ω * Dr' T ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * C T ω ∂P := by
    rw [integral_congr_ae (Eventually.of_forall fun ω => mul_comm (C T ω) (Dr' T ω))]
    exact LevyStochCalc.Ito.SecondMoment.integral_setIntegral_mul (f := fun ω s => b' s ω) hb'm (hb'q T hT) (hC2 T)
  have hX₀Dr' : ∫ ω, X₀ ω * Dr' T ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * X₀ ω ∂P := by
    rw [integral_congr_ae (Eventually.of_forall fun ω => mul_comm (X₀ ω) (Dr' T ω))]
    exact LevyStochCalc.Ito.SecondMoment.integral_setIntegral_mul (f := fun ω s => b' s ω) hb'm (hb'q T hT) hX₀2
  -- integrability in time of the pairings
  have hint_s : ∀ (g : Ω → ℝ), MemLp g 2 P →
      Integrable (fun s => ∫ ω, b s ω * g ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun g hg => ((LevyStochCalc.Ito.SecondMoment.memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
      (LevyStochCalc.Ito.SecondMoment.memLp_two_prod_fst hg)).integral_prod_right
  have hint_s' : ∀ (g : Ω → ℝ), MemLp g 2 P →
      Integrable (fun s => ∫ ω, b' s ω * g ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun g hg => ((LevyStochCalc.Ito.SecondMoment.memLp_two_prod (f := fun ω s => b' s ω) hb'm (hb'q T hT)).integrable_mul
      (LevyStochCalc.Ito.SecondMoment.memLp_two_prod_fst hg)).integral_prod_right
  have hsw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hR := _root_.Prove2MeSourceProof.h_20d586a8e09491862e290520 (P := P) hbm (hbq T hT)
  have hR' := _root_.Prove2MeSourceProof.h_20d586a8e09491862e290520 (P := P) hb'm (hb'q T hT)
  have hint1 : Integrable (fun p : Ω × ℝ => b' p.2 p.1 * LevyStochCalc.Ito.SecondMoment.running b T p)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (LevyStochCalc.Ito.SecondMoment.memLp_two_prod (f := fun ω s => b' s ω) hb'm (hb'q T hT)).integrable_mul hR
  have hint2 : Integrable (fun p : Ω × ℝ => b p.2 p.1 * LevyStochCalc.Ito.SecondMoment.running b' T p)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (LevyStochCalc.Ito.SecondMoment.memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul hR'
  have hint_Dr : Integrable (fun s => ∫ ω, b' s ω * Dr s ω ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine hint1.integral_prod_right.congr ?_
    filter_upwards [hsw] with s hs
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact congrArg (fun x => b' s ω * x) (LevyStochCalc.Ito.SecondMoment.running_eq hs)
  have hint_Dr' : Integrable (fun s => ∫ ω, b s ω * Dr' s ω ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine hint2.integral_prod_right.congr ?_
    filter_upwards [hsw] with s hs
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact congrArg (fun x => b s ω * x) (LevyStochCalc.Ito.SecondMoment.running_eq hs)
  -- the product of the two drift integrals, by the polarised pathwise identity and Fubini
  have hDrDr' : ∫ ω, Dr T ω * Dr' T ω ∂P
      = (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * Dr s ω ∂P)
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Dr' s ω ∂P := by
    have hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s => b s ω) (Set.Icc (0 : ℝ) T) volume := by
      filter_upwards [LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
        (f := fun ω s => b s ω) hbm hbq] with ω hω
      exact hω T
    have hb'int : ∀ᵐ ω ∂P, IntegrableOn (fun s => b' s ω) (Set.Icc (0 : ℝ) T) volume := by
      filter_upwards [LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
        (f := fun ω s => b' s ω) hb'm hb'q] with ω hω
      exact hω T
    have hpath : ∀ᵐ ω ∂P, Dr T ω * Dr' T ω
        = ∫ s in Set.Icc (0 : ℝ) T,
            (b' s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) + b s ω * LevyStochCalc.Ito.SecondMoment.running b' T (ω, s)) := by
      filter_upwards [hbint, hb'int] with ω hω hω'
      simp only [hDrdef, hDr'def]
      rw [_root_.Prove2MeSourceProof.h_5875d84842d3e5613d1c768d hω hω']
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      rw [LevyStochCalc.Ito.SecondMoment.running_eq hs, LevyStochCalc.Ito.SecondMoment.running_eq hs]
      ring
    have hbs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (fun ω => b s ω) 2 P :=
      LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b s ω) hbm (hbq T hT)
    have hb's : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (fun ω => b' s ω) 2 P :=
      LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b' s ω) hb'm (hb'q T hT)
    calc ∫ ω, Dr T ω * Dr' T ω ∂P
        = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T,
            (b' s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) + b s ω * LevyStochCalc.Ito.SecondMoment.running b' T (ω, s)) ∂volume ∂P :=
          integral_congr_ae hpath
      _ = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω,
            (b' s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) + b s ω * LevyStochCalc.Ito.SecondMoment.running b' T (ω, s)) ∂P := by
          rw [integral_integral_swap
            (f := fun ω s => b' s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) + b s ω * LevyStochCalc.Ito.SecondMoment.running b' T (ω, s))
            (hint1.add hint2)]
      _ = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, (b' s ω * Dr s ω + b s ω * Dr' s ω) ∂P := by
          refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          change b' s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) + b s ω * LevyStochCalc.Ito.SecondMoment.running b' T (ω, s)
            = b' s ω * Dr s ω + b s ω * Dr' s ω
          rw [LevyStochCalc.Ito.SecondMoment.running_eq hs, LevyStochCalc.Ito.SecondMoment.running_eq hs]
      _ = (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * Dr s ω ∂P)
            + ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Dr' s ω ∂P := by
          rw [← integral_add hint_Dr hint_Dr']
          refine integral_congr_ae ?_
          filter_upwards [hbs, hb's, hsw] with s hs2 hs2' hs
          exact integral_add (hs2'.integrable_mul (hDr2 s hs.1)) (hs2.integrable_mul (hDr'2 s hs.1))
  -- at almost every time of the window, the two pairings of the paths with the drifts expand
  have hXb' : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫ ω, X s ω * b' s ω ∂P
      = ∫ ω, b' s ω * X₀ ω ∂P + ∫ ω, b' s ω * Dr s ω ∂P
        + (∑ j, ∫ ω, b' s ω * S j T ω ∂P) + ∫ ω, b' s ω * C T ω ∂P := by
    filter_upwards [LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b' s ω) hb'm (hb'q T hT), hsw] with s hs2 hs
    exact _root_.Prove2MeSourceProof.h_b4f6afa5f19da9f228b3652e h hX₀2 hbm hbq hs.1 hs.2 (hb'p.stronglyMeasurable_eval s) hs2
  have hYb : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫ ω, Y s ω * b s ω ∂P
      = ∫ ω, b s ω * Y₀ ω ∂P + ∫ ω, b s ω * Dr' s ω ∂P
        + (∑ j, ∫ ω, b s ω * S' j T ω ∂P) + ∫ ω, b s ω * C' T ω ∂P := by
    filter_upwards [LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b s ω) hbm (hbq T hT), hsw] with s hs2 hs
    exact _root_.Prove2MeSourceProof.h_b4f6afa5f19da9f228b3652e h' hY₀2 hb'm hb'q hs.1 hs.2 (hbp.stronglyMeasurable_eval s) hs2
  have hXY : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫ ω, X s ω * b' s ω + Y s ω * b s ω ∂P
        = ∫ ω, X s ω * b' s ω ∂P + ∫ ω, Y s ω * b s ω ∂P := by
    filter_upwards [LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b s ω) hbm (hbq T hT),
      LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b' s ω) hb'm (hb'q T hT), hsw] with s hs2 hs2' hs
    exact integral_add ((_root_.Prove2MeSourceProof.h_0122a571e95691a0e466a41c h hX₀2 hbm hbq hs.1).integrable_mul hs2')
      ((_root_.Prove2MeSourceProof.h_0122a571e95691a0e466a41c h' hY₀2 hb'm hb'q hs.1).integrable_mul hs2)
  have hdrift : ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b' s ω + Y s ω * b s ω ∂P
      = (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * X₀ ω ∂P)
        + (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * Dr s ω ∂P)
        + (∑ j, ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * S j T ω ∂P)
        + (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b' s ω * C T ω ∂P)
        + ((∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Y₀ ω ∂P)
        + (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Dr' s ω ∂P)
        + (∑ j, ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * S' j T ω ∂P)
        + (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * C' T ω ∂P)) := by
    have j1 := hint_s' X₀ hX₀2
    have j3 : ∀ j, Integrable (fun s => ∫ ω, b' s ω * S j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := fun j => hint_s' _ (hS2 j T)
    have j3' : Integrable (fun s => ∑ j, ∫ ω, b' s ω * S j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := integrable_finsetSum _ fun j _ => j3 j
    have j4 := hint_s' _ (hC2 T)
    have j12 : Integrable (fun s => ∫ ω, b' s ω * X₀ ω ∂P + ∫ ω, b' s ω * Dr s ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := j1.add hint_Dr
    have j123 : Integrable (fun s => ∫ ω, b' s ω * X₀ ω ∂P + ∫ ω, b' s ω * Dr s ω ∂P
        + ∑ j, ∫ ω, b' s ω * S j T ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) := j12.add j3'
    have j1234 : Integrable (fun s => ∫ ω, b' s ω * X₀ ω ∂P + ∫ ω, b' s ω * Dr s ω ∂P
        + ∑ j, ∫ ω, b' s ω * S j T ω ∂P + ∫ ω, b' s ω * C T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := j123.add j4
    have k1 := hint_s Y₀ hY₀2
    have k3 : ∀ j, Integrable (fun s => ∫ ω, b s ω * S' j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := fun j => hint_s _ (hS'2 j T)
    have k3' : Integrable (fun s => ∑ j, ∫ ω, b s ω * S' j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := integrable_finsetSum _ fun j _ => k3 j
    have k4 := hint_s _ (hC'2 T)
    have k12 : Integrable (fun s => ∫ ω, b s ω * Y₀ ω ∂P + ∫ ω, b s ω * Dr' s ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := k1.add hint_Dr'
    have k123 : Integrable (fun s => ∫ ω, b s ω * Y₀ ω ∂P + ∫ ω, b s ω * Dr' s ω ∂P
        + ∑ j, ∫ ω, b s ω * S' j T ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) := k12.add k3'
    have k1234 : Integrable (fun s => ∫ ω, b s ω * Y₀ ω ∂P + ∫ ω, b s ω * Dr' s ω ∂P
        + ∑ j, ∫ ω, b s ω * S' j T ω ∂P + ∫ ω, b s ω * C' T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := k123.add k4
    have hsum : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        ∫ ω, X s ω * b' s ω + Y s ω * b s ω ∂P
          = (∫ ω, b' s ω * X₀ ω ∂P + ∫ ω, b' s ω * Dr s ω ∂P
            + (∑ j, ∫ ω, b' s ω * S j T ω ∂P) + ∫ ω, b' s ω * C T ω ∂P)
          + (∫ ω, b s ω * Y₀ ω ∂P + ∫ ω, b s ω * Dr' s ω ∂P
            + (∑ j, ∫ ω, b s ω * S' j T ω ∂P) + ∫ ω, b s ω * C' T ω ∂P) := by
      filter_upwards [hXY, hXb', hYb] with s e0 e1 e2
      rw [e0, e1, e2]
    rw [integral_congr_ae hsum, integral_add j1234 k1234, integral_add j123 j4,
      integral_add j12 j3', integral_add j1 hint_Dr, integral_finsetSum _ fun j _ => j3 j,
      integral_add k123 k4, integral_add k12 k3', integral_add k1 hint_Dr',
      integral_finsetSum _ fun j _ => k3 j]
  -- the expansion of the product of the two decompositions at the horizon
  have hL : ∫ ω, X T ω * Y T ω ∂P
      = ∫ ω, (X₀ ω + Dr T ω + ((∑ j, S j T ω) + C T ω))
          * (Y₀ ω + Dr' T ω + ((∑ j, S' j T ω) + C' T ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hdec, hdec'] with ω hω hω'
    rw [hω, hω']
    ring
  have hf1 : MemLp (fun ω => X₀ ω + Dr T ω) 2 P := hX₀2.add (hDr2 T hT.le)
  have hg1 : MemLp (fun ω => (∑ j, S j T ω) + C T ω) 2 P := hSsum2.add (hC2 T)
  have hf2 : MemLp (fun ω => Y₀ ω + Dr' T ω) 2 P := hY₀2.add (hDr'2 T hT.le)
  have hg2 : MemLp (fun ω => (∑ j, S' j T ω) + C' T ω) 2 P := hS'sum2.add (hC'2 T)
  rw [hL, _root_.Prove2MeSourceProof.h_07b9943ba0f4880793c268df hf1 hg1 hf2 hg2,
    _root_.Prove2MeSourceProof.h_07b9943ba0f4880793c268df hX₀2 (hDr2 T hT.le) hY₀2 (hDr'2 T hT.le),
    _root_.Prove2MeSourceProof.h_07b9943ba0f4880793c268df hX₀2 (hDr2 T hT.le) hS'sum2 (hC'2 T),
    _root_.Prove2MeSourceProof.h_07b9943ba0f4880793c268df hSsum2 (hC2 T) hY₀2 (hDr'2 T hT.le),
    _root_.Prove2MeSourceProof.h_07b9943ba0f4880793c268df hSsum2 (hC2 T) hS'sum2 (hC'2 T),
    hSsumS', hSsumC', hCS'sum, hCC', hX₀S'sum, hX₀C', hSsumY₀, hCY₀, hDrS'sum, hDrC', hDrY₀,
    hSsumDr', hCDr', hX₀Dr', hDrDr', hdrift]
  ring
end Bilinear

end LevyStochCalc.Ito.SecondMoment


