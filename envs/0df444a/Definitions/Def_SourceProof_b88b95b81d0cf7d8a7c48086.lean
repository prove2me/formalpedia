-- Prove2me | Definitions.Def_SourceProof_b88b95b81d0cf7d8a7c48086
-- name    : SourceProof_b88b95b81d0cf7d8a7c48086
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:35:19.270474+00:00
-- url     : https://prove2.me/theorems/79cf1f1c-bf07-4ca2-905d-e6bfe221572e
-- title:
--   LevyStochCalc source module: SourceProof_b88b95b81d0cf7d8a7c48086
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le` comes from the `LevyStochCalc.Ito.VectorItoVersionSup` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_VectorItoVersionSup_F000
import Definitions.Def_SourceProof_190a5767e8f1b936b4a6a09f
import Definitions.Def_SourceProof_700488d66fa58fc241f21293
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8
import Definitions.Def_SourceProof_ea5efb46f0ff2335ed0cf2ed

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The window supremum of the difference of two vector Itô versions

Two versions driven by different coefficients differ by a drift part, controlled pathwise by
Cauchy–Schwarz, and a martingale part, controlled by Doob's `L²` maximal inequality. Sampling the
paths on the dyadic points of the window turns the supremum into a countable one, which is all the
maximal inequality needs.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le` — the second moment of the
  window supremum of the difference, in terms of the coefficients' energies.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Helpers

variable {Ω : Type u}

variable [MeasurableSpace Ω] {P : Measure Ω}

end Helpers

section SupBound

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

include hcoord in

theorem _root_.Prove2MeSourceProof.h_b88b95b81d0cf7d8a7c48086
    {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k))}
    {hp₁ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₁ p k)}
    {hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k))}
    {hp₂ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₂ p k)}
    {hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X Y : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ X)
    (hY : IsVectorItoVersion W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ Y)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
          (4 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) := by
  classical
  set Zc : Fin n → ℝ → Ω → ℝ := fun p t ω => Y t ω p - X t ω p with hZcdef
  set Zabs : ℝ → Ω → ℝ := fun t ω => ∑ p : Fin n, |Zc p t ω| with hZabsdef
  have hZcm : ∀ (p : Fin n) (t : ℝ), Measurable (Zc p t) :=
    fun p t => (hY.measurable_coord t p).sub (hX.measurable_coord t p)
  have hZccont : ∀ (p : Fin n) (ω : Ω), Continuous fun t => Zc p t ω := by
    intro p ω
    exact ((continuous_apply p).comp (hY.continuous_path ω)).sub
      ((continuous_apply p).comp (hX.continuous_path ω))
  have hZabscont : ∀ ω : Ω, Continuous fun t => Zabs t ω :=
    fun ω => continuous_finsetSum _ fun p _ => (hZccont p ω).abs
  set S : Fin n → Ω → ℝ≥0∞ := fun p ω => ⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax (Zc p) T m ω‖₊ : ℝ≥0∞)
    with hSdef
  have hSmeas : ∀ p : Fin n, Measurable (S p) :=
    fun p => Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hZcm p) T m
  -- the window supremum is dominated by the coordinatewise dyadic suprema
  have hdom : ∀ ω : Ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞))
      ≤ ∑ p : Fin n, S p ω := by
    intro ω
    have hcad : ∀ t : ℝ, Filter.Tendsto (fun s => Zabs s ω) (nhdsWithin t (Set.Ioi t))
        (nhds (Zabs t ω)) := fun t => ((hZabscont ω).tendsto t).mono_left nhdsWithin_le_nhds
    have hstep1 : (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞))
        ≤ ⨆ t : Set.Icc (0 : ℝ) T, (‖Zabs (t : ℝ) ω‖₊ : ℝ≥0∞) := by
      refine iSup_le fun t => le_iSup_of_le t ?_
      have hnn : (0 : ℝ) ≤ ∑ q : Fin n, |Y (t : ℝ) ω q - X (t : ℝ) ω q| :=
        Finset.sum_nonneg fun q _ => abs_nonneg _
      have hreal : ‖Y (t : ℝ) ω - X (t : ℝ) ω‖
          ≤ ∑ q : Fin n, |Y (t : ℝ) ω q - X (t : ℝ) ω q| := by
        refine (pi_norm_le_iff_of_nonneg hnn).mpr fun q => ?_
        have hq : |Y (t : ℝ) ω q - X (t : ℝ) ω q|
            ≤ ∑ r : Fin n, |Y (t : ℝ) ω r - X (t : ℝ) ω r| :=
          Finset.single_le_sum (f := fun r : Fin n => |Y (t : ℝ) ω r - X (t : ℝ) ω r|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
        simpa [Real.norm_eq_abs] using hq
      have hZ : ‖Zabs (t : ℝ) ω‖ = ∑ q : Fin n, |Y (t : ℝ) ω q - X (t : ℝ) ω q| := by
        simp only [hZabsdef, hZcdef]
        exact Real.norm_of_nonneg hnn
      have hle : ‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ ≤ ‖Zabs (t : ℝ) ω‖₊ := by
        rw [← NNReal.coe_le_coe]
        simpa only [coe_nnnorm, hZ] using hreal
      exact_mod_cast hle
    refine hstep1.trans ?_
    rw [_root_.Prove2MeSourceProof.h_755d31da2fec92eb2a10cfd6 hT.le hcad]
    refine le_trans (LevyStochCalc.Probability.iSup_dyadicRunMax_sum_le Finset.univ (fun p t ω => |Zc p t ω|) T ω) ?_
    exact le_of_eq (Finset.sum_congr rfl fun p _ => by
      simp only [hSdef, LevyStochCalc.Brownian.Ito.dyadicRunMax_abs])
  -- square, and split the integral over the coordinates
  have hsq : ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n, ∫⁻ ω, (S p ω) ^ 2 ∂P := by
    calc ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
        ≤ ∫⁻ ω, ((n : ℝ≥0∞) ^ 2 * ∑ p : Fin n, (S p ω) ^ 2) ∂P := by
          refine MeasureTheory.lintegral_mono fun ω => ?_
          refine le_trans (pow_le_pow_left' (hdom ω) 2) ?_
          simpa using _root_.Prove2MeSourceProof.h_d76df0724e08b30159a31ac0 (Finset.univ : Finset (Fin n)) fun p => S p ω
      _ = (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n, ∫⁻ ω, (S p ω) ^ 2 ∂P := by
          rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
            MeasureTheory.lintegral_finsetSum _ fun p _ => (hSmeas p).pow_const 2]
  refine hsq.trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun p _ => ?_))
  -- the drift and martingale parts of the coordinate difference
  set D : ℝ → Ω → ℝ := fun t ω => (∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
    - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume with hDdef
  set M : ℝ → Ω → ℝ := fun t ω => LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
    - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω with hMdef
  have hDm : ∀ t : ℝ, Measurable (D t) := fun t =>
    (LevyStochCalc.measurable_setIntegral (hbm₂ p) (Set.Icc (0 : ℝ) t)).sub
      (LevyStochCalc.measurable_setIntegral (hbm₁ p) (Set.Icc (0 : ℝ) t))
  have hMm : ∀ t : ℝ, Measurable (M t) := fun t =>
    (LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t).sub
      (LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t)
  have hsplit : ∀ᵐ ω ∂P, ∀ m k : ℕ,
      Zc p (LevyStochCalc.Probability.dyadicTime T m k) ω = D (LevyStochCalc.Probability.dyadicTime T m k) ω + M (LevyStochCalc.Probability.dyadicTime T m k) ω := by
    rw [MeasureTheory.ae_all_iff]
    intro m
    rw [MeasureTheory.ae_all_iff]
    intro k
    filter_upwards [hX.ae_eq (LevyStochCalc.Probability.dyadicTime T m k) (LevyStochCalc.Probability.dyadicTime_nonneg hT.le m k),
      hY.ae_eq (LevyStochCalc.Probability.dyadicTime T m k) (LevyStochCalc.Probability.dyadicTime_nonneg hT.le m k)] with ω e1 e2
    simp only [hZcdef, hDdef, hMdef, e1, e2, LevyStochCalc.Brownian.Ito.vectorItoProcess]
    ring
  have hSbound : ∀ᵐ ω ∂P, (S p ω) ^ 2
      ≤ 4 * ((⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2
        + (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2) := by
    filter_upwards [hsplit] with ω hω
    have hcongr : ∀ m : ℕ, LevyStochCalc.Probability.dyadicRunMax (Zc p) T m ω
        = LevyStochCalc.Probability.dyadicRunMax (fun t ω => D t ω + M t ω) T m ω :=
      fun m => LevyStochCalc.Brownian.Ito.dyadicRunMax_congr (fun m' k => hω m' k) m
    have hle : S p ω ≤ (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞))
        + ⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞) := by
      simp only [hSdef, hcongr]
      exact LevyStochCalc.Probability.iSup_dyadicRunMax_add_le D M T ω
    exact le_trans (pow_le_pow_left' hle 2) (LevyStochCalc.Brownian.Ito.add_sq_le_four_mul _ _)
  -- the drift part, by Cauchy–Schwarz on the window
  have hΔbfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖|b₂ p ω s - b₁ p ω s|‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    have hbd : ∀ (ω : Ω) (s : ℝ), (‖|b₂ p ω s - b₁ p ω s|‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 + (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2) := by
      intro ω s
      have := LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul (b₂ p ω s) (b₁ p ω s)
      simpa [nnnorm_abs_real] using this
    exact _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293 hbd (hbm₂ p) (hbm₁ p) (hbq₂ p) (hbq₁ p) T hT
  have hDrift : ∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    have hint₁ : ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (b₁ p ω) (Set.Icc (0 : ℝ) T) volume :=
      LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm₁ p) (hbq₁ p T hT)
    have hint₂ : ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (b₂ p ω) (Set.Icc (0 : ℝ) T) volume :=
      LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm₂ p) (hbq₂ p T hT)
    have hptw : ∀ᵐ ω ∂P, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞))
        ≤ (‖∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume‖₊ : ℝ≥0∞) := by
      filter_upwards [hint₁, hint₂] with ω h1 h2
      refine LevyStochCalc.Probability.iSup_dyadicRunMax_le_of_bound hT.le fun t ht => ?_
      have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
      have hDt : D t ω = ∫ s in Set.Icc (0 : ℝ) t, (b₂ p ω s - b₁ p ω s) ∂volume := by
        simp only [hDdef]
        rw [MeasureTheory.integral_sub (h2.mono_set hsub) (h1.mono_set hsub)]
      have habs : |D t ω| ≤ ∫ s in Set.Icc (0 : ℝ) t, |b₂ p ω s - b₁ p ω s| ∂volume := by
        rw [hDt]
        exact MeasureTheory.abs_integral_le_integral_abs
      have hmono : ∫ s in Set.Icc (0 : ℝ) t, |b₂ p ω s - b₁ p ω s| ∂volume
          ≤ ∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume :=
        MeasureTheory.setIntegral_mono_set (h2.sub h1).abs
          (Filter.Eventually.of_forall fun s => abs_nonneg _) hsub.eventuallyLE
      have hnn : ‖D t ω‖₊ ≤ ‖∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume‖₊ := by
        rw [← NNReal.coe_le_coe]
        simp only [coe_nnnorm, Real.norm_eq_abs]
        have hAnn : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume :=
          MeasureTheory.integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun s => abs_nonneg _)
        rw [abs_of_nonneg hAnn]
        exact habs.trans hmono
      exact_mod_cast hnn
    calc ∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
        ≤ ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) T,
            |b₂ p ω s - b₁ p ω s| ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P :=
          MeasureTheory.lintegral_mono_ae (hptw.mono fun ω h => pow_le_pow_left' h 2)
      _ ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖|b₂ p ω s - b₁ p ω s|‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
          _root_.Prove2MeSourceProof.h_190a5767e8f1b936b4a6a09f
            ((hbm₂ p).sub (hbm₁ p)).abs hT.le hΔbfin
      _ = ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
          simp
  -- the martingale part, by Doob's inequality
  have hMart : MeasureTheory.Martingale M ℱ P :=
    (LevyStochCalc.Brownian.Ito.martingale_vectorItoMartingale W ℱ hcoord hm₂ hp₂ hq₂ p).sub
      (LevyStochCalc.Brownian.Ito.martingale_vectorItoMartingale W ℱ hcoord hm₁ hp₁ hq₁ p)
  have hMT : ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    have hMTeq : ∀ ω : Ω, M T ω = ∑ k : Fin d,
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
            (hq₂ p k) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
            (hq₁ p k) T ω) := by
      intro ω
      simp only [hMdef, LevyStochCalc.Brownian.Ito.vectorItoMartingale, coordItoIntegral]
      rw [Finset.sum_sub_distrib]
    have hkm : ∀ k : Fin d, Measurable fun ω : Ω =>
        (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
            (hq₂ p k) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
            (hq₁ p k) T ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro k
      have h2 : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k)
          (hm₂ p k) (hp₂ p k) (hq₂ p k) T) :=
        ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H₂ p k)
          (hm₂ p k) (hp₂ p k) (hq₂ p k) T).mono (ℱ.le T)).measurable
      have h1 : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k)
          (hm₁ p k) (hp₁ p k) (hq₁ p k) T) :=
        ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H₁ p k)
          (hm₁ p k) (hp₁ p k) (hq₁ p k) T).mono (ℱ.le T)).measurable
      exact (((h2.sub h1).nnnorm).coe_nnreal_ennreal).pow_const 2
    calc ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, (d : ℝ≥0∞) * ∑ k : Fin d,
            (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
                (hq₂ p k) T ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
                (hq₁ p k) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
          refine MeasureTheory.lintegral_mono fun ω => ?_
          rw [hMTeq ω]
          exact _root_.Prove2MeSourceProof.h_ea5efb46f0ff2335ed0cf2ed _
      _ = (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω,
            (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
                (hq₂ p k) T ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
                (hq₁ p k) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
          rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
            MeasureTheory.lintegral_finsetSum _ fun k _ => hkm k]
      _ = (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
          refine congrArg (fun x => (d : ℝ≥0∞) * x) (Finset.sum_congr rfl fun k _ => ?_)
          exact _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 (W.W k) ℱ (hcoord k) (H₂ p k)
            (H₁ p k) (hm₂ p k) (hm₁ p k) (hp₂ p k) (hp₁ p k) (hq₂ p k) (hq₁ p k) hT
  have hDoob : ∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    LevyStochCalc.Probability.lintegral_iSup_dyadicRunMax_sq_le hMart hT.le
  calc ∫⁻ ω, (S p ω) ^ 2 ∂P
      ≤ ∫⁻ ω, 4 * ((⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2
          + (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        MeasureTheory.lintegral_mono_ae hSbound
    _ = 4 * (∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
          + ∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
          MeasureTheory.lintegral_add_left
            ((Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax hDm T m).pow_const 2)]
    _ ≤ 4 * (ENNReal.ofReal T * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) :=
        mul_le_mul' le_rfl (add_le_add hDrift (hDoob.trans (mul_le_mul' le_rfl hMT)))
    _ = 4 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
        rw [mul_add]
end SupBound

end LevyStochCalc.Brownian.Ito


