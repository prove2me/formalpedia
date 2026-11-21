-- Prove2me | Definitions.Def_SourceProof_ef93b78d487d6b1fdb99d88f
-- name    : SourceProof_ef93b78d487d6b1fdb99d88f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:01:22.147242+00:00
-- url     : https://prove2.me/theorems/c196e0cc-eab3-4ff0-8885-860f2d6a22cf
-- title:
--   LevyStochCalc source module: SourceProof_ef93b78d487d6b1fdb99d88f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded_coeff` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F000
import Definitions.Def_SourceProof_0ac980e224d4498dc611b565
import Definitions.Def_SourceProof_beebe463528d222d5e910101
import Definitions.Def_SourceProof_d535c014a12fb1a12728f5c9
import Definitions.Def_SourceProof_e1094767e30c62c80823a8ec
import Definitions.Def_SourceProof_f41a629fee8aa0c308c4bfeb

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula without a pointwise bound on the coefficients

Passing to the limit along the clamped approximation gives Itô's formula for a vector Itô process
whose diffusion matrix and drift carry no pointwise bound, first for a function with bounded first
and second derivatives and then, by localisation, for an arbitrary `C²` function.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded_coeff` — Itô's formula with unbounded
  coefficients, for a function with bounded first and second derivatives.
* `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded` — Itô's formula for a `C²` function of a
  vector Itô process, with no bound on either the coefficients or the derivatives.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Limits

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)

variable (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')


theorem _root_.Prove2MeSourceProof.h_ef93b78d487d6b1fdb99d88f
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
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    (hf'c : Continuous f') (hf''c : Continuous f'')
    (hf''unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖f'' z - f'' w‖ ≤ ε)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
  classical
  have hX₀' : ∀ p : Fin n, Measurable fun ω => X₀ ω p :=
    fun p => (hX₀ p).mono (ℱ'.le 0) le_rfl
  have hqT : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := fun p k => (hHs p k T hT).ne
  have hbqT : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := fun p => (hbq p T hT).ne
  obtain ⟨ns, hge, hns⟩ := LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_lt hHm hbm hqT hbqT
  -- the versions driven by the clamped coefficients
  have hex : ∀ j : ℕ, ∃ Z : ℝ → Ω → Fin n → ℝ,
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ' hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
        (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm j p k)
        (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp j p k)
        (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
        X₀ (LevyStochCalc.Brownian.Ito.clampDrift bdrift j) Z := fun j =>
    _root_.Prove2MeSourceProof.h_e135e60f4c0109b1a168208c W ℱ' hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
      (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm j p k)
      (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp j p k)
      (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
      (Nat.cast_nonneg j) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H j) hℱ0 hnull hX₀ (LevyStochCalc.Brownian.Ito.clampDrift bdrift j)
      (fun p => LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm j p)
      (fun p => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampDrift hbp j p)
      (Nat.cast_nonneg j) (LevyStochCalc.Brownian.Ito.abs_clampDrift_le bdrift j)
  choose Xj hXj using hex
  have hYm : ∀ i : ℕ, Measurable (Function.uncurry fun ω s => Xj (ns i) s ω) :=
    fun i => (hXj (ns i)).measurable_uncurry
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) :=
    _root_.Prove2MeSourceProof.h_e1094767e30c62c80823a8ec W ℱ' hcoord hX₀' hbm hbq h hXj hns
  -- the integrands along the clamped versions
  have hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s) :=
    fun i p k => ((hXj (ns i)).measurable_uncurry_comp
      (LevyStochCalc.continuous_coordDeriv hf'c p).measurable).mul (LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm (ns i) p k)
  have hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      fun ω s => LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s :=
    fun i p k => ((hXj (ns i)).progressivelyMeasurable_comp
      (LevyStochCalc.continuous_coordDeriv hf'c p)).mul (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp (ns i) p k)
  have hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
    intro i p k
    refine _root_.Prove2MeSourceProof.h_2abda5a9ee832ec6f2f4409e (M := K₁ * ((ns i : ℕ) : ℝ)) fun ω s => ?_
    rw [abs_mul]
    exact mul_le_mul (LevyStochCalc.abs_coordDeriv_le hf'bd p _) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H (ns i) p k ω s)
      (abs_nonneg _) hK₁0
  -- the polarised coefficients of the clamped model
  have hma : ∀ (i : ℕ) (p q : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s + LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s) :=
    fun i p q k => (LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm (ns i) p k).add
      (LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm (ns i) q k)
  have hpa : ∀ (i : ℕ) (p q : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      fun ω s => LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s + LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s :=
    fun i p q k => (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp (ns i) p k).add
      (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp (ns i) q k)
  have hqa : ∀ (i : ℕ) (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s + LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
    intro i p q k
    refine _root_.Prove2MeSourceProof.h_2abda5a9ee832ec6f2f4409e (M := 2 * ((ns i : ℕ) : ℝ)) fun ω s => ?_
    calc |LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s + LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s|
        ≤ |LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s| + |LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s| := abs_add_le _ _
      _ ≤ ((ns i : ℕ) : ℝ) + ((ns i : ℕ) : ℝ) :=
          add_le_add (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H (ns i) p k ω s) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H (ns i) q k ω s)
      _ = 2 * ((ns i : ℕ) : ℝ) := by ring
  -- Itô's formula for each clamped model
  have hform : ∀ i : ℕ,
      (fun ω : Ω => f (Xj (ns i) T ω) - f (Xj (ns i) 0 ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampDrift bdrift (ns i) p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s)
              (hmY i p k) (hpY i p k) (hqY i p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv₂ f'' p q (Xj (ns i) s ω)
                * ∑ k : Fin d, LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s
                    * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s ∂volume := fun i =>
    (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_8e283c77eae519d37a5460ab p2mMethodArg0 p2mMethodArg1 (hXj (ns i))) (Nat.cast_nonneg (ns i)) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H (ns i)) hX₀'
      (fun p => LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm (ns i) p) (Nat.cast_nonneg (ns i))
      (LevyStochCalc.Brownian.Ito.abs_clampDrift_le bdrift (ns i)) (hma i) (hpa i) (hqa i) hf hf' hf'bd hK₂0 hf''bd
      hf''c hf''unif (hmY i) (hpY i) (hqY i) hT
  obtain ⟨ms, hmsge, hSI⟩ := LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_clamp W ℱ' hcoord hf'c hK₁0 hf'bd
    hHm hT (fun p k => hHs p k T hT) hYm h.measurable_uncurry hge hae hmY hpY hqY hmg hpg hqg
  have hmsTop : Filter.Tendsto ms Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hmsge Filter.tendsto_id
  have hfc : Continuous f :=
    Differentiable.continuous fun z => (hf z).differentiableAt
  have hTlim : ∀ᵐ ω ∂P, Filter.Tendsto (fun i => Xj (ns i) T ω) Filter.atTop (𝓝 (X T ω)) :=
    _root_.Prove2MeSourceProof.h_f41a629fee8aa0c308c4bfeb W ℱ' hcoord hX₀' hbm hbq h hXj hns hT le_rfl
  have hzeroj : ∀ᵐ ω ∂P, ∀ j : ℕ, Xj j 0 ω = X₀ ω :=
    MeasureTheory.ae_all_iff.mpr fun j => _root_.Prove2MeSourceProof.h_0ac980e224d4498dc611b565 W ℱ' hcoord (hXj j)
  have hzeroX : X 0 =ᵐ[P] X₀ := _root_.Prove2MeSourceProof.h_0ac980e224d4498dc611b565 W ℱ' hcoord h
  have hdrift := _root_.Prove2MeSourceProof.h_d535c014a12fb1a12728f5c9 hf'c hf'bd hbm (fun p => hbq p T hT) hYm
    hge hae
  have hqv := _root_.Prove2MeSourceProof.h_beebe463528d222d5e910101 hf''c hK₂0 hf''bd hHm (fun p k => hHs p k T hT) hYm
    hge hae
  filter_upwards [MeasureTheory.ae_all_iff.mpr hform, hTlim, hzeroj, hzeroX, hdrift, hqv, hSI]
    with ω h1 h2 h3 h4 h5 h6 h7
  have hlhs : Filter.Tendsto
      (fun i : ℕ => f (Xj (ns (ms i)) T ω) - f (Xj (ns (ms i)) 0 ω)) Filter.atTop
      (𝓝 (f (X T ω) - f (X 0 ω))) := by
    have hzeroeq : ∀ i : ℕ, f (Xj (ns (ms i)) 0 ω) = f (X 0 ω) := by
      intro i
      rw [h3 (ns (ms i)), h4]
    have hTt : Filter.Tendsto (fun i : ℕ => f (Xj (ns (ms i)) T ω)) Filter.atTop
        (𝓝 (f (X T ω))) := (hfc.continuousAt.tendsto.comp h2).comp hmsTop
    have hconst : Filter.Tendsto (fun i : ℕ => f (Xj (ns (ms i)) 0 ω)) Filter.atTop
        (𝓝 (f (X 0 ω))) := by
      refine Filter.Tendsto.congr (fun i => (hzeroeq i).symm) ?_
      exact tendsto_const_nhds
    exact hTt.sub hconst
  have hrhs : Filter.Tendsto (fun i : ℕ =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv f' p (Xj (ns (ms i)) s ω) * LevyStochCalc.Brownian.Ito.clampDrift bdrift (ns (ms i)) p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => LevyStochCalc.coordDeriv f' p (Xj (ns (ms i)) s ω)
              * LevyStochCalc.Brownian.Ito.clampCoeff H (ns (ms i)) p k ω s)
            (hmY (ms i) p k) (hpY (ms i) p k) (hqY (ms i) p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (Xj (ns (ms i)) s ω)
              * ∑ k : Fin d, LevyStochCalc.Brownian.Ito.clampCoeff H (ns (ms i)) p k ω s
                  * LevyStochCalc.Brownian.Ito.clampCoeff H (ns (ms i)) q k ω s ∂volume) Filter.atTop
      (𝓝 ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) := by
    refine ((tendsto_finsetSum _ fun p _ => (h5 p).comp hmsTop).add
      (tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun k _ => h7 p k)).add ?_
    exact (tendsto_finsetSum _ fun p _ =>
      tendsto_finsetSum _ fun q _ => (h6 p q).comp hmsTop).const_mul _
  exact tendsto_nhds_unique (Filter.Tendsto.congr (fun i => h1 (ms i)) hlhs) hrhs
end Limits

end Clamped

end LevyStochCalc.Brownian.Ito


