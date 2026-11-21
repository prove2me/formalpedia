-- Prove2me | Definitions.Def_SourceProof_8e283c77eae519d37a5460ab
-- name    : SourceProof_8e283c77eae519d37a5460ab
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:51:41.306723+00:00
-- url     : https://prove2.me/theorems/6995866c-f567-4edf-9211-4aa965892e77
-- title:
--   LevyStochCalc source module: SourceProof_8e283c77eae519d37a5460ab
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula` comes from the `LevyStochCalc.Brownian.VectorItoFormula` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_f8a966cc15e24894670072db

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a vector Itô process on a uniform grid

The grid decomposition leaves four errors: the second-order Taylor remainder, one drift Riemann
sum per state index, one martingale Riemann sum per state-and-Brownian index pair, and one
weighted quadratic variation per pair of state indices. Under an affine oscillation bound
`A + K‖z − w‖` on the second derivative each is bounded by a function of the mesh whose limit is
proportional to `A`; a uniformly continuous second derivative supplies such a bound for every
`A > 0`, so the `L¹` defect of Itô's formula vanishes.

## Main statements

* `LevyStochCalc.Brownian.Ito.vectorItoGridError` — the mesh-error function.
* `LevyStochCalc.Brownian.Ito.tendsto_vectorItoGridError` — it vanishes as the mesh does.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_vectorItoFormula_le` — the `L¹`
  defect of Itô's formula on every uniform grid.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula` — Itô's formula in the vector case.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

section Formula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_8e283c77eae519d37a5460ab
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    (hf''c : Continuous f'')
    (hf''unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖f'' z - f'' w‖ ≤ ε)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
  have haff : ∀ ε : ℝ, 0 < ε →
      ∃ Kε : ℝ, 0 ≤ Kε ∧ ∀ z w, ‖f'' z - f'' w‖ ≤ ε + Kε * ‖z - w‖ := by
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ := hf''unif ε hε
    refine ⟨2 * K₂ / δ, by positivity, fun z w => ?_⟩
    have hnn : (0 : ℝ) ≤ 2 * K₂ / δ * ‖z - w‖ := by positivity
    rcases lt_or_ge ‖z - w‖ δ with hlt | hge
    · have hle : ‖f'' z - f'' w‖ ≤ ε := hδ z w hlt
      linarith
    · have h1 : ‖f'' z - f'' w‖ ≤ 2 * K₂ := by
        refine (norm_sub_le (f'' z) (f'' w)).trans ?_
        linarith [hf''bd z, hf''bd w]
      have h2 : 2 * K₂ / δ * δ ≤ 2 * K₂ / δ * ‖z - w‖ :=
        mul_le_mul_of_nonneg_left hge (by positivity)
      rw [div_mul_cancel₀ _ (ne_of_gt hδ0)] at h2
      linarith
  obtain ⟨K₁ε, hK₁ε0, haff1⟩ := haff 1 one_pos
  obtain ⟨hZint, -⟩ := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_f8a966cc15e24894670072db p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hX₀ hbm hB0 hB hma hpa hqa
    hf hf' hf'bd hK₂0 hf''bd zero_le_one hK₁ε0 hf''c haff1 hmg hpg hqg hT one_ne_zero
  have hkey : ∀ ε : ℝ, 0 < ε →
      ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
        ≤ ε * LevyStochCalc.Brownian.Ito.vectorItoGridResidue (n : ℝ) (d : ℝ) C T := by
    intro ε hε
    obtain ⟨Kε, hKε0, haffε⟩ := haff ε hε
    have hgrid := fun (m : ℕ) (hm0 : m ≠ 0) =>
      (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_f8a966cc15e24894670072db p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hX₀ hbm hB0 hB hma hpa hqa hf hf' hf'bd
        hK₂0 hf''bd hε.le hKε0 hf''c haffε hmg hpg hqg hT hm0
    exact ge_of_tendsto (LevyStochCalc.Brownian.Ito.tendsto_vectorItoGridError (n : ℝ) (d : ℝ) B C T ε Kε K₂)
      ((Filter.eventually_gt_atTop 0).mono fun m hmpos => (hgrid m hmpos.ne').2)
  have htend : Filter.Tendsto
      (fun j : ℕ => (1 / ((j : ℝ) + 1)) * LevyStochCalc.Brownian.Ito.vectorItoGridResidue (n : ℝ) (d : ℝ) C T)
      Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.mul_const (LevyStochCalc.Brownian.Ito.vectorItoGridResidue (n : ℝ) (d : ℝ) C T)
  have hzero := ge_of_tendsto htend (Filter.Eventually.of_forall fun j : ℕ =>
    hkey (1 / ((j : ℝ) + 1)) (by positivity))
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg
    (fun ω => abs_nonneg _) hZint.abs).mp
    (le_antisymm hzero (MeasureTheory.integral_nonneg fun ω => abs_nonneg _))
  filter_upwards [hae] with ω hω
  have hz := abs_eq_zero.mp hω
  linarith
end Formula

end LevyStochCalc.Brownian.Ito


