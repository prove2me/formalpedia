-- Prove2me | Definitions.Def_SourceProof_47110770aca16d7a3084f758
-- name    : SourceProof_47110770aca16d7a3084f758
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:44:06.224768+00:00
-- url     : https://prove2.me/theorems/0e040808-df5a-4398-bead-e2e193fb61f1
-- title:
--   LevyStochCalc source module: SourceProof_47110770aca16d7a3084f758
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le` comes from the `LevyStochCalc.Brownian.ItoFormulaScalar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F001
import Definitions.Def_SourceProof_136e4408263cc1188bc69017
import Definitions.Def_SourceProof_3f24f0fb576e2ea9f8ba092b
import Definitions.Def_SourceProof_68d2be4bfe56156e1f930f2e
import Definitions.Def_SourceProof_724ac40b8d5293986a0749a0
import Definitions.Def_SourceProof_84dc228d7203d8f3c18ebbd6
import Definitions.Def_SourceProof_a028c987115bc886420ad387

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a scalar Itô process

For a continuous adapted version `X` of `X₀ + ∫ b ds + ∫ H dW` with bounded coefficients and
`f` twice differentiable with bounded derivatives and a Lipschitz second derivative,

  `f(X_T) − f(X_0) = ∫_0^T f'(X_s) b_s ds + ∫_0^T f'(X_s) H_s dW_s
      + ½ ∫_0^T f''(X_s) H_s² ds`

almost surely. The proof telescopes the second-order Taylor expansion over a uniform grid and
bounds the four resulting errors, all of which vanish as the mesh does.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoGridError` — the `L¹` error of the grid approximation, as a
  function of the mesh.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le` — that error bounds the
  `L¹` defect of Itô's formula on every uniform grid.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.itoFormula` — Itô's formula.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Formula

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_47110770aca16d7a3084f758
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hX₀ : Measurable X₀) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {K₁ K₂ : ℝ} (hf'bd : ∀ x, |f' x| ≤ K₁) (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ x, |f'' x| ≤ K₂)
    {K : ℝ} (hK0 : 0 ≤ K) (hf''lip : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|)
    (hmg : Measurable (Function.uncurry fun ω s => f' (X s ω) * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => f' (X s ω) * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖f' (X s ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
          + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)) P
      ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
            + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s)
                hmg hpg hqg T ω
            + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P
        ≤ itoGridError B C T K K₂ (T / (m : ℝ)) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hf'd : Differentiable ℝ f' := fun x => (hf' x).differentiableAt
  have hf'c : Continuous f' := hf'd.continuous
  have hf''c : Continuous f'' := by
    have hlip : LipschitzWith (Real.toNNReal K) f'' := by
      refine LipschitzWith.of_dist_le_mul fun u v => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK0]
      exact hf''lip u v
    exact hlip.continuous
  have hf'lip : ∀ u v : ℝ, |f' u - f' v| ≤ K₂ * |u - v| :=
    LevyStochCalc.Brownian.Ito.abs_sub_le_of_hasDerivAt_bound hf' hf''bd
  -- the four error terms
  obtain ⟨hZ1int, hZ1le⟩ := _root_.Prove2MeSourceProof.h_a028c987115bc886420ad387 W ℱ hℱ H hm hp hq hC0 hCH hX₀
    bdrift hbm hB0 hB hK0 hf hf' hf''lip hT hm0
  obtain ⟨hZ2int, hZ2le⟩ := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_68d2be4bfe56156e1f930f2e p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB
    bdrift hbm hB0 hB hf'c hf'bd hK₂0 hf'lip hT hm0
  have hZ3sq := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_136e4408263cc1188bc69017 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB hf'bd hK₂0 hf'lip
    hmg hpg hqg hT hm0
  obtain ⟨hZ4int, hZ4le⟩ := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_3f24f0fb576e2ea9f8ba092b p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB
    hf''c hK₂0 hf''bd hK0 hf''lip hT hm0
  -- the martingale term in `L¹`
  have hZ3meas : Measurable fun ω : Ω => (∑ i : Fin m, f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m ((i : ℕ) + 1)) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω))
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω := by
    refine Measurable.sub (Finset.measurable_sum _ fun i _ =>
      (hf'c.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)))).mul
        (LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq _ _)) ?_
    exact ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ
      (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T).mono (ℱ.le T)).measurable
  have hV0 : (0 : ℝ) ≤ C ^ 2 * (K₂ ^ 2 * (T * (2 * (B * (T / (m : ℝ))) ^ 2
      + 2 * (C ^ 2 * (T / (m : ℝ)))))) := by
    have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
    have hT0 : (0 : ℝ) ≤ T := hT.le
    positivity
  obtain ⟨hZ3int, hZ3le⟩ := _root_.Prove2MeSourceProof.h_84dc228d7203d8f3c18ebbd6
    hZ3meas.aestronglyMeasurable hV0 (by
      refine hZ3sq.trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)])
  -- the increments split
  have hsub : ∀ᵐ ω ∂P, ∀ i : ℕ,
      X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω
        = (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
          + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) :=
    MeasureTheory.ae_all_iff.mpr fun i => h.sub_ae hbm hB (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i)
      (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
  have hgrid : ∀ᵐ ω ∂P, ∀ i : ℕ, X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω
      = LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω :=
    h.ae_eq_all (LevyStochCalc.Brownian.Ito.unifGrid T m) fun i => LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i
  -- the Taylor remainder transferred to the version
  have hRae : (fun ω : Ω => LevyStochCalc.taylorRemainder f f' f''
        (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m)
      =ᵐ[P] fun ω => LevyStochCalc.taylorRemainder f f' f''
        (fun i => LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m := by
    filter_upwards [hgrid] with ω hω
    have hfun : (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        = fun i => LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω := funext hω
    rw [hfun]
  have hZ1int' : MeasureTheory.Integrable (fun ω : Ω =>
      LevyStochCalc.taylorRemainder f f' f'' (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m) P := hZ1int.congr hRae.symm
  have hZ1le' : ∫ ω, |LevyStochCalc.taylorRemainder f f' f'' (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m| ∂P
      ≤ K * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ))))) :=
    le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hRae.fun_comp abs))) hZ1le
  -- the halved quadratic-variation term
  have hZ4le' : ∫ ω, |1 / 2 * ((∑ i ∈ Finset.range m, f'' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2)
        - ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P
      ≤ 1 / 2 * ((m : ℝ) * (K₂ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (2 * K₂ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ))))
        + Real.sqrt (K₂ ^ 2 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4)
            * ((m : ℝ) * (T / (m : ℝ)) ^ 2))
        + K * C ^ 2 * (T * (B * (T / (m : ℝ)) + C * Real.sqrt (T / (m : ℝ))))) := by
    have habs : ∀ ω : Ω, |1 / 2 * ((∑ i ∈ Finset.range m, f'' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2)
          - ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)|
        = 1 / 2 * |(∑ i ∈ Finset.range m, f'' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2)
          - ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume| := by
      intro ω
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp_rw [habs]
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hZ4le (by norm_num)
  -- the grid decomposition
  have hdecomp : (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
          + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume))
      =ᵐ[P] fun ω => LevyStochCalc.taylorRemainder f f' f'' (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m
        + ((∑ i ∈ Finset.range m, f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + ((∑ i : Fin m, f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω)
              * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                  (LevyStochCalc.Brownian.Ito.unifGrid T m ((i : ℕ) + 1)) ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω))
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s)
                hmg hpg hqg T ω)
        + 1 / 2 * ((∑ i ∈ Finset.range m, f'' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2)
            - ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume) := by
    filter_upwards [hsub] with ω hω
    have hfin : (∑ i : Fin m, f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω)
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m ((i : ℕ) + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω))
        = ∑ i ∈ Finset.range m, f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) :=
      Fin.sum_univ_eq_sum_range (fun i => f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)) m
    rw [hfin]
    simp only [LevyStochCalc.taylorRemainder, LevyStochCalc.Brownian.Ito.unifGrid_self hm0, LevyStochCalc.Brownian.Ito.unifGrid_zero]
    have hsplit : ∑ i ∈ Finset.range m, f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        = (∑ i ∈ Finset.range m, f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift ω s ∂volume)
          + ∑ i ∈ Finset.range m, f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hω i]
      ring
    have hhalf : ∑ i ∈ Finset.range m, f'' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2 / 2
        = 1 / 2 * ∑ i ∈ Finset.range m, f'' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hhalf]
    ring
  refine ⟨(((hZ1int'.add hZ2int).add hZ3int).add (hZ4int.const_mul (1 / 2))).congr
      hdecomp.symm, ?_⟩
  refine le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hdecomp.fun_comp abs))) ?_
  -- the mesh identities
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have e1 : (m : ℝ) * (B * (T / (m : ℝ))) ^ 3 = B ^ 3 * T * (T / (m : ℝ)) ^ 2 := by
    field_simp
  have e2 : (m : ℝ) * (K₂ * (B * (T / (m : ℝ))) ^ 2)
      = K₂ * (B ^ 2 * T * (T / (m : ℝ))) := by
    field_simp
  have e3 : (m : ℝ) * (2 * K₂ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ))))
      = 2 * K₂ * B * C * T * Real.sqrt (T / (m : ℝ)) := by
    field_simp
  have e4 : (m : ℝ) * (T / (m : ℝ)) ^ 2 = T * (T / (m : ℝ)) := by
    field_simp
  rw [e1] at hZ1le'
  rw [e2, e3, e4] at hZ4le'
  unfold LevyStochCalc.Brownian.Ito.itoGridError
  exact _root_.Prove2MeSourceProof.h_724ac40b8d5293986a0749a0 hZ1int' hZ2int hZ3int (hZ4int.const_mul (1 / 2))
    hZ1le' hZ2le hZ3le hZ4le'
end Formula

end LevyStochCalc.Brownian.Ito


