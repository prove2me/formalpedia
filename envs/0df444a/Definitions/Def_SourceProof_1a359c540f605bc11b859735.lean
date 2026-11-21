-- Prove2me | Definitions.Def_SourceProof_1a359c540f605bc11b859735
-- name    : SourceProof_1a359c540f605bc11b859735
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:17:30.112738+00:00
-- url     : https://prove2.me/theorems/17fae14d-da67-4eeb-825e-c84a0199bd28
-- title:
--   LevyStochCalc source module: SourceProof_1a359c540f605bc11b859735
-- statement:
--   The original source theorem `LevyStochCalc.Ito.ae_eq_of_martingale_of_lintegral_sq_eq` comes from the `LevyStochCalc.BSDEJ.IntegralLocality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F001
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F002
import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Locality of the canonical stochastic integrals after a horizon

An integrand vanishing after a positive time `c` has an Itô integral that no longer moves after
`c`: the increment of the integral is a martingale increment whose second moment is the energy
carried by `(c, t]`, which is zero. This is the Brownian counterpart of
`LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_of_vanishing_gt`, together with the
multidimensional version and reformulations for integrands vanishing off a horizon `[0, T]`, the
shape carried by the fields of `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ`.

## Main statements

* `LevyStochCalc.Ito.ae_eq_of_martingale_of_lintegral_sq_eq` — two times of an `L²` martingale
  with the same second moment carry the same value almost surely.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq_of_vanishing_gt`
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_eq_of_vanishing_gt`
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq_of_vanish`,
  `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_eq_of_vanish`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_of_vanish` — the same statements
  for an integrand vanishing off `[0, T]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

namespace LevyStochCalc.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_1a359c540f605bc11b859735 {M : ℝ → Ω → ℝ} {c t : ℝ} (hct : c ≤ t)
    (hmart : Martingale M ℱ P) (hMt : MemLp (M t) 2 P) (hMc : MemLp (M c) 2 P)
    (hsame : ∫⁻ ω, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ∫⁻ ω, (‖M c ω‖₊ : ℝ≥0∞) ^ 2 ∂P) :
    M t =ᵐ[P] M c := by
  have hMtInt : Integrable (M t) P := hMt.integrable one_le_two
  have hct_int : Integrable (fun ω => M c ω * M t ω) P := hMc.integrable_mul hMt
  have hcc_int : Integrable (fun ω => M c ω * M c ω) P := hMc.integrable_mul hMc
  have htt_int : Integrable (fun ω => M t ω * M t ω) P := hMt.integrable_mul hMt
  -- the second moment is the `toReal` of the second `lintegral`
  have hsq : ∀ {r : ℝ}, MemLp (M r) 2 P →
      ∫ ω, M r ω * M r ω ∂P = (∫⁻ ω, (‖M r ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := by
    intro r hr
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => mul_self_nonneg _)
      (hr.aestronglyMeasurable.mul hr.aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← sq, show ((‖M r ω‖₊ : ℝ≥0∞)) = ‖M r ω‖ₑ from rfl, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  -- the cross moment is the second moment at the earlier time
  have hcross : ∫ ω, M c ω * M t ω ∂P = ∫ ω, M c ω * M c ω ∂P := by
    have hce : P[(fun ω => M c ω * M t ω) | ℱ c]
        =ᵐ[P] fun ω => M c ω * (P[M t | ℱ c]) ω :=
      condExp_mul_of_stronglyMeasurable_left (hmart.stronglyMeasurable c) hct_int hMtInt
    have hmc : P[M t | ℱ c] =ᵐ[P] M c := hmart.condExp_ae_eq hct
    rw [← integral_condExp (ℱ.le c)]
    refine integral_congr_ae (hce.trans ?_)
    filter_upwards [hmc] with ω hω
    rw [hω]
  have hsame' : ∫ ω, M t ω * M t ω ∂P = ∫ ω, M c ω * M c ω ∂P := by
    rw [hsq hMt, hsq hMc, hsame]
  -- hence the increment has zero second moment
  have hzero : ∫ ω, (M t ω - M c ω) * (M t ω - M c ω) ∂P = 0 := by
    have hexp : (fun ω => (M t ω - M c ω) * (M t ω - M c ω))
        = fun ω => M t ω * M t ω - (2 : ℝ) * (M c ω * M t ω) + M c ω * M c ω := by
      funext ω; ring
    have h1 : Integrable (fun ω => M t ω * M t ω - (2 : ℝ) * (M c ω * M t ω)) P :=
      htt_int.sub (hct_int.const_mul 2)
    rw [hexp, integral_add h1 hcc_int, integral_sub htt_int (hct_int.const_mul 2),
      integral_const_mul, hcross, hsame']
    ring
  have hdiff : Integrable (fun ω => (M t ω - M c ω) * (M t ω - M c ω)) P :=
    (hMt.sub hMc).integrable_mul (hMt.sub hMc)
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => mul_self_nonneg _) hdiff).mp hzero
  filter_upwards [hae] with ω hω
  have h0 : M t ω - M c ω = 0 := mul_self_eq_zero.mp hω
  linarith
end LevyStochCalc.Ito

namespace LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  (W : MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : ∀ i : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W i) ℱ)
  {Z : ℝ → Ω → (Fin d → ℝ)}
  (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
  (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
  (hq : ∀ i : Fin d, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim

namespace LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {φ : Ω → ℝ → E → ℝ}
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end LevyStochCalc.Poisson.Compensated


