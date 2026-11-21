-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_IntegralLocality_F000
-- name    : LevyStochCalc_BSDEJ_IntegralLocality_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:21:07.682926+00:00
-- url     : https://prove2.me/theorems/d2544321-8cda-4895-9ffe-0a762a6dee5f
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.IntegralLocality
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.IntegralLocality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F001
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F002
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
import Definitions.Def_SourceProof_199d6571e2e85cd1e6522226
import Definitions.Def_SourceProof_1a359c540f605bc11b859735
import Definitions.Def_SourceProof_5a9b6e7ab698681a1e363ba1
import Definitions.Def_SourceProof_a11eee7d83378555a816acd3

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

end LevyStochCalc.Ito

namespace LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in
/-- The Itô integral of an integrand vanishing after a positive time does not move after it. -/
theorem stochasticIntegralBrownian_ae_eq_of_vanishing_gt {c t : ℝ} (hc : 0 < c) (hct : c ≤ t)
    (hH : ∀ ω s, c < s → H ω s = 0) :
    stochasticIntegralBrownian W ℱ hℱ H hm hp hq t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H hm hp hq c := by
  have hwin : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∫⁻ s in Set.Icc (0 : ℝ) c, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    have hdisj : Disjoint (Set.Icc (0 : ℝ) c) (Set.Ioc c t) :=
      Set.disjoint_left.2 fun s hs hs' => absurd hs'.1 (not_lt.2 hs.2)
    rw [← Set.Icc_union_Ioc_eq_Icc hc.le hct, lintegral_union measurableSet_Ioc hdisj,
      setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ≥0∞))
        (fun s hs => by simp [hH ω s hs.1]), lintegral_zero, add_zero]
  refine _root_.Prove2MeSourceProof.h_1a359c540f605bc11b859735 hct
    (_root_.Prove2MeSourceProof.h_199d6571e2e85cd1e6522226 W ℱ hℱ H hm hp hq)
    (stochasticIntegralBrownian_memLp W ℱ hℱ H hm hp hq t)
    (stochasticIntegralBrownian_memLp W ℱ hℱ H hm hp hq c) ?_
  rw [_root_.Prove2MeSourceProof.h_a11eee7d83378555a816acd3 W ℱ hℱ H hm hp hq (hc.le.trans hct),
    _root_.Prove2MeSourceProof.h_a11eee7d83378555a816acd3 W ℱ hℱ H hm hp hq hc.le]
  exact lintegral_congr hwin
include hℱ in
/-- The Itô integral of an integrand vanishing off a horizon `[0, T]` is, after `T`, the integral
at `T`. -/
theorem stochasticIntegralBrownian_ae_eq_of_vanish {T t : ℝ} (hT : 0 < T) (hTt : T ≤ t)
    (hH : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → H ω s = 0) :
    stochasticIntegralBrownian W ℱ hℱ H hm hp hq t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H hm hp hq T :=
  stochasticIntegralBrownian_ae_eq_of_vanishing_gt W ℱ hℱ hm hp hq hT hTt
    fun ω s hs => hH ω s fun h => absurd h.2 (not_le.2 hs)
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

include hℱ in
/-- The multidimensional Itô integral of an integrand vanishing after a positive time does not
move after it. -/
theorem stochasticIntegral_ae_eq_of_vanishing_gt {c t : ℝ} (hc : 0 < c) (hct : c ≤ t)
    (hZ : ∀ ω s, c < s → Z s ω = 0) :
    stochasticIntegral W ℱ hℱ Z hm hp hq t =ᵐ[P] stochasticIntegral W ℱ hℱ Z hm hp hq c := by
  have hcomp : ∀ i : Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱ i) (fun ω' s => Z s ω' i)
          (hm i) (hp i) (hq i) t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱ i) (fun ω' s => Z s ω' i)
          (hm i) (hp i) (hq i) c ω := fun i =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq_of_vanishing_gt (W.W i) ℱ (hℱ i)
      (hm i) (hp i) (hq i) hc hct fun ω s hs => by simp [hZ ω s hs]
  filter_upwards [Filter.eventually_all.2 hcomp] with ω hω
  exact Finset.sum_congr rfl fun i _ => hω i
include hℱ in
/-- The multidimensional Itô integral of an integrand vanishing off a horizon `[0, T]` is, after
`T`, the integral at `T`. -/
theorem stochasticIntegral_ae_eq_of_vanish {T t : ℝ} (hT : 0 < T) (hTt : T ≤ t)
    (hZ : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0) :
    stochasticIntegral W ℱ hℱ Z hm hp hq t =ᵐ[P] stochasticIntegral W ℱ hℱ Z hm hp hq T :=
  stochasticIntegral_ae_eq_of_vanishing_gt W ℱ hℱ hm hp hq hT hTt
    fun ω s hs => hZ ω s fun h => absurd h.2 (not_le.2 hs)
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

include hℱ in
/-- The compensated integral of an integrand vanishing off a horizon `[0, T]` is, after `T`, the
integral at `T`. -/
theorem stochasticIntegral_ae_eq_of_vanish {T t : ℝ} (hT : 0 < T) (hTt : T ≤ t)
    (hφ : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → φ ω s e = 0) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t =ᵐ[P] stochasticIntegral N ℱ hℱ φ hm hp hq T :=
  _root_.Prove2MeSourceProof.h_5a9b6e7ab698681a1e363ba1 N hℱ hm hp hq hT hTt
    fun ω s e hs => hφ ω s e fun h => absurd h.2 (not_le.2 hs)
end LevyStochCalc.Poisson.Compensated


