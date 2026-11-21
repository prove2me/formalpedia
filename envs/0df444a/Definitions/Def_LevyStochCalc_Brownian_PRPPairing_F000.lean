-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F000
-- name    : LevyStochCalc_Brownian_PRPPairing_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:51:57.722049+00:00
-- url     : https://prove2.me/theorems/0a9d3180-e9fe-47a8-8ee9-27af486cf5cc
-- title:
--   Source declarations: LevyStochCalc.Brownian.PRPPairing
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PRPPairing. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_GronwallIntegral_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoPullOut_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoTrigIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing a weight orthogonal to the Itô integrals against a trigonometric increment

If `Z` pairs to zero against every Itô integral, then pairing it against `g (X_t)`, for `X` a
version of `∫ 1_{(a,b]} dW` and `g` one of the scaled trigonometric functions, gives a scalar
function of `t` that solves `Λ(t) = −(l²/2) ∫_0^t 1_{(a,b]}(s) Λ(s) ds`. Grönwall then forces
`Λ` to vanish.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The indicator of a window is idempotent. -/
theorem indIoc_sq (a b : ℝ) (ω : Ω) (s : ℝ) :
    indIoc Ω a b ω s ^ 2 = indIoc Ω a b ω s := by
  unfold indIoc
  by_cases h : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num
section Pairing

variable {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- An integrable weight times a bounded function is integrable. -/
theorem integrable_mul_of_bounded {Z : Ω → ℂ} (hZ : Integrable Z P) {F : Ω → ℂ}
    (hFm : AEStronglyMeasurable F P) {c : ℝ} (hFb : ∀ ω, ‖F ω‖ ≤ c) :
    Integrable (fun ω => Z ω * F ω) P := by
  refine Integrable.mono' (hZ.norm.const_mul c) (hZ.aestronglyMeasurable.mul hFm)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul]
  calc ‖Z ω‖ * ‖F ω‖ ≤ ‖Z ω‖ * c := mul_le_mul_of_nonneg_left (hFb ω) (norm_nonneg _)
    _ = c * ‖Z ω‖ := mul_comm _ _
variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

/-- A weight that pairs to zero against every `L²` Itô integral. -/
structure PerpItoIntegrals (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (Z : Ω → ℂ) : Prop where
  /-- The pairing against every Itô integral vanishes. -/
  perp : ∀ (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ), 0 < t →
    ∫ ω, Z ω * ((stochasticIntegralBrownian W ℱ hℱ K hm hp hq t ω : ℝ) : ℂ) ∂P = 0
/-- The pairing of a weight against a bounded continuous function of a jointly measurable
process is measurable in the time parameter. -/
theorem measurable_pairing {Z : Ω → ℂ} (hZm : Measurable Z) {X : ℝ → Ω → ℝ}
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) {g : ℝ → ℝ} (hg : Continuous g) :
    Measurable fun t : ℝ => ∫ ω, Z ω * ((g (X t ω) : ℝ) : ℂ) ∂P := by
  have hjoint : StronglyMeasurable (Function.uncurry fun (t : ℝ) (ω : Ω) =>
      Z ω * ((g (X t ω) : ℝ) : ℂ)) := by
    refine Measurable.stronglyMeasurable ?_
    refine (hZm.comp measurable_snd).mul ?_
    refine Complex.measurable_ofReal.comp (hg.measurable.comp ?_)
    exact hXm.comp (measurable_snd.prodMk measurable_fst)
  exact (hjoint.integral_prod_right).measurable
variable {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

include hℱ in
/-- A version of `∫ 1_{(a,b]} dW` vanishes at time zero. -/
theorem ae_eq_zero_of_isItoVersion_indIoc (ha : 0 ≤ a) (hab : a < b)
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X) :
    X 0 =ᵐ[P] fun _ => (0 : ℝ) := by
  have h1 := hX.ae_eq 0 le_rfl
  have h2 := _root_.Prove2MeSourceProof.h_969e6fb8eb30320c0ccbf403 W ℱ hℱ ha hab hm hp hq (le_refl (0 : ℝ))
  have hb0 : (0 : ℝ) ≤ b := le_trans ha hab.le
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1]
  change (0 : ℝ) + (∫ _s in Set.Icc (0 : ℝ) 0, (0 : ℝ) ∂volume)
      + stochasticIntegralBrownian W ℱ hℱ (indIoc Ω a b) hm hp hq 0 ω = 0
  rw [hω2]
  simp [min_eq_right hb0, min_eq_right ha]
include hℱ in
/-- At the right end of the window a version of `∫ 1_{(a,b]} dW` is the Brownian increment. -/
theorem ae_eq_increment_of_isItoVersion_indIoc (ha : 0 ≤ a) (hab : a < b)
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X) :
    X b =ᵐ[P] fun ω => W.W b ω - W.W a ω := by
  have hb0 : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have h1 := hX.ae_eq b hb0.le
  have h2 := _root_.Prove2MeSourceProof.h_969e6fb8eb30320c0ccbf403 W ℱ hℱ ha hab hm hp hq hb0.le
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1]
  change (0 : ℝ) + (∫ _s in Set.Icc (0 : ℝ) b, (0 : ℝ) ∂volume)
      + stochasticIntegralBrownian W ℱ hℱ (indIoc Ω a b) hm hp hq b ω = _
  rw [hω2]
  simp [min_self, min_eq_left hab.le]
/-- A real function in `L²` stays in `L²` after coercion to `ℂ`. -/
theorem memLp_ofReal {P : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 2 P) :
    MemLp (fun ω => ((f ω : ℝ) : ℂ)) 2 P := by
  refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1, ?_⟩
  have hnorm : eLpNorm (fun ω => ((f ω : ℝ) : ℂ)) 2 P = eLpNorm f 2 P :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ω => by simp)
  rw [hnorm]
  exact hf.2
end Pairing

section Perp

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}

end Perp

section Equation

variable {P : Measure Ω} [IsProbabilityMeasure P]

end Equation

end LevyStochCalc.Brownian.Ito


