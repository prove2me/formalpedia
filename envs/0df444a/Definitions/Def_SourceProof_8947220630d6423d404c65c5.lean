-- Prove2me | Definitions.Def_SourceProof_8947220630d6423d404c65c5
-- name    : SourceProof_8947220630d6423d404c65c5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:53:34.739169+00:00
-- url     : https://prove2.me/theorems/9d000424-db0b-4231-b1c8-bf828100e30d
-- title:
--   LevyStochCalc source module: SourceProof_8947220630d6423d404c65c5
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.pairing_ito_eq_zero` comes from the `LevyStochCalc.Brownian.PRPPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F000
import Definitions.Def_SourceProof_92bec27d240f0e5702c6d539
import Definitions.Def_SourceProof_a85377d9ae43b1c0795fd7b5

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

section Pairing

variable {P : Measure Ω} [IsProbabilityMeasure P]

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

variable {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

end Pairing

section Perp

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}

include hℱ in

theorem _root_.Prove2MeSourceProof.h_8947220630d6423d404c65c5 (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℂ} (hZ2 : MemLp Z 2 P) (hZp : PerpItoIntegrals W ℱ hℱ Z)
    {V : Ω → ℂ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, ‖V ω‖ ≤ Mv)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℂ _ (ℱ a) V)
    {K : Ω → ℝ → ℝ} (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K) {Kb : ℝ}
    (hKbd : ∀ ω s, |K ω s| ≤ Kb)
    (hmg : Measurable (Function.uncurry fun ω s => K ω s * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => K ω s * indIoc Ω a b ω s)
    (hqg : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, Z ω * V ω * ((stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ) ∂P = 0 := by
  classical
  have hswap : (fun (ω : Ω) (s : ℝ) => LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s)
      = fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s := by
    funext ω s; ring
  have him : Measurable (Function.uncurry fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s) := by
    rw [hswap]; exact hmg
  have hip : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s := by
    rw [hswap]; exact hpg
  have hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T hT
    have hpt : ∀ (ω : Ω) (s : ℝ),
        LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s = K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s := fun ω s => mul_comm _ _
    simp_rw [hpt]
    exact hqg T hT
  have hIeq := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hswap him hip hiq hmg hpg hqg t
  have hKq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T hT => _root_.Prove2MeSourceProof.h_aa77a05410d36d075f77b369 hKbd T hT
  -- each real component of the weight passes inside the integral
  have hcomp : ∀ Vr : Ω → ℝ, Measurable Vr → (∀ ω, |Vr ω| ≤ Mv) →
      @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Vr →
      Integrable (fun ω => Z ω * ((Vr ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)) P
        ∧ ∫ ω, Z ω * ((Vr ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ) ∂P = 0 := by
    intro Vr hVrm hVrb hVra
    have hvm : Measurable (Function.uncurry fun ω s => Vr ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s) := by
      have h1 : Measurable fun p : Ω × ℝ => Vr p.1 * LevyStochCalc.Brownian.Ito.indIoc Ω a b p.1 p.2 :=
        (hVrm.comp measurable_fst).mul (LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc a b)
      exact h1.mul hKm
    have hvp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        fun ω s => Vr ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s :=
      (_root_.Prove2MeSourceProof.h_a85377d9ae43b1c0795fd7b5 ℱ ha hab ⟨Mv, hVrb⟩ hVrm hVra).mul hKp
    have hvbd : ∀ (ω : Ω) (s : ℝ), |Vr ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s| ≤ Mv * 1 * Kb := by
      intro ω s
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hVrb ω) (LevyStochCalc.Brownian.Ito.indIoc_le_one a b ω s) (abs_nonneg _) hMv0)
        (hKbd ω s) (abs_nonneg _) (by positivity)
    have hvq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Vr ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      fun T hT => _root_.Prove2MeSourceProof.h_aa77a05410d36d075f77b369 hvbd T hT
    have hpull := _root_.Prove2MeSourceProof.h_92bec27d240f0e5702c6d539 W ℱ hℱ ha hab ⟨Mv, hVrb⟩ hVrm hVra
      K hKm hKp hKq him hip hiq hvm hvp hvq ht
    -- the product is a.e. an Itô integral, hence square integrable
    have hae : (fun ω => Vr ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω)
        =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => Vr ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s) hvm hvp hvq t := by
      filter_upwards [hpull] with ω hω
      rw [← hIeq]
      exact hω
    have hL2 : MemLp (fun ω => ((Vr ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)) 2 P :=
      LevyStochCalc.Brownian.Ito.memLp_ofReal
        ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ _ hvm hvp hvq t).ae_eq hae.symm)
    refine ⟨hZ2.integrable_mul hL2, ?_⟩
    have hcong : ∫ ω, Z ω * ((Vr ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ) ∂P
        = ∫ ω, Z ω * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => Vr ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s) hvm hvp hvq t ω : ℝ) : ℂ) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with ω hω
      exact congrArg (fun x : ℝ => Z ω * ((x : ℝ) : ℂ)) hω
    rw [hcong]
    exact hZp.perp _ hvm hvp hvq t ht
  obtain ⟨hreint, hre⟩ := hcomp (fun ω => (V ω).re) (Complex.measurable_re.comp hVm)
    (fun ω => le_trans (Complex.abs_re_le_norm _) (hVb ω))
    (Complex.continuous_re.comp_stronglyMeasurable hVa)
  obtain ⟨himint, himz⟩ := hcomp (fun ω => (V ω).im) (Complex.measurable_im.comp hVm)
    (fun ω => le_trans (Complex.abs_im_le_norm _) (hVb ω))
    (Complex.continuous_im.comp_stronglyMeasurable hVa)
  have hdecomp : ∀ ω : Ω, Z ω * V ω * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)
      = Z ω * (((V ω).re * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)
        + Complex.I * (Z ω * (((V ω).im * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)) := by
    intro ω
    have hV : ((V ω).re : ℂ) + ((V ω).im : ℂ) * Complex.I = V ω := Complex.re_add_im (V ω)
    calc Z ω * V ω * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
            (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)
        = Z ω * (((V ω).re : ℂ) + ((V ω).im : ℂ) * Complex.I)
            * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => K ω s * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ) := by rw [hV]
      _ = _ := by push_cast; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hdecomp),
    integral_add hreint (himint.const_mul Complex.I), hre, integral_const_mul, himz,
    mul_zero, add_zero]
end Perp

section Equation

variable {P : Measure Ω} [IsProbabilityMeasure P]

end Equation

end LevyStochCalc.Brownian.Ito


