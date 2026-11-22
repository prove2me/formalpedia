-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpDiffusionAdapted_F000
-- name    : LevyStochCalc_Ito_JumpDiffusionAdapted_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:12:27.838664+00:00
-- url     : https://prove2.me/theorems/9ddb9a20-3067-4354-8e41-69987e6b6033
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpDiffusionAdapted
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpDiffusionAdapted. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F000
import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F001
import Definitions.Def_SourceProof_4dc182a98fe43374f6dd9730
import Definitions.Def_SourceProof_7b7fe4c6b4bf6f12571973df
import Definitions.Def_SourceProof_d86b93a1720501bd3dee4555

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Adaptedness of a jump diffusion

The jump-diffusion integral equation of `LevyStochCalc.Ito.Picard.SolvesOn` expresses the path
map at time `t` as the sum of a drift integral over `[0, t]`, a Brownian Itô integral and a
compensated Poisson integral. The Brownian integral is strongly adapted to `ℱ`
(`LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted`), the compensated
integral is adapted to the right-continuation `ℱ₊` of `ℱ`
(`LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted`), and the drift integral of a
progressively measurable integrand is `ℱ t`-measurable
(`ProgressivelyMeasurable.measurable_setIntegral_Icc`), so the right-hand side is
`ℱ₊ t`-measurable and the equation transfers that measurability to the path map up to a null
set.

## Main statements

* `SolvesOn.aeStronglyMeasurable_rightCont` — the path map at time `t` is
  `ℱ₊ t`-a.e.-strongly measurable, given progressive measurability of the drift
  integrand along the path.
* `SolvesOn.stronglyMeasurable_rightCont` — the same with the null set absorbed, when `ℱ 0`
  contains the `P`-null sets and the path map is jointly measurable.
* `SolvesOn.stronglyMeasurable_of_isRegular` — under the usual conditions and the Lipschitz and
  regularity hypotheses on the coefficients, every jointly measurable, `S²`-bounded solution on
  all horizons is `ℱ t`-strongly measurable at every `t ≥ 0`; no hypothesis on the drift
  integrand is needed.
* `JumpDiffusion.stronglyMeasurable_of_solvesOn`, `JumpDiffusion.exists_unique_adapted` — the
  same for a `JumpDiffusion` solving the equation relative to `ℱ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {α : Type*} [MeasurableSpace α]

end LevyStochCalc.Probability

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The multidimensional Brownian Itô integral is strongly adapted to the filtration of its
integrand. -/
theorem stronglyAdapted_stochasticIntegral (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (h_meas : ∀ i : Fin d, Measurable (Function.uncurry (fun ω s => Z s ω i)))
    (h_progMeas : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ (fun ω s => Z s ω i))
    (h_sq : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    StronglyAdapted ℱ (stochasticIntegral W ℱ hℱ Z h_meas h_progMeas h_sq) := by
  intro t
  have key : ∀ i : Fin d, Measurable[ℱ t]
      (LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱ i) (fun ω' s => Z s ω' i)
        (h_meas i) (h_progMeas i) (h_sq i) t) := fun i =>
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W i) ℱ (hℱ i)
      (fun ω' s => Z s ω' i) (h_meas i) (h_progMeas i) (h_sq i) t).measurable
  letI : MeasurableSpace Ω := ℱ t
  exact (Finset.measurable_sum Finset.univ fun i _ => key i).stronglyMeasurable
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)

/-- The right-hand side of the jump-diffusion integral equation at time `t` is
`ℱ.rightCont t`-measurable in each coordinate, for an integrand bundle whose drift component is
progressively measurable. -/
theorem measurable_rightCont_picardStep {X : ℝ → Ω → (Fin n → ℝ)}
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X s ω) i j)
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X s ω) e i)
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_μ_progMeas : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (X s ω) i)
    (t : ℝ) (i : Fin n) :
    Measurable[ℱ.rightCont t] fun ω =>
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas
        h_γ_sq t ω i := by
  have hdrift : Measurable[ℱ.rightCont t]
      fun ω => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i :=
    ((_root_.Prove2MeSourceProof.h_4dc182a98fe43374f6dd9730 (h_μ_progMeas i)) t).mono (ℱ.le_rightCont t) le_rfl
  have hdiff : Measurable[ℱ.rightCont t]
      fun ω => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
        (fun s ω' j => coeffs.σ s (X s ω') i j) (h_σ_meas i) (h_σ_progMeas i) (h_σ_sq i) t ω :=
    ((LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stronglyAdapted_stochasticIntegral
      W ℱ hℱW _ (h_σ_meas i) (h_σ_progMeas i) (h_σ_sq i) t).measurable).mono
      (ℱ.le_rightCont t) le_rfl
  have hjump : Measurable[ℱ.rightCont t]
      fun ω => LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
        (fun ω' s e => coeffs.γ s (X s ω') e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) t ω :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN _ (h_γ_meas i)
      (h_γ_progMeas i) (h_γ_sq i) t
  simp only [picardStep, picardStep_drift, picardStep_diffusion, picardStep_jump, Pi.add_apply]
  exact ((measurable_const.add hdrift).add hdiff).add hjump
/-- A solution of the jump-diffusion equation on `[0, T]` whose drift integrand is progressively
measurable is `ℱ.rightCont t`-a.e.-strongly measurable at every `t ∈ [0, T]`. -/
theorem SolvesOn.aeStronglyMeasurable_rightCont {X : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T)
    (h_μ_progMeas : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (X s ω) i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    AEStronglyMeasurable[ℱ.rightCont t] (X t) P := by
  have key : ∀ i : Fin n, Measurable[ℱ.rightCont t] fun ω =>
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h.h_σ_meas h.h_σ_progMeas h.h_σ_sq h.h_γ_meas
        h.h_γ_progMeas h.h_γ_sq t ω i := fun i =>
    measurable_rightCont_picardStep W N ℱ hℱW hℱN coeffs x₀ h.h_σ_meas h.h_σ_progMeas
      h.h_σ_sq h.h_γ_meas h.h_γ_progMeas h.h_γ_sq h_μ_progMeas t i
  refine ⟨fun ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h.h_σ_meas h.h_σ_progMeas h.h_σ_sq
    h.h_γ_meas h.h_γ_progMeas h.h_γ_sq t ω, ?_, ?_⟩
  · letI : MeasurableSpace Ω := ℱ.rightCont t
    exact (measurable_pi_lambda _ key).stronglyMeasurable
  · filter_upwards [h.eqn t ht] with ω hω
    exact funext fun i => hω i
/-- A solution of the jump-diffusion equation on `[0, T]` with a jointly measurable path map and
a progressively measurable drift integrand is `ℱ.rightCont t`-strongly measurable at every
`t ∈ [0, T]`, when `ℱ 0` contains the `P`-null sets. -/
theorem SolvesOn.stronglyMeasurable_rightCont {X : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T)
    (h_μ_progMeas : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (X s ω) i)
    (hXm : Measurable (Function.uncurry X))
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    StronglyMeasurable[ℱ.rightCont t] (X t) := by
  have hnull' : ∀ s : Set Ω, MeasurableSet[mΩ] s → P s = 0 → MeasurableSet[ℱ.rightCont t] s :=
    fun s hs h0 => (ℱ.le_rightCont t) _ (ℱ.mono ht.1 _ (hnull s hs h0))
  have key : ∀ i : Fin n, Measurable[ℱ.rightCont t] fun ω => X t ω i := by
    intro i
    refine _root_.Prove2MeSourceProof.h_7b7fe4c6b4bf6f12571973df hnull'
      ((measurable_pi_apply i).comp (Measurable.of_uncurry_left hXm))
      (measurable_rightCont_picardStep W N ℱ hℱW hℱN coeffs x₀ h.h_σ_meas h.h_σ_progMeas h.h_σ_sq
        h.h_γ_meas h.h_γ_progMeas h.h_γ_sq h_μ_progMeas t i) ?_
    filter_upwards [h.eqn t ht] with ω hω using hω i
  letI : MeasurableSpace Ω := ℱ.rightCont t
  exact (measurable_pi_lambda _ key).stronglyMeasurable
/-- Under the usual conditions on `ℱ` and the Lipschitz and regularity hypotheses on the
coefficients, a jointly measurable, `S²`-bounded solution of the jump-diffusion equation on all
horizons is `ℱ t`-strongly measurable at every `t ≥ 0`. -/
theorem SolvesOn.stronglyMeasurable_of_isRegular [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X : ℝ → Ω → (Fin n → ℝ)} (hXm : Measurable (Function.uncurry X))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hX : ∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T)
    {t : ℝ} (ht : 0 ≤ t) :
    StronglyMeasurable[ℱ t] (X t) := by
  obtain ⟨Y, hYm, hYp, -, -, hYS, hYsol⟩ :=
    _root_.Prove2MeSourceProof.h_a1d63148328e300a17a03a3d W N ℱ hℱW hℱN coeffs hℱ0 hnull hReg hLip x₀
  have hae : ∀ᵐ ω ∂P, ∀ i : Fin n, X t ω i = Y t ω i :=
    _root_.Prove2MeSourceProof.h_48fc762eec2686f4f3c5681d W N ℱ hℱW hℱN coeffs x₀ hReg hLip hXm hYm hXS hYS
      (show (0 : ℝ) < t + 1 by linarith) (hX (t + 1)) (hYsol (t + 1)) t ⟨ht, by linarith⟩
  have hnull' : ∀ s : Set Ω, MeasurableSet[mΩ] s → P s = 0 → MeasurableSet[ℱ t] s :=
    fun s hs h0 => ℱ.mono ht _ (hnull s hs h0)
  have key : ∀ i : Fin n, Measurable[ℱ t] fun ω => X t ω i := by
    intro i
    refine _root_.Prove2MeSourceProof.h_7b7fe4c6b4bf6f12571973df hnull'
      ((measurable_pi_apply i).comp (Measurable.of_uncurry_left hXm))
      ((hYp i).stronglyMeasurable_eval t).measurable ?_
    filter_upwards [hae] with ω hω using hω i
  letI : MeasurableSpace Ω := ℱ t
  exact (measurable_pi_lambda _ key).stronglyMeasurable
end LevyStochCalc.Ito.Picard

namespace LevyStochCalc.Ito.Setting
namespace JumpDiffusion

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
variable {ν : Measure E} [SigmaFinite ν]

/-- A `JumpDiffusion` solving the equation relative to a filtration satisfying the usual
conditions is adapted to that filtration on `[0, ∞)`. -/
theorem stronglyMeasurable_of_solvesOn
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (jd : JumpDiffusion W N coeffs x₀)
    (hjd : ∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd.X T)
    {t : ℝ} (ht : 0 ≤ t) :
    StronglyMeasurable[ℱ t] (jd.X t) :=
  LevyStochCalc.Ito.Picard.SolvesOn.stronglyMeasurable_of_isRegular W N ℱ hℱW hℱN coeffs x₀
    hℱ0 hnull hReg hLip jd.measurable_path jd.sup_L2 hjd ht
/-- **Existence, uniqueness and adaptedness of the jump-diffusion SDE.** The solution of
`JumpDiffusion.exists_unique` is adapted to the filtration on `[0, ∞)`, and so is every solution
of the equation relative to that filtration. -/
theorem exists_unique_adapted
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : JumpDiffusionCoeffs n d E) (x₀ : Fin n → ℝ)
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs ν) :
    ∃ jd : JumpDiffusion W N coeffs x₀,
      (∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd.X T)
        ∧ (∀ t : ℝ, 0 ≤ t → StronglyMeasurable[ℱ t] (jd.X t))
        ∧ ∀ jd' : JumpDiffusion W N coeffs x₀,
            (∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd'.X T) →
              (∀ t : ℝ, 0 ≤ t → StronglyMeasurable[ℱ t] (jd'.X t))
                ∧ ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω := by
  obtain ⟨jd, hjd, huniq⟩ :=
    _root_.Prove2MeSourceProof.h_d86b93a1720501bd3dee4555 W N ℱ hℱW hℱN hℱ0 hnull coeffs x₀ hLip hReg
  refine ⟨jd, hjd, fun t ht => stronglyMeasurable_of_solvesOn W N ℱ hℱW hℱN hℱ0 hnull hReg hLip
    jd hjd ht, fun jd' hjd' => ⟨fun t ht => stronglyMeasurable_of_solvesOn W N ℱ hℱW hℱN hℱ0
      hnull hReg hLip jd' hjd' ht, huniq jd' hjd'⟩⟩
end JumpDiffusion
end LevyStochCalc.Ito.Setting


