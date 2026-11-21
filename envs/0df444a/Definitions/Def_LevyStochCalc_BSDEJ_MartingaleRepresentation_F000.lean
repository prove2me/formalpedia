-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_MartingaleRepresentation_F000
-- name    : LevyStochCalc_BSDEJ_MartingaleRepresentation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:17:37.252219+00:00
-- url     : https://prove2.me/theorems/c0926de3-1741-4fce-aa30-6f94696597d9
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.MartingaleRepresentation
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.MartingaleRepresentation. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Definition_F000
import Definitions.Def_LevyStochCalc_Driver_CadlagMartingale_F001
import Definitions.Def_SourceProof_97d4630f3ae7c9c2d2a46808
import Definitions.Def_SourceProof_c8672576cdefe37eb0187287

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg conditional-expectation martingale of a joint filtration

Every square-integrable random variable `ξ` measurable at time `T` for the joint
right-continuous filtration of a Brownian motion `W` and a Poisson random measure `N` is the
terminal value of a càdlàg square-integrable martingale on that filtration whose value at time
`0` is `𝔼 ξ` (`condExp_to_PRP_martingale_form`). The content of that theorem is Doob's `L²`
càdlàg regularisation of the conditional-expectation martingale `t ↦ 𝔼[ξ ∣ ℱ₊ t]`
(Karatzas–Shreve I.3.13), together with Blumenthal's 0-1 law for the joint filtration, which is
what identifies the value at time `0` with `𝔼 ξ`. The martingale is
`LevyStochCalc.Driver.LevyDriver.cadlagCondExp`, built in `Driver/CadlagMartingale.lean`.

The theorem contains no predictable representation. Neither `W` nor the compensated measure
`Ñ` occurs in its conclusion, and nothing in it exhibits the martingale as a stochastic
integral. The representation this library does state is the terminal-time one,
`LevyStochCalc.Driver.LevyDriver.exists_predictable_jointIntegral` in
`Driver/PredictableRepresentation.lean`, which writes a centred square-integrable `Z`, measurable
at `T` for the augmented joint filtration `𝔸`, as `∑ i, ∫₀ᵀ G i dWⁱ + ∫₀ᵀ ∫ K dÑ` for predictable
integrands `G` and `K`. Its process-level form, the conditional expectation
`𝔼[Z ∣ 𝔸₊ t] = ∑ i, ∫₀ᵗ G i dWⁱ + ∫₀ᵗ ∫ K dÑ` almost surely at each `t ≤ T` for integrands not
asserted predictable, is
`LevyStochCalc.Driver.LevyDriver.exists_jointIntegralProcess_augFiltration_of_mean_zero` in
`Driver/JointPRPProcess.lean`; a pathwise identity along a càdlàg version is not stated.

Jacod 1975 and Jacod–Shiryaev III.4.34 are the literature for that predictable representation,
not for the theorem below. The formulation `jacodYor_PRP_martingale_axiom`, asking for
integrands adapted to the natural filtration of a single driver — the class the `L²` integrals
of this library were then built on — while the martingale is one of the joint filtration, is
refutable: the martingale `W_t · Ñ_t` is not representable in that class
(`tools/cited_axioms.md`, `Retired #13a`). The integrals now take a common filtration `ℱ` with
`LevyStochCalc.Brownian.IsBrownianFiltration` and `LevyStochCalc.Poisson.IsPoissonFiltration`
hypotheses; the property over the joint filtration of a Lévy driver is the terminal-time
representation above, and the single-driver representations are in
`Brownian/PRPMultidimAssembly.lean` and `Poisson/PredictableRepresentation.lean`.

## Source

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, Theorem I.3.13
  (the càdlàg regularisation and Blumenthal's 0-1 law behind the theorem below).
* Jacod, J. "Multivariate point processes: predictable projection,
  Radon-Nikodym derivatives, representation of martingales",
  Z. Wahrsch. Verw. Gebiete 31(3), 1975, pp 235–253 (the predictable representation, which is
  `Driver/PredictableRepresentation.lean`, not this file).
* Jacod–Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed.,
  Springer 2003, Theorem III.4.34 (likewise).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.MartingaleRepresentation

universe u v

section PRP
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The right-continuous joint filtration of a Lévy driver `D = (W, N)`, i.e. `ℱ₊`
for `ℱ = (⨆ i, ℱ^{Wⁱ}) ⊔ ℱ^N`. Every coordinate of `D.W` is a Brownian motion for
it and `D.N` a Poisson random measure (`LevyDriver.isBrownianFiltration`,
`.isPoissonFiltration`, lifted by `.rightCont`), and `D` carries the independence
`σ(W) ⟂ σ(N)` that the `M₀ = 𝔼 ξ` clause below needs. -/
noncomputable abbrev jointFiltration
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {d : ℕ}
    (D : LevyStochCalc.Driver.LevyDriver P d ν) :
    MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω› :=
  D.filtration.rightCont
end PRP

section Representation
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Every square-integrable random variable measurable for the joint right-continuous filtration
of a Lévy driver at time `T` is the terminal value of a càdlàg square-integrable martingale for
that filtration whose value at time `0` is its mean: Doob's `L²` càdlàg regularisation of the
conditional-expectation martingale of `ξ`, whose value at time `0` is identified by Blumenthal's
0-1 law. The conclusion carries no predictable representation; it does not exhibit the
martingale as a stochastic integral against `W` and `Ñ`. That representation, in its
terminal-time form, is `LevyDriver.exists_predictable_jointIntegral` in
`Driver/PredictableRepresentation.lean`. -/
theorem condExp_to_PRP_martingale_form
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {d : ℕ}
    (D : LevyStochCalc.Driver.LevyDriver P d ν)
    (T : ℝ)
    (ξ : Ω → ℝ)
    (h_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((jointFiltration D).seq T) ξ)
    (h_sq_int : ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤) :
    ∃ (M : ℝ → Ω → ℝ),
      MeasureTheory.Martingale M (jointFiltration D) P
      ∧ (∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤)
      ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
          Filter.Tendsto (fun s => M s ω)
            (nhdsWithin t (Set.Ioi t)) (nhds (M t ω))
            ∧ ∃ L : ℝ,
                Filter.Tendsto (fun s => M s ω)
                  (nhdsWithin t (Set.Iio t)) (nhds L))
      ∧ (∀ᵐ ω ∂P, M 0 ω = (∫ ω', ξ ω' ∂P))
      ∧ (∀ᵐ ω ∂P, M T ω = ξ ω) := by
  have hSM : MeasureTheory.StronglyMeasurable ξ :=
    h_meas.mono ((jointFiltration D).le T)
  have hξ : MeasureTheory.MemLp ξ 2 P := by
    refine ⟨hSM.aestronglyMeasurable, ?_⟩
    have heq : ∀ ω, ‖ξ ω‖ₑ ^ ENNReal.toReal 2 = (‖ξ ω‖₊ : ℝ≥0∞) ^ (2 : ℕ) := fun ω => by
      rw [show ENNReal.toReal 2 = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      rfl
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp_rw [heq]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt h_sq_int)
  have hterm := LevyStochCalc.Driver.LevyDriver.cadlagCondExp_terminal_ae_eq
    (D := D) (ξ := ξ) hξ hSM h_meas
  refine ⟨D.cadlagCondExp ξ,
    LevyStochCalc.Driver.LevyDriver.martingale_cadlagCondExp (D := D) (ξ := ξ) hξ hSM,
    ?_, ?_, LevyStochCalc.Driver.LevyDriver.cadlagCondExp_zero_ae_eq (D := D) (ξ := ξ) hξ hSM,
    hterm⟩
  · rw [MeasureTheory.lintegral_congr_ae (hterm.mono fun ω h => by rw [h])]
    exact h_sq_int
  · filter_upwards [_root_.Prove2MeSourceProof.h_c8672576cdefe37eb0187287
      (D := D) (ξ := ξ)] with ω hω t
    exact ⟨_root_.Prove2MeSourceProof.h_97d4630f3ae7c9c2d2a46808
      (D := D) (ξ := ξ) t ω, hω t⟩
end Representation

end LevyStochCalc.BSDEJ.MartingaleRepresentation


