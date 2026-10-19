-- Prove2me | Definitions.Def_OAIE3v2B046
-- name    : OAIE3v2B046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:12:50.441563+00:00
-- url     : https://prove2.me/theorems/a1a780a9-d850-4212-9c0d-93bab0817ceb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 47 of 311
-- statement:
--   Definitions bundle 47 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B001`, `OAIE3v2B004`, `OAIE3v2B007`, `OAIE3v2B011`, `OAIE3v2B012`, `OAIE3v2B013` of this split.
--
--   Modules: `Dynamics/CrootSisaskSampleBudget.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/CyclicRelativeChang.lean`, `Estimates/LocalBoostedAlmostPeriods.lean`, `Estimates/LocalShiftFiber.lean`, `Estimates/LocalizedSiftingAlmostPeriods.lean`, `Estimates/PinnedSectionMeans.lean`, `FixedDensity/OrderedRemoval.lean`, `Fourier/BohrTorusApproximation.lean`, `Fourier/CyclicAffineCharacterPhase.lean`, `Fourier/ExponentialBohrVolume.lean`, `Fourier/FiniteFourierSmoothing.lean`, `Fourier/LocalBohrAlmostPeriodsRelative.lean`, `Fourier/RectangularGridCharacter.lean`, `Fourier/RelativeSpectrumDimension.lean`, `Fourier/TranslatedBohrDifference.lean`, `Geometry/CoordinateLeafCount.lean`, `Geometry/CoordinateTreeOutside.lean`, `Geometry/CoordinateTreeRelabel.lean`, `Geometry/CoordinateTreeTrace.lean`, `Geometry/DifferenceEventSupport.lean`, `Lattices/CircleResiduePartition.lean`, `Lattices/ResidueSliceCountingCost.lean`, `Polynomial/AffinePhaseBias.lean`, `Probability/DifferenceEventProbability.lean`, `Probability/MassConvolution.lean`, `Probability/ObservedProductDensity.lean`, `Sampling/CyclicSamplingMoments.lean`, `Sampling/FiniteSamplingMoment.lean`, `Sampling/LocalSamplingBudget.lean`, `Sampling/QuarticSamplingBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B012
import Definitions.Def_OAIE3v2B013

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CrootSisaskSampleBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

theorem samplingMomentCost_nonneg (m k : ℕ) : 0 ≤ samplingMomentCost m k := by
  unfold samplingMomentCost
  positivity

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem star_finiteFourierCoeff (f : H → ℂ) (χ : AddChar H ℂ) :
    star (finiteFourierCoeff f χ) = 𝔼 x, star (f x) * χ x := by
  rw [finiteFourierCoeff, ← expect_star]
  apply Finset.expect_congr rfl
  intro x _
  simp only [star_mul, star_star]
  ring

theorem finiteFourier_inner (f g : H → ℂ) :
    (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * star (finiteFourierCoeff g χ)) =
      𝔼 x, f x * star (g x) := by
  simp_rw [star_finiteFourierCoeff, Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  calc
    _ = (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * χ x) * star (g x) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by rw [finiteFourier_inversion]

theorem finiteFourier_parseval (f : H → ℂ) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff f χ‖ ^ 2) = 𝔼 x, ‖f x‖ ^ 2 := by
  have h := congrArg Complex.re (finiteFourier_inner f f)
  simpa only [Complex.re_sum, expect_re, mul_star_re_eq_norm_sq] using h

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem finiteFourierCoeff_finiteSetAverage
    (A : Finset G) (f : G → ℂ) (psi : AddChar G ℂ) :
    finiteFourierCoeff (finiteSetAverage A f) psi =
      setFourierMultiplier A psi * finiteFourierCoeff f psi := by
  unfold finiteFourierCoeff finiteSetAverage
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  change (𝔼 a ∈ A, finiteFourierCoeff (fun x => f (x - a)) psi) = _
  simp_rw [finiteFourierCoeff_translate]
  rw [← Finset.expect_mul]
  rfl

omit [Fintype G] in
theorem setFourierMultiplier_eq (A : Finset G) (psi : AddChar G ℂ) :
    setFourierMultiplier A psi = star (Chang.spectrumSum A psi) / (A.card : ℂ) := by
  simp only [setFourierMultiplier, Finset.expect_eq_sum_div_card, Chang.spectrumSum, star_sum]

omit [Fintype G] in
theorem norm_setFourierMultiplier (A : Finset G) (psi : AddChar G ℂ) :
    ‖setFourierMultiplier A psi‖ = ‖Chang.spectrumSum A psi‖ / A.card := by
  rw [setFourierMultiplier_eq, norm_div, norm_star, Complex.norm_natCast]

theorem mem_largeSpectrum_iff_le_multiplier {A : Finset G} (hA : A.Nonempty)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ Chang.largeSpectrum A eta ↔ eta ≤ ‖setFourierMultiplier A psi‖ := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  rw [Chang.mem_largeSpectrum, norm_setFourierMultiplier, le_div_iff₀ hcard]

noncomputable def iteratedFiniteSetAverage (A : Finset G) (f : G → ℂ) : ℕ → G → ℂ
  | 0 => f
  | n + 1 => finiteSetAverage A (iteratedFiniteSetAverage A f n)

theorem finiteFourierCoeff_iteratedFiniteSetAverage
    (A : Finset G) (f : G → ℂ) (psi : AddChar G ℂ) (n : ℕ) :
    finiteFourierCoeff (iteratedFiniteSetAverage A f n) psi =
      setFourierMultiplier A psi ^ n * finiteFourierCoeff f psi := by
  induction n with
  | zero => simp [iteratedFiniteSetAverage]
  | succ n ih =>
      rw [iteratedFiniteSetAverage, finiteFourierCoeff_finiteSetAverage, ih, pow_succ]
      ring

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem iteratedFiniteSetAverage_translate_le
    {X : Finset G} (hX : X.Nonempty) (m : ℕ) (f : G → ℂ)
    {eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : G)
    (hphase : ∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) :
    ‖iteratedFiniteSetAverage X f m (x - t) - iteratedFiniteSetAverage X f m x‖ ≤
      (theta + 2 * eta ^ m) * fourierL1 f := by
  apply (norm_sub_translate_le_fourier_sum (iteratedFiniteSetAverage X f m) t x).trans
  calc
    (∑ psi : AddChar G ℂ,
        ‖finiteFourierCoeff (iteratedFiniteSetAverage X f m) psi‖ * ‖psi (-t) - 1‖) ≤
        ∑ psi : AddChar G ℂ, (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
      apply Finset.sum_le_sum
      intro psi _
      rw [finiteFourierCoeff_iteratedFiniteSetAverage, norm_mul, norm_pow,
        norm_character_neg_sub_one]
      have hmu := norm_setFourierMultiplier_le_one hX psi
      by_cases hlarge : eta ≤ ‖setFourierMultiplier X psi‖
      · have hpow : ‖setFourierMultiplier X psi‖ ^ m ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) hmu
        have hp := hphase psi ((mem_largeSpectrum_iff_le_multiplier hX eta psi).2 hlarge)
        calc
          ‖setFourierMultiplier X psi‖ ^ m * ‖finiteFourierCoeff f psi‖ * ‖1 - psi t‖ ≤
              1 * ‖finiteFourierCoeff f psi‖ * theta := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
            have hepow : 0 ≤ eta ^ m := pow_nonneg heta m
            have hf : 0 ≤ ‖finiteFourierCoeff f psi‖ := norm_nonneg _
            nlinarith
      · have htail : ‖setFourierMultiplier X psi‖ ^ m ≤ eta ^ m :=
          pow_le_pow_left₀ (norm_nonneg _) (le_of_not_ge hlarge) m
        have hchord : ‖1 - psi t‖ ≤ 2 := by
          calc
            ‖1 - psi t‖ ≤ ‖(1 : ℂ)‖ + ‖psi t‖ := norm_sub_le _ _
            _ = 2 := by norm_num
        calc
          ‖setFourierMultiplier X psi‖ ^ m * ‖finiteFourierCoeff f psi‖ * ‖1 - psi t‖ ≤
              eta ^ m * ‖finiteFourierCoeff f psi‖ * 2 := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
            have hf : 0 ≤ ‖finiteFourierCoeff f psi‖ := norm_nonneg _
            nlinarith
    _ = (theta + 2 * eta ^ m) * fourierL1 f := by rw [fourierL1, Finset.mul_sum]

theorem translate_le_of_iteratedFiniteSetAverage_approx
    {X : Finset G} (hX : X.Nonempty) (m : ℕ) (f : G → ℂ)
    {delta eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : G)
    (happrox : ∀ y, ‖iteratedFiniteSetAverage X f m y - f y‖ ≤ delta)
    (hphase : ∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) :
    ‖f (x - t) - f x‖ ≤ 2 * delta + (theta + 2 * eta ^ m) * fourierL1 f := by
  let p := iteratedFiniteSetAverage X f m
  have hdecomp : f (x - t) - f x =
      (f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x) := by ring
  rw [hdecomp]
  calc
    ‖(f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x)‖ ≤
        ‖f (x - t) - p (x - t)‖ + ‖p (x - t) - p x‖ + ‖p x - f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ delta + ((theta + 2 * eta ^ m) * fourierL1 f) + delta := by
      apply add_le_add
      · apply add_le_add
        · simpa only [norm_sub_rev] using happrox (x - t)
        · exact iteratedFiniteSetAverage_translate_le hX m f heta htheta t x hphase
      · exact happrox x
    _ = 2 * delta + (theta + 2 * eta ^ m) * fourierL1 f := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

noncomputable def averagingKernel (B : Finset H) (x : H) : ℂ :=
  (Fintype.card H : ℂ) / B.card * finiteIndicator B x

omit [AddCommGroup H] in
theorem mean_indicator_norm_sq (I : Finset H) :
    (𝔼 x, ‖finiteIndicator I x‖ ^ 2) = (I.card : ℝ) / Fintype.card H := by
  have he (x : H) : ‖finiteIndicator I x‖ ^ 2 = if x ∈ I then (1 : ℝ) else 0 := by
    by_cases hx : x ∈ I <;> simp [finiteIndicator, hx]
  simp only [he, Fintype.expect_eq_sum_div_card]
  simp

theorem mean_averagingKernel_norm_sq {B : Finset H} (hB : B.Nonempty) :
    (𝔼 x, ‖averagingKernel B x‖ ^ 2) = (Fintype.card H : ℝ) / B.card := by
  have hn : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  simp only [averagingKernel, norm_mul, norm_div, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_expect, mean_indicator_norm_sq]
  field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MassConvolution
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [DecidableEq G]

theorem realUniformMass_nonneg (A : Finset G) (x : G) : 0 ≤ realUniformMass A x := by
  unfold realUniformMass
  split_ifs <;> positivity

theorem sum_realUniformMass [Fintype G] {A : Finset G} (hA : A.Nonempty) :
    ∑ x, realUniformMass A x = 1 := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  simp [realUniformMass, hcard]

end Erdos3

end

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [AddCommGroup G] [Fintype G] in
theorem realUniformMass_ne_zero_iff {A : Finset G} (hA : A.Nonempty) (x : G) :
    realUniformMass A x ≠ 0 ↔ x ∈ A := by
  unfold realUniformMass
  split_ifs with hx
  · simp [hx, hA.card_ne_zero]
  · simp [hx]

omit [DecidableEq G] in
theorem massConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (z : G) :
    0 ≤ massConvolution f g z := by
  exact sum_nonneg fun x _ ↦ mul_nonneg (hf x) (hg (z - x))

omit [DecidableEq G] in

theorem massConvolution_comm (f g : G → ℝ) :
    massConvolution f g = massConvolution g f := by
  funext x
  rw [massConvolution, massConvolution]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ ?_
  simp [mul_comm]

omit [DecidableEq G] in

theorem sum_massConvolution (f g : G → ℝ) :
    ∑ x : G, massConvolution f g x = (∑ x : G, f x) * ∑ x : G, g x := by
  simp_rw [massConvolution, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun x ↦ by simp

@[simp] theorem convolutionPower_succ (f : G → ℝ) (n : ℕ) :
    convolutionPower f (n + 1) =
      massConvolution (convolutionPower f n) f := rfl

theorem convolutionPower_nonneg {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ n x, 0 ≤ convolutionPower f n x := by
  intro n
  induction n with
  | zero =>
      exact realUniformMass_nonneg {0}
  | succ n ihn =>
      exact massConvolution_nonneg ihn hf

theorem sum_convolutionPower {f : G → ℝ} (hf : ∑ x : G, f x = 1) :
    ∀ n, ∑ x : G, convolutionPower f n x = 1 := by
  intro n
  induction n with
  | zero =>
      exact sum_realUniformMass (singleton_nonempty 0)
  | succ n ihn =>
      rw [convolutionPower_succ, sum_massConvolution, ihn, hf, one_mul]

end

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RelativeSpectrumDimension
namespace OAI

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

namespace RelativeSpectrumBridge

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem sum_realFinsetIndicator_mul_character_eq_const_mul
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (psi : AddChar G ℂ) :
    ∑ x : G, ((realFinsetIndicator X x * w x : ℝ) : ℂ) * psi x =
      (c : ℂ) * Chang.spectrumSum X psi := by
  classical
  calc
    ∑ x : G, ((realFinsetIndicator X x * w x : ℝ) : ℂ) * psi x =
        ∑ x ∈ X, (c : ℂ) * psi x := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realFinsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [realFinsetIndicator, hxX]
    _ = (c : ℂ) * Chang.spectrumSum X psi := by
      rw [Chang.spectrumSum, Finset.mul_sum]

theorem mem_relativeLargeSpectrum_of_eq_const_iff
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (hc : 0 < c)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ RelativeChangSanders.relativeLargeSpectrum w (realFinsetIndicator X) eta ↔
      psi ∈ Chang.largeSpectrum X eta := by
  classical
  rw [RelativeChangSanders.mem_relativeLargeSpectrum, Chang.mem_largeSpectrum]
  rw [sum_realFinsetIndicator_mul_eq_const_mul_card hXB hw]
  rw [sum_realFinsetIndicator_mul_character_eq_const_mul hXB hw]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  constructor
  · intro h
    have hh : c * (eta * (X.card : ℝ)) ≤
        c * ‖Chang.spectrumSum X psi‖ := by
      calc
        c * (eta * (X.card : ℝ)) = eta * (c * (X.card : ℝ)) := by ring
        _ ≤ c * ‖Chang.spectrumSum X psi‖ := h
    nlinarith
  · intro h
    calc
      eta * (c * (X.card : ℝ)) = c * (eta * (X.card : ℝ)) := by ring
      _ ≤ c * ‖Chang.spectrumSum X psi‖ :=
        mul_le_mul_of_nonneg_left h hc.le

end RelativeSpectrumBridge
end Erdos3

end

section

noncomputable section

open _root_.Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem card_weightedDissociated_realFinsetIndicator_le
    (B X : Finset G) (hXB : X ⊆ B) (hX : X.Nonempty)
    (w : G → ℝ) (c R eta : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∈ B, w x = c)
    (hc : 0 < c) (hR : (c * X.card)⁻¹ ≤ R)
    (heta : 0 < eta) (Delta : Finset (AddChar G ℂ))
    (hDelta : IsWeightedDissociated w 1 Delta)
    (hsub : Delta ⊆ Chang.largeSpectrum X eta) :
    (Delta.card : ℝ) ≤ 2 * (1 + log R) / eta ^ 2 := by
  classical
  have hmass_eq :
      ∑ x : G, realFinsetIndicator X x * w x = c * X.card :=
    RelativeSpectrumBridge.sum_realFinsetIndicator_mul_eq_const_mul_card hXB hw
  have hmass : 0 < ∑ x : G, realFinsetIndicator X x * w x := by
    rw [hmass_eq]
    have hXcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    positivity
  have hsub' : Delta ⊆
      relativeLargeSpectrum w (realFinsetIndicator X) eta := by
    intro psi hpsi
    exact (RelativeSpectrumBridge.mem_relativeLargeSpectrum_of_eq_const_iff
      hXB hw hc eta psi).2 (hsub hpsi)
  have hdim := card_weightedDissociated_relativeLargeSpectrum_le
    w (realFinsetIndicator X) 1 eta Delta hw0
    (by intro x; unfold realFinsetIndicator; split <;> norm_num)
    (by intro x; unfold realFinsetIndicator; split <;> norm_num)
    heta hDelta hsub' hmass
  have hmassInv :
      ((∑ x : G, realFinsetIndicator X x * w x)⁻¹) ≤ R := by
    simpa [hmass_eq] using hR
  have hlog :
      log ((∑ x : G, realFinsetIndicator X x * w x)⁻¹) ≤ log R :=
    Real.log_le_log (inv_pos.mpr hmass) hmassInv
  calc
    (Delta.card : ℝ) ≤
        2 * (1 + log ((∑ x : G, realFinsetIndicator X x * w x)⁻¹)) /
          eta ^ 2 := by simpa using hdim
    _ ≤ 2 * (1 + log R) / eta ^ 2 := by
      gcongr

end Erdos3.RelativeChangSanders

end

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
namespace OAI

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

namespace Set

lemma rank_meet_le (B C : Set N) : (B.meet C).rank ≤ B.rank + C.rank := by
  exact Finset.card_union_le _ _

lemma neg_mem_iff (B : Set N) (x : ZMod N) : -x ∈ B ↔ x ∈ B := by
  rw [mem_iff, mem_iff]
  have hnorm (z : ℂ) : ‖1 - (starRingEnd ℂ) z‖ = ‖1 - z‖ := by
    simpa using (RCLike.norm_conj (1 - z))
  constructor
  · intro h r hr
    have hr' := h r hr
    rw [AddChar.map_neg_eq_conj, hnorm] at hr'
    exact hr'
  · intro h r hr
    rw [AddChar.map_neg_eq_conj, hnorm]
    exact h r hr

lemma add_mem_of_mem {B₁ B₂ B₃ : Set N}
    (hfreq₁ : B₃.frequencies ⊆ B₁.frequencies)
    (hfreq₂ : B₃.frequencies ⊆ B₂.frequencies)
    (hradius : B₁.radius + B₂.radius ≤ B₃.radius)
    {x y : ZMod N} (hx : x ∈ B₁) (hy : y ∈ B₂) : x + y ∈ B₃ := by
  rw [mem_iff] at hx hy ⊢
  intro r hr
  calc
    ‖1 - character r (x + y)‖ =
        ‖1 - character r x * character r y‖ := by rw [character_add]
    _ ≤ ‖1 - character r x‖ + ‖1 - character r y‖ :=
      norm_one_sub_mul_of_norm_le_one (by rw [norm_character])
    _ ≤ B₁.radius + B₂.radius := add_le_add (hx r (hfreq₁ hr)) (hy r (hfreq₂ hr))
    _ ≤ B₃.radius := hradius

lemma add_mem_dilate {B : Set N} {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    {x y : ZMod N} (hx : x ∈ B.dilate ρ) (hy : y ∈ B.dilate σ) :
    x + y ∈ B.dilate (ρ + σ) := by
  apply add_mem_of_mem (B₁ := B.dilate ρ) (B₂ := B.dilate σ)
      (B₃ := B.dilate (ρ + σ))
  · simp
  · simp
  · simp [abs_of_nonneg hρ, abs_of_nonneg hσ, abs_of_nonneg (add_nonneg hρ hσ), add_mul]
  · exact hx
  · exact hy

lemma sub_mem_dilate {B : Set N} {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    {x y : ZMod N} (hx : x ∈ B.dilate ρ) (hy : y ∈ B.dilate σ) :
    x - y ∈ B.dilate (ρ + σ) := by
  rw [sub_eq_add_neg]
  apply add_mem_dilate hρ hσ hx
  exact (B.dilate σ).neg_mem_iff y |>.2 hy

lemma carrier_mono {B₁ B₂ : Set N} (hfreq : B₂.frequencies ⊆ B₁.frequencies)
    (hradius : B₁.radius ≤ B₂.radius) : B₁.carrier ⊆ B₂.carrier := by
  intro x hx
  rw [mem_carrier] at hx ⊢
  intro r hr
  exact (hx r (hfreq hr)).trans hradius

lemma carrier_meet_subset_left (B C : Set N) : (B.meet C).carrier ⊆ B.carrier := by
  apply carrier_mono
  · exact Finset.subset_union_left
  · exact min_le_left _ _

lemma carrier_meet_subset_right (B C : Set N) : (B.meet C).carrier ⊆ C.carrier := by
  apply carrier_mono
  · exact Finset.subset_union_right
  · exact min_le_right _ _

lemma dilate_mono (B : Set N) {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρσ : ρ ≤ σ) :
    (B.dilate ρ).carrier ⊆ (B.dilate σ).carrier := by
  apply carrier_mono
  · simp
  · have hσ : 0 ≤ σ := hρ.trans hρσ
    simp only [radius_dilate, ge_iff_le]
    rw [abs_of_nonneg hρ, abs_of_nonneg hσ]
    exact mul_le_mul_of_nonneg_right hρσ B.radius_nonneg

end Set
end CyclicBohr
end Erdos3

end

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

lemma norm_one_sub_character_sub (r x y : ZMod N) :
    ‖1 - character r (x - y)‖ = ‖character r x - character r y‖ := by
  have hy : character r y ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_character]; norm_num)
  rw [AddChar.map_sub_eq_div, one_sub_div hy, norm_div, norm_character]
  simp [norm_sub_rev]

end CyclicBohr
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

theorem character_eq_one_iff (x : Circle) : character x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa [character] using h
  · rintro rfl
    exact character_zero

end
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped Real NNReal

theorem character_coe_exp (r : ℝ) :
    character (r : Circle) = Complex.exp (Complex.I * (2 * Real.pi * r : ℝ)) := by
  unfold character
  rw [AddCircle.toCircle, Function.Periodic.lift_coe, _root_.Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem norm_character_sub_one_le (x : Circle) :
    ‖character x - 1‖ ≤ 2 * Real.pi * ‖x‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  let y : ℝ := r - round r
  have hry : (r : Circle) = (y : Circle) := by simp [y, sub_eq_add_neg]
  change ‖character (r : Circle) - 1‖ ≤ 2 * Real.pi * integerDistance (r : Circle)
  rw [integerDistance_coe]
  change ‖character (r : Circle) - 1‖ ≤ 2 * Real.pi * |y|
  rw [hry, character_coe_exp, Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : (2 * Real.pi * y) / 2 = Real.pi * y := by ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * |Real.pi * y| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

theorem character_lipschitz : LipschitzWith characterLipConstant character := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy : character (x - y) * character y = character x := by
    rw [← character_add, sub_add_cancel]
  have heq : (character (x - y) - 1) * character y = character x - character y := by
    rw [sub_mul, one_mul, hxy]
  have hnorm : ‖character x - character y‖ = ‖character (x - y) - 1‖ := by
    rw [← heq, norm_mul, norm_character, mul_one]
  rw [dist_eq_norm, hnorm, dist_eq_norm]
  exact norm_character_sub_one_le (x - y)

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CyclicAffineCharacterPhase
namespace OAI

section

namespace Erdos3.CircleFourier

theorem exists_real_character_phase {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ r : ℝ, character (r : Circle) = z := by
  let c : _root_.Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨t, ht⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  rw [AddCircle.homeomorphCircle_apply] at ht
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact ⟨r, congrArg (fun c : _root_.Circle => (c : ℂ)) ht⟩

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped BigOperators

theorem CircleFourier.character_affine_integer_combination
    {I : Type*} [Fintype I] (a t : ℝ) (b : I → ℝ) (x : I → ℤ) :
    character ((t * (a + ∑ i, (x i : ℝ) * b i) : ℝ) : Circle) =
      character ((t * a : ℝ) : Circle) *
        ∏ i, character ((t * b i : ℝ) : Circle) ^ (x i) := by
  classical
  have hcoe (v : I → ℝ) : ((∑ i, v i : ℝ) : Circle) = ∑ i, (v i : Circle) :=
    map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) v Finset.univ
  rw [mul_add, Finset.mul_sum, AddCircle.coe_add, character_add, hcoe, character_fintype_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← character_zsmul, ← AddCircle.coe_zsmul]
  congr 1
  congr 1
  simp only [zsmul_eq_mul]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrTorusApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def torusChordCutoff (a : ℝ) (h : ℝ≥0) (v : ι → CircleFourier.Circle) : ℝ :=
  chordBoxCutoff a h (fun i => CircleFourier.character (v i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TranslatedBohrDifference
namespace OAI

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem massCoeff_realUniformMass (A : Finset G) (ψ : AddChar G ℂ) :
    massCoeff (realUniformMass A) ψ =
      ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
  calc
    massCoeff (realUniformMass A) ψ =
        ∑ x ∈ A, ((A.card : ℝ)⁻¹ : ℂ) * ψ x := by
      rw [massCoeff, ← Finset.sum_subset (s₁ := A) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realUniformMass, hx]
      · simp
      · intro x hxU hxA
        simp [realUniformMass, hxA]
    _ = ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
      rw [Chang.spectrumSum, Finset.mul_sum]

omit [DecidableEq G] in

theorem massCoeff_massConvolution (f g : G → ℝ) (ψ : AddChar G ℂ) :
    massCoeff (massConvolution f g) ψ = massCoeff f ψ * massCoeff g ψ := by
  unfold massCoeff massConvolution
  push_cast
  calc
    ∑ x : G, (∑ y : G, (f y : ℂ) * (g (x - y) : ℂ)) * ψ x =
        ∑ x : G, ∑ y : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ∑ y : G, ∑ x : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x :=
      Finset.sum_comm
    _ =
        ∑ y : G, ((f y : ℂ) * ψ y) *
          ∑ z : G, (g z : ℂ) * ψ z := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun z ↦ ?_
      have hψ : ψ z = ψ y * ψ (z - y) := by
        calc
          ψ z = ψ (y + (z - y)) := congrArg ψ (by simp)
          _ = ψ y * ψ (z - y) := AddChar.map_add_eq_mul ψ y (z - y)
      simp only [Equiv.subRight_apply]
      rw [hψ]
      ring
    _ = (∑ y : G, (f y : ℂ) * ψ y) *
        ∑ z : G, (g z : ℂ) * ψ z := by
      simpa using
        (Finset.sum_mul (univ : Finset G) (fun y ↦ (f y : ℂ) * ψ y)
          (∑ z : G, (g z : ℂ) * ψ z)).symm

theorem massCoeff_convolutionPower (f : G → ℝ) (ψ : AddChar G ℂ) :
    ∀ n, massCoeff (convolutionPower f n) ψ = massCoeff f ψ ^ n := by
  intro n
  induction n with
  | zero =>
      unfold massCoeff
      rw [Fintype.sum_eq_single 0]
      · simp [realUniformMass]
      · intro y hy
        simp [realUniformMass, hy]
  | succ n ihn =>
      rw [convolutionPower_succ, massCoeff_massConvolution, ihn, pow_succ]

end

end Erdos3

end

section

open AddChar _root_.Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma normalizedSpectrum_eq (A : Finset G) (psi : AddChar G ℂ) :
    (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
      ((A.card : ℂ)⁻¹) * Chang.spectrumSum A psi := by
  classical
  rw [Chang.spectrumSum, Finset.mul_sum]
  calc
    (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
        ∑ x : G, if x ∈ A then ((A.card : ℂ)⁻¹) * psi x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [realUniformMass, hx]
    _ = ∑ x ∈ A, ((A.card : ℂ)⁻¹) * psi x := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter fun x : G ↦ x ∈ A) = A := by
        ext x
        simp
      rw [hfilter]

end

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicRelativeChang
namespace OAI

section

noncomputable section

open _root_.Finset Real
open scoped BigOperators ComplexConjugate

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem zero_mem_chang_largeSpectrum_half (A : Finset G) :
    (0 : AddChar G ℂ) ∈ Erdos3.Chang.largeSpectrum A (1 / 2 : ℝ) := by
  rw [Erdos3.Chang.mem_largeSpectrum]
  simp [Erdos3.Chang.spectrumSum]
  have hcard : (0 : ℝ) ≤ A.card := by exact_mod_cast Nat.zero_le A.card
  nlinarith

theorem neg_mem_chang_largeSpectrum {A : Finset G} {eta : ℝ}
    {psi : AddChar G ℂ}
    (hpsi : psi ∈ Erdos3.Chang.largeSpectrum A eta) :
    -psi ∈ Erdos3.Chang.largeSpectrum A eta := by
  rw [Erdos3.Chang.mem_largeSpectrum] at hpsi ⊢
  have hsum : Erdos3.Chang.spectrumSum A (-psi) =
      conj (Erdos3.Chang.spectrumSum A psi) := by
    unfold Erdos3.Chang.spectrumSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [AddChar.neg_apply, AddChar.map_neg_eq_conj]
  rw [hsum, RCLike.norm_conj]
  exact hpsi

end Erdos3.RelativeChangSanders

end

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteSamplingMoment
namespace OAI

section

namespace Erdos3.CyclicMZ

open _root_.Finset Fintype Nat

variable {ι : Type*} {A : Finset ι} {m n : ℕ}

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

namespace Real

attribute [-instance] decidableForallFin

theorem marcinkiewicz_zygmund' (m : ℕ) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  obtain rfl | hm := m.eq_zero_or_pos
  · simp
  have hm' : 1 ≤ m := by rwa [Nat.succ_le_iff]
  obtain rfl | hA := A.eq_empty_or_nonempty
  · cases n <;> cases m <;> simp
  let B := A ^^ n
  calc
    ∑ a ∈ B, (∑ i, f (a i)) ^ (2 * m) ≤
        ∑ a ∈ A ^^ n,
          (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (2 * m)) / #A ^ n := by
      gcongr
      simpa [pow_mul, sq_abs] using step_one' hA f hf (2 * m) _
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
        ∑ k ∈ piAntidiag univ (2 * m) with ∀ i, 2 ∣ k i,
          multinomial univ (fun i ↦ k i) * ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [← sum_div]
      simp_rw [pow_abs_two_mul]
      rw [step_two, step_three, mul_comm, inv_pow, ← div_eq_mul_inv, div_div]
      simp only [step_four, mul_ite, mul_zero, mul_one, ← sum_filter, ← sum_mul,
        even_iff_two_dvd]
      rw [mul_comm, mul_div_mul_left]
      positivity
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
        ∑ k ∈ (piAntidiag univ m).map
          ⟨(2 • ·), fun _ _ h ↦ funext fun i ↦
            mul_right_injective₀ two_ne_zero (congr_fun h i)⟩,
          multinomial univ (fun i ↦ k i) * ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [map_nsmul_piAntidiag_univ m (ι := Fin n) (n := 2) two_ne_zero]
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
        multinomial univ (fun i ↦ 2 * k i) *
          ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n := by
      simp
    _ ≤ _ := end_step hm' hA

theorem marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * m) := by
  obtain _ | m := m
  · simp at hm
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  calc
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * (m + 1)) ≤
        (4 * ↑(m + 1)) ^ (m + 1) *
          ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ (m + 1) :=
      marcinkiewicz_zygmund' _ f hf
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) *
        (∑ a ∈ A ^^ n, n ^ m * ∑ i, f (a i) ^ (2 * (m + 1))) := by
      gcongr with a
      rw [← div_le_iff₀' (by positivity)]
      simpa only [Finset.card_fin, pow_mul] using
        pow_sum_div_card_le_sum_pow (f := fun i ↦ f (a i) ^ 2)
          (s := univ) (fun i _ ↦ by positivity) m
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * n ^ m *
        ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * (m + 1)) := by
      simp_rw [mul_assoc, mul_sum]
      rfl

end Real

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

theorem marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → 𝕜)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (8 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ A ^^ n, ∑ i, ‖f (a i)‖ ^ (2 * m) := by
  let f₁ x : ℝ := _root_.RCLike.re (f x)
  let f₂ x : ℝ := _root_.RCLike.im (f x)
  let B := A ^^ n
  have hf₁ i : ∑ a ∈ B, f₁ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have hf₂ i : ∑ a ∈ B, f₂ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have h₁ := Real.marcinkiewicz_zygmund hm _ hf₁
  have h₂ := Real.marcinkiewicz_zygmund hm _ hf₂
  dsimp [f₁, f₂] at h₁ h₂
  simp only [pow_mul, RCLike.norm_sq_eq_def, ← sq, map_sum, map_sum]
  calc
    ∑ a ∈ B, ((∑ i, _root_.RCLike.re (f (a i))) ^ 2 +
        (∑ i, _root_.RCLike.im (f (a i))) ^ 2) ^ m ≤
        ∑ a ∈ B, 2 ^ (m - 1) *
          (((∑ i, _root_.RCLike.re (f (a i))) ^ 2) ^ m +
            ((∑ i, _root_.RCLike.im (f (a i))) ^ 2) ^ m) := by
      gcongr with a
      apply add_pow_le <;> positivity
    _ = 2 ^ (m - 1) *
        (∑ a ∈ B, (∑ i, _root_.RCLike.re (f (a i))) ^ (2 * m) +
          ∑ a ∈ B, (∑ i, _root_.RCLike.im (f (a i))) ^ (2 * m)) := by
      simp only [← sum_add_distrib, mul_sum, pow_mul]
    _ ≤ 2 ^ (m - 1) *
        ((4 * m) ^ m * n ^ (m - 1) *
            ∑ a ∈ B, ∑ i, _root_.RCLike.re (f (a i)) ^ (2 * m) +
          (4 * m) ^ m * n ^ (m - 1) *
            ∑ a ∈ B, ∑ i, _root_.RCLike.im (f (a i)) ^ (2 * m)) := by
      gcongr
    _ = 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ B, ∑ i,
          (_root_.RCLike.re (f (a i)) ^ (2 * m) +
            _root_.RCLike.im (f (a i)) ^ (2 * m))) := by
      simp_rw [sum_add_distrib, mul_add]
    _ ≤ 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ B, ∑ i,
          2 * (_root_.RCLike.re (f (a i)) ^ 2 +
            _root_.RCLike.im (f (a i)) ^ 2) ^ m) := by
      simp_rw [pow_mul]
      gcongr
      apply pow_add_pow_le' <;> positivity
    _ = (8 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ B, ∑ i,
          (_root_.RCLike.re (f (a i)) ^ 2 +
            _root_.RCLike.im (f (a i)) ^ 2) ^ m := by
      simp_rw [← mul_sum, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow,
        ← pow_sub_one_mul hm (2 : ℝ)]
      ring

end RCLike

end Erdos3.CyclicMZ

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalShiftFiber
namespace OAI

section

namespace Erdos3

open _root_.Finset Fintype
open scoped BigOperators Pointwise

namespace CyclicCrootSisask

variable {N k m : ℕ} [NeZero N]

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

omit [NeZero N] in

theorem pointwise_sampleDeviation_moment
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    (hm : m ≠ 0) (x : ZMod N) :
    ∑ a ∈ A ^^ k, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
  let g : ZMod N → ℝ := centeredTranslate A f x
  have hg : ∀ i, ∑ a ∈ A ^^ k, g (a i) = 0 := by
    intro i
    rw [Fintype.sum_piFinset_apply]
    rw [show ∑ b ∈ A, g b = 0 by
      simpa [g] using sum_centeredTranslate_eq_zero hA f x]
    simp
  have h := Erdos3.CyclicMZ.RCLike.marcinkiewicz_zygmund
    (A := A) (n := k) hm g hg
  simpa only [Real.norm_eq_abs, sampleDeviation, g] using h

theorem global_sampleDeviation_moment
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    (hm : m ≠ 0) :
    ∑ a ∈ A ^^ k, ∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ x : ZMod N, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
  rw [Finset.sum_comm]
  calc
    ∑ x : ZMod N, ∑ a ∈ A ^^ k, |sampleDeviation A f a x| ^ (2 * m) ≤
        ∑ x : ZMod N, (8 * m) ^ m * k ^ (m - 1) *
          ∑ a ∈ A ^^ k, ∑ i,
            |centeredTranslate A f x (a i)| ^ (2 * m) := by
      exact Finset.sum_le_sum fun x _ ↦ pointwise_sampleDeviation_moment hA f hm x
    _ = (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ x : ZMod N, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

end CyclicCrootSisask
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CyclicSamplingMoments
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {N k m : ℕ} [NeZero N]

theorem sum_setAverageTranslate_pow_le {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (n : ℕ) :
    ∑ x, |setAverageTranslate A f x| ^ n ≤ ∑ x, |f x| ^ n := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  cases n with
  | zero => simp
  | succ n =>
    have hpoint (x : ZMod N) : |setAverageTranslate A f x| ^ (n + 1) ≤
        (∑ a ∈ A, |f (x - a)| ^ (n + 1)) / A.card := by
      have habs : |setAverageTranslate A f x| ≤ (∑ a ∈ A, |f (x - a)|) / A.card := by
        rw [setAverageTranslate, abs_div, abs_of_pos hc]
        exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
      have hj := pow_sum_div_card_le_sum_pow (s := A)
        (fun a _ => abs_nonneg (f (x - a))) n
      calc
        _ ≤ ((∑ a ∈ A, |f (x - a)|) / A.card) ^ (n + 1) :=
          pow_le_pow_left₀ (abs_nonneg _) habs _
        _ = (∑ a ∈ A, |f (x - a)|) ^ (n + 1) / (A.card : ℝ) ^ n / A.card := by
          rw [div_pow, pow_succ (A.card : ℝ) n, div_mul_eq_div_div]
        _ ≤ _ := div_le_div_of_nonneg_right hj hc.le
    calc
      _ ≤ ∑ x, (∑ a ∈ A, |f (x - a)| ^ (n + 1)) / A.card :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ = (∑ a ∈ A, ∑ x, |f (x - a)| ^ (n + 1)) / A.card := by
        rw [← Finset.sum_div, Finset.sum_comm]
      _ = (∑ _a ∈ A, ∑ x, |f x| ^ (n + 1)) / A.card := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
      _ = _ := by simp [hc.ne']

theorem sum_centeredTranslate_pow_le {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (a : ZMod N) (hm : m ≠ 0) :
    ∑ x, |centeredTranslate A f x a| ^ (2 * m) ≤
      2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  have hpoint (x : ZMod N) : |centeredTranslate A f x a| ^ (2 * m) ≤
      2 ^ (2 * m - 1) * (|f (x - a)| ^ (2 * m) + |setAverageTranslate A f x| ^ (2 * m)) := by
    apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) _).trans
    exact add_pow_le (abs_nonneg _) (abs_nonneg _) _
  have hshift : (∑ x, |f (x - a)| ^ (2 * m)) = ∑ x, |f x| ^ (2 * m) :=
    Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
  calc
    _ ≤ ∑ x, 2 ^ (2 * m - 1) *
        (|f (x - a)| ^ (2 * m) + |setAverageTranslate A f x| ^ (2 * m)) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = 2 ^ (2 * m - 1) * ((∑ x, |f x| ^ (2 * m)) +
        ∑ x, |setAverageTranslate A f x| ^ (2 * m)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hshift]
    _ ≤ 2 ^ (2 * m - 1) * ((∑ x, |f x| ^ (2 * m)) + ∑ x, |f x| ^ (2 * m)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (sum_setAverageTranslate_pow_le hA f _)) (by positivity)
    _ = _ := by
      rw [← pow_sub_one_mul (show 2 * m ≠ 0 by omega) (2 : ℝ)]
      ring

theorem global_sampleDeviation_input_moment {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (hm : m ≠ 0) :
    ∑ a ∈ A ^^ k, ∑ x, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) * (A.card : ℝ) ^ k * k *
        (2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
  apply (global_sampleDeviation_moment (k := k) hA f hm).trans
  have hsum (a : Fin k → ZMod N) :
      ∑ x, ∑ i, |centeredTranslate A f x (a i)| ^ (2 * m) ≤
        k * (2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i : Fin k, 2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m) :=
        Finset.sum_le_sum (fun i _ => sum_centeredTranslate_pow_le hA f (a i) hm)
      _ = _ := by simp
  calc
    _ ≤ (8 * m) ^ m * k ^ (m - 1) *
        ∑ _a ∈ A ^^ k, k * (2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum (fun a _ => hsum a)
      · positivity
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset_const, Nat.cast_pow]
      ring

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalBoostedAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

theorem sum_realSetIndicator_moment (M : Finset (ZMod N)) {n : ℕ} (hn : n ≠ 0) :
    (∑ x, |realSetIndicator M x| ^ n) = (M.card : ℝ) := by
  have hp (x : ZMod N) : |realSetIndicator M x| ^ n = if x ∈ M then 1 else 0 := by
    by_cases hx : x ∈ M <;> simp [realSetIndicator, hx, hn]
  simp only [hp]
  simp

theorem triple_period_moment_bound {L : Finset (ZMod N)} (hL : L.Nonempty)
    (A M : Finset (ZMod N)) (t x : ZMod N) {n : ℕ} (hn : n ≠ 0) {epsilon : ℝ}
    (hperiod : ∑ y,
      |setAverageTranslate A (realSetIndicator M) (y + t) -
        setAverageTranslate A (realSetIndicator M) y| ^ n ≤
          epsilon ^ n * ∑ y, |realSetIndicator M y| ^ n) :
    |setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) (x + t) -
      setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x| ^ n ≤
        epsilon ^ n * ((M.card : ℝ) / L.card) := by
  have h := convolution_period_moment_bound hL
    (setAverageTranslate A (realSetIndicator M)) t x n hperiod
  simpa only [sum_realSetIndicator_moment M hn, mul_div_assoc] using h

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {N k m : ℕ} [NeZero N]

theorem half_samples_good_input_moment {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (hm : m ≠ 0) :
    (A.card : ℝ) ^ k / 2 ≤
      (goodSamples A f k m (samplingMomentCost m k * ∑ x, |f x| ^ (2 * m))).card := by
  let C := samplingMomentCost m k * ∑ x, |f x| ^ (2 * m)
  have hC : 0 ≤ C := mul_nonneg (samplingMomentCost_nonneg _ _)
    (Finset.sum_nonneg (fun _ _ => by positivity))
  have htotal : ∑ a ∈ A ^^ k, ∑ x, |sampleDeviation A f a x| ^ (2 * m) ≤
      (1 / 2 : ℝ) * C * (A ^^ k).card := by
    apply (global_sampleDeviation_input_moment (k := k) hA f hm).trans_eq
    simp only [C, samplingMomentCost, Fintype.card_piFinset_const, Nat.cast_pow]
    ring
  have h := half_card_le_filter_of_sum_le (A ^^ k)
    (fun a => ∑ x, |sampleDeviation A f a x| ^ (2 * m)) hC
    (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) htotal
  simpa only [goodSamples, C, Fintype.card_piFinset_const, Nat.cast_pow] using h

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

variable {N : ℕ}

theorem setAverageTranslate_approx_of_shifts {A : Finset (ZMod N)} (hA : A.Nonempty)
    (u : ZMod N → ℝ) {delta : ℝ}
    (hshift : ∀ t ∈ A, ∀ x, |u (x + t) - u x| ≤ delta) (x : ZMod N) :
    |setAverageTranslate A u x - u x| ≤ delta := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have heq : setAverageTranslate A u x - u x =
      (∑ t ∈ A, (u (x - t) - u x)) / A.card := by
    rw [setAverageTranslate, Finset.sum_sub_distrib, sub_div]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hpoint (t : ZMod N) (ht : t ∈ A) : |u (x - t) - u x| ≤ delta := by
    have h := hshift t ht (x - t)
    simpa only [sub_add_cancel, abs_sub_comm] using h
  rw [heq, abs_div, abs_of_pos hc]
  calc
    _ ≤ (∑ t ∈ A, |u (x - t) - u x|) / A.card :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
    _ ≤ (∑ _t ∈ A, delta) / A.card :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) hc.le
    _ = delta := by simp [hc.ne']

theorem iteratedSetAverage_uniform_error {A : Finset (ZMod N)} (hA : A.Nonempty)
    (u : ZMod N → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hstep : ∀ x, |setAverageTranslate A u x - u x| ≤ delta) (n : ℕ) :
    ∀ x, |iteratedSetAverage A u n x - u x| ≤ n * delta := by
  induction n with
  | zero => intro x; simp [iteratedSetAverage]
  | succ n ih =>
    intro x
    change |setAverageTranslate A (iteratedSetAverage A u n) x - u x| ≤ _
    have herror : |setAverageTranslate A (iteratedSetAverage A u n) x - setAverageTranslate A u x| ≤
        n * delta := by
      rw [← setAverageTranslate_sub]
      exact abs_setAverageTranslate_le hA (fun y => iteratedSetAverage A u n y - u y)
        (mul_nonneg (Nat.cast_nonneg _) hdelta) ih x
    calc
      _ = |(setAverageTranslate A (iteratedSetAverage A u n) x - setAverageTranslate A u x) +
          (setAverageTranslate A u x - u x)| := by congr 1; ring
      _ ≤ |setAverageTranslate A (iteratedSetAverage A u n) x - setAverageTranslate A u x| +
          |setAverageTranslate A u x - u x| := abs_add_le _ _
      _ ≤ n * delta + delta := add_le_add herror (hstep x)
      _ = _ := by push_cast; ring

theorem iteratedSetAverage_approx_of_shifts {A : Finset (ZMod N)} (hA : A.Nonempty)
    (u : ZMod N → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hshift : ∀ t ∈ A, ∀ x, |u (x + t) - u x| ≤ delta) (n : ℕ) (x : ZMod N) :
    |iteratedSetAverage A u n x - u x| ≤ n * delta :=
  iteratedSetAverage_uniform_error hA u hdelta (setAverageTranslate_approx_of_shifts hA u hshift) n x

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators Pointwise

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {N : ℕ} [NeZero N]

theorem exists_local_almostPeriods {A S : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (f : ZMod N → ℝ)
    {m : ℕ} (hm : 0 < m) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let k := crootSisaskSampleSize m epsilon
    ∃ T : Finset (ZMod N), T ⊆ S ∧ T.Nonempty ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      ∀ s ∈ T, ∀ t ∈ T,
        ∑ x, |setAverageTranslate A f (x + (t - s)) - setAverageTranslate A f x| ^ (2 * m) ≤
          epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  classical
  intro k
  let C := samplingMomentCost m k * ∑ x, |f x| ^ (2 * m)
  let L := goodSamples A f k m C
  have hhalf : (A.card : ℝ) ^ k / 2 ≤ L.card := half_samples_good_input_moment hA f hm.ne'
  have hLpos : (0 : ℝ) < L.card :=
    (div_pos (pow_pos (by exact_mod_cast hA.card_pos) _) (by norm_num)).trans_le hhalf
  have hL : L.Nonempty := Finset.card_pos.mp (by exact_mod_cast hLpos)
  have hLA : L ⊆ A ^^ k := Finset.filter_subset _ _
  obtain ⟨x, T, hTS, hT, hcount, hgood⟩ := exists_local_shift_fiber hA hS L hL hLA
  refine ⟨T, hTS, hT, ?_, ?_⟩
  · apply le_trans _ hcount
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)) (by positivity)
  · intro s hs t ht
    have hbase : (x - fun _ => s) ∈ goodSamples A f k m C := hgood s hs
    have hshift : ((x - fun _ => s) - fun _ => t - s) ∈ goodSamples A f k m C := by
      have heq : ((x - fun _ => s) - fun _ => t - s) = x - fun _ => t := by
        funext i
        simp only [Pi.sub_apply]
        abel
      rw [heq]
      exact hgood t ht
    exact goodSamples_relative_moment_bound hm (crootSisaskSampleSize_pos hm hepsilon)
      (crootSisaskSampleSize_bound m hepsilon) hbase hshift

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_local_triple_almostPeriods {A S L : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (M : Finset (ZMod N)) {delta : ℝ} (hdelta : 0 < delta) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m (delta / Real.exp 1)
    ∃ T : Finset (ZMod N), T ⊆ S ∧ T.Nonempty ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      ∀ s ∈ T, ∀ t ∈ T, ∀ x : ZMod N,
        |setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) (x + (t - s)) -
          setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x| ≤ delta := by
  intro m k
  obtain ⟨T, hTS, hT, hcount, hperiod⟩ := exists_local_almostPeriods hA hS (realSetIndicator M)
    (convolutionMomentOrder_pos M L) (div_pos hdelta (Real.exp_pos _))
  refine ⟨T, hTS, hT, hcount, ?_⟩
  intro s hs t ht x
  apply convolution_moment_to_pointwise M L hdelta
  exact triple_period_moment_bound hL A M (t - s) x
    (show 2 * m ≠ 0 by have := convolutionMomentOrder_pos M L; dsimp only [m]; omega)
    (hperiod s hs t ht)

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_local_boosted_triple_almostPeriods {A S L : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (M : Finset (ZMod N)) (q : ℕ) (hq : 0 < q) {delta : ℝ} (hdelta : 0 < delta) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m ((delta / q) / Real.exp 1)
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ (T X : Finset (ZMod N)) (z : ZMod N), T ⊆ S ∧ z ∈ T ∧
      X = T.map (Equiv.subRight z).toEmbedding ∧ 0 ∈ X ∧ X ⊆ S - S ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      ∀ x, |iteratedSetAverage X u q x - u x| ≤ delta := by
  intro m k u
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdeltaq : 0 < delta / (q : ℝ) := div_pos hdelta hqR
  obtain ⟨T, hTS, hT, hcount, hperiod⟩ := exists_local_triple_almostPeriods hA hS hL M hdeltaq
  obtain ⟨z, hz⟩ := hT
  let X := T.map (Equiv.subRight z).toEmbedding
  have hzero : (0 : ZMod N) ∈ X := by
    apply Finset.mem_map.mpr
    exact ⟨z, hz, sub_self z⟩
  have hXS : X ⊆ S - S := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ht
    exact Finset.sub_mem_sub (hTS ha) (hTS hz)
  refine ⟨T, X, z, hTS, hz, rfl, hzero, hXS, hcount, ?_⟩
  have hshift : ∀ t ∈ X, ∀ x, |u (x + t) - u x| ≤ delta / (q : ℝ) := by
    intro t ht x
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ht
    exact hperiod z hz a ha x
  intro x
  have h := iteratedSetAverage_approx_of_shifts (show X.Nonempty from ⟨0, hzero⟩)
    u hdeltaq.le hshift q x
  have hcancel : (q : ℝ) * (delta / q) = delta := by field_simp
  exact h.trans_eq hcancel

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LocalBohrAlmostPeriodsRelative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem finiteFourierCoeff_finiteIndicator (A : Finset G) (psi : AddChar G ℂ) :
    finiteFourierCoeff (finiteIndicator A) psi =
      (∑ a ∈ A, star (psi a)) / (Fintype.card G : ℂ) := by
  simp [finiteFourierCoeff, Fintype.expect_eq_sum_div_card, finiteIndicator, ite_mul]

theorem finiteFourierCoeff_averagingKernel {A : Finset G} (hA : A.Nonempty)
    (psi : AddChar G ℂ) :
    finiteFourierCoeff (averagingKernel A) psi = setFourierMultiplier A psi := by
  have hN : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (A.card : ℂ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have heq : finiteFourierCoeff (averagingKernel A) psi =
      ((Fintype.card G : ℂ) / A.card) * finiteFourierCoeff (finiteIndicator A) psi := by
    unfold finiteFourierCoeff averagingKernel
    simp only [mul_assoc, Finset.mul_expect]
  rw [heq, finiteFourierCoeff_finiteIndicator, setFourierMultiplier,
    Finset.expect_eq_sum_div_card]
  field_simp

theorem sum_sq_setFourierMultiplier {A : Finset G} (hA : A.Nonempty) :
    (∑ psi : AddChar G ℂ, ‖setFourierMultiplier A psi‖ ^ 2) =
      (Fintype.card G : ℝ) / A.card := by
  simp_rw [← finiteFourierCoeff_averagingKernel hA]
  rw [finiteFourier_parseval, mean_averagingKernel_norm_sq hA]

theorem fourierL1_triple_average_sq_le {A L : Finset G}
    (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset G) :
    fourierL1 (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) ^ 2 ≤
      (M.card : ℝ) / L.card := by
  let s : ℝ := ∑ psi : AddChar G ℂ,
    ‖setFourierMultiplier L psi‖ * ‖finiteFourierCoeff (finiteIndicator M) psi‖
  have hbound : fourierL1 (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) ≤ s := by
    unfold fourierL1
    apply Finset.sum_le_sum
    intro psi _
    rw [finiteFourierCoeff_finiteSetAverage, finiteFourierCoeff_finiteSetAverage]
    simp only [norm_mul]
    have hAone := norm_setFourierMultiplier_le_one hA psi
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) hAone) (norm_nonneg _)
  have hnonneg : 0 ≤ fourierL1
      (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hCS : s ^ 2 ≤
      (∑ psi : AddChar G ℂ, ‖setFourierMultiplier L psi‖ ^ 2) *
        ∑ psi : AddChar G ℂ, ‖finiteFourierCoeff (finiteIndicator M) psi‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [sum_sq_setFourierMultiplier hL, finiteFourier_parseval, mean_indicator_norm_sq] at hCS
  have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcancel : ((Fintype.card G : ℝ) / L.card) * (M.card / (Fintype.card G : ℝ)) =
      (M.card : ℝ) / L.card := by field_simp
  exact (pow_le_pow_left₀ hnonneg hbound 2).trans (hCS.trans_eq hcancel)

theorem fourierL1_triple_average_le {A L : Finset G}
    (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset G) :
    fourierL1 (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) ≤
      Real.sqrt ((M.card : ℝ) / L.card) :=
  Real.le_sqrt_of_sq_le (fourierL1_triple_average_sq_le hA hL M)

end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem finiteSetAverage_ofReal (A : Finset (ZMod N)) (u : ZMod N → ℝ) :
    finiteSetAverage A (fun x => (u x : ℂ)) = fun x => (setAverageTranslate A u x : ℂ) := by
  funext x
  rw [finiteSetAverage, Finset.expect_eq_sum_div_card, setAverageTranslate]
  push_cast
  rfl

omit [NeZero N] in
theorem iteratedFiniteSetAverage_ofReal (A : Finset (ZMod N)) (u : ZMod N → ℝ) (q : ℕ) :
    iteratedFiniteSetAverage A (fun x => (u x : ℂ)) q =
      fun x => (iteratedSetAverage A u q x : ℂ) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [iteratedFiniteSetAverage, ih, finiteSetAverage_ofReal]
      rfl

omit [NeZero N] in
theorem finiteIndicator_eq_ofReal_realSetIndicator (M : Finset (ZMod N)) :
    finiteIndicator M = fun x => (realSetIndicator M x : ℂ) := by
  funext x
  by_cases hx : x ∈ M <;> simp [finiteIndicator, realSetIndicator, hx]

omit [NeZero N] in
theorem triple_average_ofReal (A L M : Finset (ZMod N)) :
    finiteSetAverage L (finiteSetAverage A (finiteIndicator M)) =
      fun x => (setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x : ℂ) := by
  rw [finiteIndicator_eq_ofReal_realSetIndicator, finiteSetAverage_ofReal, finiteSetAverage_ofReal]

theorem triple_translate_le_of_iterated_approx
    {A L X : Finset (ZMod N)} (hA : A.Nonempty) (hL : L.Nonempty) (hX : X.Nonempty)
    (M : Finset (ZMod N)) (q : ℕ) {delta eta theta : ℝ}
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : ZMod N) :
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    (∀ y, |iteratedSetAverage X u q y - u y| ≤ delta) →
    (∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) →
    |u (x - t) - u x| ≤
      2 * delta + (theta + 2 * eta ^ q) * Real.sqrt ((M.card : ℝ) / L.card) := by
  intro u happrox hphase
  let f := finiteSetAverage L (finiteSetAverage A (finiteIndicator M))
  have hf : f = fun y => (u y : ℂ) := triple_average_ofReal A L M
  have happrox' : ∀ y, ‖iteratedFiniteSetAverage X f q y - f y‖ ≤ delta := by
    intro y
    rw [hf, iteratedFiniteSetAverage_ofReal]
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using happrox y
  have h := translate_le_of_iteratedFiniteSetAverage_approx hX q f heta htheta t x happrox' hphase
  have hreal : |u (x - t) - u x| ≤ 2 * delta + (theta + 2 * eta ^ q) * fourierL1 f := by
    simpa only [hf, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  exact hreal.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (fourierL1_triple_average_le hA hL M)
      (add_nonneg htheta (mul_nonneg (by norm_num) (pow_nonneg heta q)))))

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DifferenceEventProbability
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

noncomputable def differenceEventProbability
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N) : ℝ :=
  𝔼 a ∈ A₁, 𝔼 b ∈ A₂, realSetIndicator K (a - b + t)

theorem differenceEventProbability_eq_triple
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N) :
    differenceEventProbability A₁ A₂ K t =
      setAverageTranslate (-A₁) (setAverageTranslate A₂ (realSetIndicator K)) t := by
  rw [differenceEventProbability, setAverageTranslate_eq_expect, Finset.expect_neg_index]
  apply Finset.expect_congr rfl
  intro a _
  rw [setAverageTranslate_eq_expect]
  apply Finset.expect_congr rfl
  intro b _
  congr 1
  abel

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DifferenceEventSupport
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

theorem differenceEventProbability_self_zero (A : Finset (ZMod N)) (hA : A.Nonempty) :
    differenceEventProbability A A (A - A) 0 = 1 := by
  unfold differenceEventProbability
  have hone : ∀ a ∈ A, ∀ b ∈ A, realSetIndicator (A - A) (a - b + 0) = 1 := by
    intro a ha b hb
    simp only [add_zero, realSetIndicator, if_pos (Finset.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩)]
  calc
    (𝔼 a ∈ A, 𝔼 b ∈ A, realSetIndicator (A - A) (a - b + 0)) =
        𝔼 _a ∈ A, 𝔼 _b ∈ A, (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro a ha
      apply Finset.expect_congr rfl
      intro b hb
      exact hone a ha b hb
    _ = 1 := by rw [Finset.expect_const hA, Finset.expect_const hA]

theorem exists_difference_event_of_probability_pos
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N)
    (h : 0 < differenceEventProbability A₁ A₂ K t) :
    ∃ a ∈ A₁, ∃ b ∈ A₂, a - b + t ∈ K := by
  classical
  by_contra hnone
  push Not at hnone
  have hz : differenceEventProbability A₁ A₂ K t = 0 := by
    unfold differenceEventProbability
    calc
      (𝔼 a ∈ A₁, 𝔼 b ∈ A₂, realSetIndicator K (a - b + t)) =
          𝔼 _a ∈ A₁, 𝔼 _b ∈ A₂, (0 : ℝ) := by
        apply Finset.expect_congr rfl
        intro a ha
        apply Finset.expect_congr rfl
        intro b hb
        simp only [realSetIndicator, if_neg (hnone a ha b hb)]
      _ = 0 := by simp
  linarith

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LocalSamplingBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

variable {N : ℕ}

theorem localBoostedSampleSize_le (M L : Finset (ZMod N)) {p delta : ℝ}
    (hp : 0 ≤ p) (hratio : (M.card : ℝ) / L.card ≤ Real.exp p)
    (hdelta : 0 < delta) (q : ℕ) (hq : 0 < q) :
    (crootSisaskSampleSize (convolutionMomentOrder M L) ((delta / q) / Real.exp 1) : ℝ) ≤
      (256 * Real.exp 1 ^ 2 / delta ^ 2) * (p + 2) * (q : ℝ) ^ 2 + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < (delta / (q : ℝ)) / Real.exp 1 := by positivity
  have hm := convolutionMomentOrder_le_of_ratio M L hp hratio
  apply (crootSisaskSampleSize_le _ he).trans
  have hid : 256 * (convolutionMomentOrder M L : ℝ) / ((delta / q) / Real.exp 1) ^ 2 + 1 =
      (256 * Real.exp 1 ^ 2 / delta ^ 2) * (convolutionMomentOrder M L : ℝ) * (q : ℝ) ^ 2 + 1 := by
    field_simp
  rw [hid]
  gcongr

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.QuarticSamplingBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

theorem samplingCubicFactor_pos (epsilon : ℝ) : 0 < samplingCubicFactor epsilon := by
  unfold samplingCubicFactor
  positivity

theorem rankQuarticFactor_pos (epsilon : ℝ) : 0 < rankQuarticFactor epsilon := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hC := samplingCubicFactor_pos epsilon
  unfold rankQuarticFactor
  positivity

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped NNReal Pointwise

theorem almostPeriodicityWidthConstant_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < almostPeriodicityWidthConstant epsilon := by
  have hC := rankQuarticFactor_pos epsilon
  unfold almostPeriodicityWidthConstant
  positivity

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise NNReal

noncomputable def quarticBogolyubovConstant : ℝ :=
  3 * almostPeriodicityWidthConstant (1 / 2)

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

noncomputable def CompatibleAuxResidue.baseValue {M d : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) : ℤ := Classical.choose v.property

noncomputable def CompatibleAuxResidue.refinedValue {M d J : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (hcop : (M * d).Coprime J) (w : ℤ) : ℤ :=
  Classical.choose ((coprime_refinement_preserves_compatibility hcop u v.val.val w).mp v.property)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffinePhaseBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace CircleFourier

noncomputable def linearPhaseMean {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → ℕ) (a : ι → Circle) : ℂ :=
  𝔼 t : ∀ i, Fin (T i), character (∑ i, ((t i : ℕ) • a i))

end CircleFourier
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace CircleFourier

theorem affinePhaseMean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (c : ℂ) (a₀ : Circle) (a : ι → Circle) :
    (𝔼 t : ∀ i, Fin (T i), c * character (a₀ + ∑ i, (t i : ℕ) • a i)) =
      c * character a₀ * linearPhaseMean T a := by
  simp only [character_add, ← mul_assoc]
  rw [← Finset.mul_expect]
  rfl

theorem linearPhaseMean_norm_ge_of_affine_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (c : ℂ) (a₀ : Circle) (a : ι → Circle)
    {M δ : ℝ} (hM : 0 < M) (hc : ‖c‖ ≤ M)
    (hbias : δ ≤ ‖𝔼 t : ∀ i, Fin (T i), c * character (a₀ + ∑ i, (t i : ℕ) • a i)‖) :
    δ / M ≤ ‖linearPhaseMean T a‖ := by
  rw [affinePhaseMean_eq, norm_mul, norm_mul, norm_character, mul_one] at hbias
  apply (div_le_iff₀ hM).mpr
  exact hbias.trans ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (mul_comm _ _))

end CircleFourier
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

noncomputable def productFiberMass (w : (∀ i, X i) → ℝ) (S : Finset I)
    (x : ∀ i, X i) : ℝ := ∑ y, w y * productFiberIndicator S x y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

def ofAssignment (S : Finset ι) (x : ∀ i, X i) : ProductCylinder X :=
  ⟨S, fun i => x i.val⟩

def Contains (c : ProductCylinder X) (x : ∀ i, X i) : Prop :=
  ∀ i : c.1, x i.val = c.2 i

theorem assignment_mem (c : ProductCylinder X) (base : ∀ i, X i) (i : ι) (hi : i ∈ c.1) :
    c.assignment base i = c.2 ⟨i, hi⟩ := by
  simp only [assignment, hi, dite_true]

theorem contains_iff (c : ProductCylinder X) (base x : ∀ i, X i) :
    c.Contains x ↔ ∀ i ∈ c.1, x i = c.assignment base i := by
  constructor
  · intro h i hi
    rw [c.assignment_mem base i hi]
    exact h ⟨i, hi⟩
  · intro h i
    rw [h i.val i.property, c.assignment_mem base i.val i.property]

end ProductCylinder

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace SimplexHypergraph

def deletionCapacity {k : ℕ} (V : Fin k → Type*)
    [∀ i, Fintype (V i)] : ℕ :=
  ∑ j, Fintype.card (DeletedVector V j)

end SimplexHypergraph

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeTrace
namespace OAI

section

namespace Erdos3

universe u v

namespace CoordinateDecisionTree

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

inductive Valid (Good : Finset ι → (∀ i, Value i) → Prop) :
    Finset ι → (∀ i, Value i) → CoordinateDecisionTree ι Value → ℕ → Prop
  | leaf {I : Finset ι} {x : ∀ i, Value i} {d : ℕ} (good : Good I x) : Valid Good I x .leaf d
  | split {I : Finset ι} {x : ∀ i, Value i} {i : ι}
      {children : Value i → CoordinateDecisionTree ι Value} {d : ℕ}
      (fresh : i ∉ I)
      (branches : ∀ value, Valid Good (insert i I) (Function.update x i value) (children value) d) :
      Valid Good I x (.split i children) (d + 1)

end CoordinateDecisionTree

end Erdos3

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem trace_contains (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (x input : ∀ i, Value i) : I ⊆ (trace tree I x input).1 := by
  induction tree generalizing I x with
  | leaf => exact Finset.Subset.refl I
  | split i children ih =>
    exact (Finset.subset_insert i I).trans (ih (input i) (insert i I) (Function.update x i (input i)))

theorem trace_agrees (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (x input : ∀ i, Value i) (hagree : ∀ i ∈ I, x i = input i) :
    ∀ i ∈ (trace tree I x input).1, (trace tree I x input).2 i = input i := by
  induction tree generalizing I x with
  | leaf => exact hagree
  | split i children ih =>
    apply ih (input i) (insert i I) (Function.update x i (input i))
    intro j hj
    by_cases hji : j = i
    · subst j
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hji]
      exact hagree j (Finset.mem_of_mem_insert_of_ne hj hji)

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeOutside
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

def liftOutside (K : Finset ι) :
    CoordinateDecisionTree {i // i ∉ K} (fun i => Value i.val) → CoordinateDecisionTree ι Value
  | .leaf => .leaf
  | .split i children => .split i.val (fun v => liftOutside K (children v))

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeRelabel
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v w

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v} {Other : ι → Type w}

def relabel (e : ∀ i, Value i ≃ Other i) :
    CoordinateDecisionTree ι Value → CoordinateDecisionTree ι Other
  | .leaf => .leaf
  | .split i children => .split i (fun v => relabel e (children ((e i).symm v)))

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CircleResiduePartition
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped NNReal

noncomputable def residueCutoff {q : ℕ} [NeZero q] (j : ZMod q) (x : Circle) : ℝ :=
  max 0 (1 - (q : ℝ) * dist x (ZMod.toAddCircle j))

theorem residueCutoff_unit_interval {q : ℕ} [NeZero q] (j : ZMod q) (x : Circle) :
    0 ≤ residueCutoff j x ∧ residueCutoff j x ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  linarith [mul_nonneg (Nat.cast_nonneg q) (dist_nonneg (x := x) (y := ZMod.toAddCircle j))]

theorem residueCutoff_lipschitz {q : ℕ} [NeZero q] (j : ZMod q) :
    LipschitzWith (q : ℝ≥0) (residueCutoff j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |max 0 (1 - (q : ℝ) * dist x (ZMod.toAddCircle j)) -
    max 0 (1 - (q : ℝ) * dist y (ZMod.toAddCircle j))| ≤ (q : ℝ) * dist x y
  calc
    _ ≤ |(1 - (q : ℝ) * dist x (ZMod.toAddCircle j)) -
        (1 - (q : ℝ) * dist y (ZMod.toAddCircle j))| := by
      rw [max_comm 0 _, max_comm 0 _]
      exact abs_max_sub_max_le_abs _ _ _
    _ = (q : ℝ) * |dist x (ZMod.toAddCircle j) - dist y (ZMod.toAddCircle j)| := by
      rw [show (1 - (q : ℝ) * dist x (ZMod.toAddCircle j)) -
          (1 - (q : ℝ) * dist y (ZMod.toAddCircle j)) =
          -(q : ℝ) * (dist x (ZMod.toAddCircle j) - dist y (ZMod.toAddCircle j)) by ring,
        abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg q)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_dist_sub_le x y (ZMod.toAddCircle j)) (Nat.cast_nonneg q)

theorem residueCutoff_at_grid {q : ℕ} [NeZero q] (j k : ZMod q) :
    residueCutoff j (ZMod.toAddCircle k) = if k = j then 1 else 0 := by
  classical
  by_cases h : k = j
  · subst k
    simp [residueCutoff]
  · simp only [h, ↓reduceIte]
    exact max_eq_left (by linarith [one_le_mul_dist_toAddCircle h])

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateLeafCount
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem trace_eq_of_agree (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input other : ∀ i, Value i)
    (hagree : ∀ i ∈ (trace tree I base input).1, other i = input i) :
    trace tree I base other = trace tree I base input := by
  induction tree generalizing I base with
  | leaf => rfl
  | split i children ih =>
    have hi : i ∈ (trace (children (input i)) (insert i I) (Function.update base i (input i)) input).1 :=
      trace_contains _ _ _ _ (Finset.mem_insert_self _ _)
    have he : other i = input i := hagree i hi
    simp only [trace, he]
    exact ih (input i) (insert i I) (Function.update base i (input i)) hagree

def traceCylinder (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) : ProductCylinder Value :=
  ProductCylinder.ofAssignment (trace tree I base input).1 (trace tree I base input).2

theorem traceCylinder_contains (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) (hinput : ∀ i ∈ I, input i = base i) :
    (traceCylinder tree I base input).Contains input := by
  intro i
  exact (trace_agrees tree I base input (fun j hj => (hinput j hj).symm) i i.property).symm

theorem traceCylinder_contains_iff (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input other : ∀ i, Value i) (hinput : ∀ i ∈ I, input i = base i) :
    (traceCylinder tree I base input).Contains other ↔
      (∀ i ∈ I, other i = base i) ∧ traceCylinder tree I base other = traceCylinder tree I base input := by
  have htrace := trace_agrees tree I base input (fun i hi => (hinput i hi).symm)
  constructor
  · intro h
    have hagree : ∀ i ∈ (trace tree I base input).1, other i = input i := by
      intro i hi
      exact (h ⟨i, hi⟩).trans (htrace i hi)
    have heq := trace_eq_of_agree tree I base input other hagree
    refine ⟨fun i hi => (hagree i (trace_contains tree I base input hi)).trans (hinput i hi), ?_⟩
    unfold traceCylinder
    rw [heq]
  · rintro ⟨hother, heq⟩
    rw [← heq]
    exact traceCylinder_contains tree I base other hother

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Value : ι → Type*}
  [∀ i, Fintype (Value i)]

noncomputable def leafCylinders (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) : Finset (ProductCylinder Value) :=
  (Finset.univ.filter (fun input : ∀ i, Value i => ∀ i ∈ I, input i = base i)).image
    (traceCylinder tree I base)

theorem mem_leafCylinders (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) (c : ProductCylinder Value) :
    c ∈ leafCylinders tree I base ↔
      ∃ input, (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c := by
  simp only [leafCylinders, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem leafCylinders_contains_iff (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) (c : ProductCylinder Value) (hc : c ∈ leafCylinders tree I base) :
    c.Contains input ↔ (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c := by
  obtain ⟨source, hs, rfl⟩ := (mem_leafCylinders tree I base c).mp hc
  exact traceCylinder_contains_iff tree I base source input hs

theorem leafCylinders_indicator_sum (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) :
    (∑ c ∈ leafCylinders tree I base, productFiberIndicator c.1 (c.assignment base) input) =
      productFiberIndicator I base input := by
  have he (c : ProductCylinder Value) (hc : c ∈ leafCylinders tree I base) :
      productFiberIndicator c.1 (c.assignment base) input =
        if (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c then 1 else 0 := by
    simp only [productFiberIndicator, ← ProductCylinder.contains_iff,
      leafCylinders_contains_iff tree I base input c hc]
  calc
    _ = ∑ c ∈ leafCylinders tree I base,
        if (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl he
    _ = _ := by
      by_cases hi : ∀ i ∈ I, input i = base i
      · have hc : traceCylinder tree I base input ∈ leafCylinders tree I base :=
          (mem_leafCylinders tree I base _).mpr ⟨input, hi, rfl⟩
        have hvalue : productFiberIndicator I base input = 1 := by
          unfold productFiberIndicator
          exact if_pos hi
        rw [hvalue, Finset.sum_eq_single (traceCylinder tree I base input)]
        · exact if_pos ⟨hi, rfl⟩
        · intro c _ hne
          exact if_neg (fun h => hne h.2.symm)
        · exact fun hn => False.elim (hn hc)
      · have hvalue : productFiberIndicator I base input = 0 := by
          unfold productFiberIndicator
          exact if_neg hi
        rw [hvalue]
        apply Finset.sum_eq_zero
        intro c _
        exact if_neg (fun h => hi h.1)

theorem leafCylinders_mass_sum (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) (w : (∀ i, Value i) → ℝ) :
    (∑ c ∈ leafCylinders tree I base, productFiberMass w c.1 (c.assignment base)) =
      productFiberMass w I base := by
  unfold productFiberMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, leafCylinders_indicator_sum]

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}
  [∀ i, Fintype (Y i)]
  {Good : Finset ι → (∀ i, Y i) → Prop}
  {tree : CoordinateDecisionTree ι Y} {I : Finset ι} {base : ∀ i, Y i} {d : ℕ}

noncomputable def leafSourceAssignments (X : ι → Type*) [∀ i, Fintype (X i)]
    (tree : CoordinateDecisionTree ι Y) (I : Finset ι) (base : ∀ i, Y i) :
    Finset (Σ c : ProductCylinder Y, ∀ i : c.1, X i.val) :=
  (leafCylinders tree I base).sigma (fun _c => Finset.univ)

end Erdos3.CoordinateDecisionTree

end

end OAI
end


