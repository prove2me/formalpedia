-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellGronwallIdentity_F000
-- name    : LevyStochCalc_Driver_CellGronwallIdentity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:31:10.973656+00:00
-- url     : https://prove2.me/theorems/cb6981f1-d896-457a-a0d8-b871234dd40f
-- title:
--   Source declarations: LevyStochCalc.Driver.CellGronwallIdentity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellGronwallIdentity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F001
import Definitions.Def_SourceProof_0bb2980da918585a74bdb0be
import Definitions.Def_SourceProof_8e93ea357455e3e54fbc2c2e
import Definitions.Def_SourceProof_a0fbf86328c3631d08155362

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell identity and the Grönwall bound for the cell pairing

The real and the imaginary cell identities recombine into an integral equation for the pairing of
a square-integrable weight and a bounded factor with the product of the Brownian cell character
`e^{i l X_s}` and the Poisson cell character: the pairing at a time in the cell is its value at
the origin plus a deterministic drift term over the elapsed times and a mark-factor term over the
window. The Grönwall estimate that follows forces the pairing to vanish throughout the cell when
the weight is orthogonal to every Itô integral and every compensated integral and has mean zero
against the bounded factor.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Identity

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {ι : Type*} [Fintype ι]

include hℱN hℱW in
/-- **The real part of the cell identity, in the recombination's form.** -/
theorem cellPart_identity_re
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hg'c : Continuous g') (hg'b : ∀ x, |g' x| ≤ |l|)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).re) t
      = cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).re) 0
        + ∫ s in Set.Ioc (0 : ℝ) t, cellDrift l a b s
            * cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).re) s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            (∫ ω, Z ω * V ω * (g (l * X q.1 ω) * charRe N w Bfam A T ω q.1 q.2) ∂P)
            ∂(referenceIntensity ν) := by
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hBsub' : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha hbT.le) le_rfl)
  refine _root_.Prove2MeSourceProof.h_8e93ea357455e3e54fbc2c2e hXbase hgc hgb hAν
    (Ym := fun s ω => (charStrictPred N w Bfam A T e₀ s ω).re)
    (Complex.measurable_re.comp (measurable_uncurry_charStrictPred N w hℱN hBm hA hAν T e₀))
    (fun s ω => abs_charStrictPred_re_le N w Bfam A T e₀ s ω) (fun s hs => ?_)
    (measurable_charRe N hℱN w hBm hA hAν hBsub') (abs_charRe_le N w Bfam A T)
    (hZ2.integrable one_le_two) ((hVa.mono (ℱ.le a)).measurable) hMv0 hVb
    (_root_.Prove2MeSourceProof.h_0bb2980da918585a74bdb0be N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b hmg hpg hqg hito
      hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT)
  filter_upwards [ae_charStrictPred_eq_charAt N w hBm hT hbT hBsub0 he₀ hs] with ω hω
  rw [hω]
include hℱN hℱW in
/-- **The imaginary part of the cell identity, in the recombination's form.** -/
theorem cellPart_identity_im
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hg'c : Continuous g') (hg'b : ∀ x, |g' x| ≤ |l|)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).im) t
      = cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).im) 0
        + ∫ s in Set.Ioc (0 : ℝ) t, cellDrift l a b s
            * cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).im) s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            (∫ ω, Z ω * V ω * (g (l * X q.1 ω) * charIm N w Bfam A T ω q.1 q.2) ∂P)
            ∂(referenceIntensity ν) := by
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hBsub' : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha hbT.le) le_rfl)
  refine _root_.Prove2MeSourceProof.h_8e93ea357455e3e54fbc2c2e hXbase hgc hgb hAν
    (Ym := fun s ω => (charStrictPred N w Bfam A T e₀ s ω).im)
    (Complex.measurable_im.comp (measurable_uncurry_charStrictPred N w hℱN hBm hA hAν T e₀))
    (fun s ω => abs_charStrictPred_im_le N w Bfam A T e₀ s ω) (fun s hs => ?_)
    (measurable_charIm N hℱN w hBm hA hAν hBsub') (abs_charIm_le N w Bfam A T)
    (hZ2.integrable one_le_two) ((hVa.mono (ℱ.le a)).measurable) hMv0 hVb
    (_root_.Prove2MeSourceProof.h_a0fbf86328c3631d08155362 N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b hmg hpg hqg hito
      hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT)
  filter_upwards [ae_charStrictPred_eq_charAt N w hBm hT hbT hBsub0 he₀ hs] with ω hω
  rw [hω]
end Identity

end LevyStochCalc.Driver


