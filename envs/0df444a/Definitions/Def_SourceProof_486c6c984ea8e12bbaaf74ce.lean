-- Prove2me | Definitions.Def_SourceProof_486c6c984ea8e12bbaaf74ce
-- name    : SourceProof_486c6c984ea8e12bbaaf74ce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:28:50.477581+00:00
-- url     : https://prove2.me/theorems/a7dd0132-881b-4cee-90da-20cdfc099007
-- title:
--   LevyStochCalc source module: SourceProof_486c6c984ea8e12bbaaf74ce
-- statement:
--   The original source theorem `LevyStochCalc.Driver.cellPairing_eq_zero` comes from the `LevyStochCalc.Driver.CellGronwallIdentity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallIdentity_F001
import Definitions.Def_SourceProof_c464ce22d9a9d649a047ee62

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

theorem _root_.Prove2MeSourceProof.h_486c6c984ea8e12bbaaf74ce
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b) (l : ℝ)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hZV : ∫ ω, Z ω * V ω ∂P = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, cellPairing N w Bfam Z V l X t = 0 := by
  have hVm : Measurable V := (hVa.mono (ℱ.le a)).measurable
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := hXbase.measurable_uncurry
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hu0 : LevyStochCalc.Driver.cellPairing N w Bfam Z V l X 0 = 0 := by
    rw [LevyStochCalc.Driver.cellPairing_zero N w Bfam hX0, hZV, Complex.ofReal_zero]
  have hsplit : ∀ s, LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s
      = LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.cos s
        + Complex.I * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.sin s := fun s =>
    _root_.Prove2MeSourceProof.h_d70b081240f0d1c36022214e N w hBm hZ2 hVm hVb (hXbase.measurable s)
  have hmeas : AEStronglyMeasurable (fun s => ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s‖)
      (volume.restrict (Set.Icc (0 : ℝ) b)) := by
    have hc := _root_.Prove2MeSourceProof.h_d1d586759601e65f10bea970 (l := l) N hℱN w hBm hA hAν hT hbT hBsub0 he₀
      hZ2 hVm Real.continuous_cos hXm b
    have hs := _root_.Prove2MeSourceProof.h_d1d586759601e65f10bea970 (l := l) N hℱN w hBm hA hAν hT hbT hBsub0 he₀
      hZ2 hVm Real.continuous_sin hXm b
    exact ((hc.add (hs.const_mul Complex.I)).congr
      (Filter.Eventually.of_forall fun s => (hsplit s).symm)).norm
  have hzero := LevyStochCalc.Analysis.eq_zero_of_le_mul_setIntegral
    (a := (0 : ℝ)) (b := b) (c := l ^ 2 / 2 + 2 * (ν A).toReal)
    (B := 2 * (Mv * ∫ ω, ‖Z ω‖ ∂P))
    (by positivity) hmeas (fun t => norm_nonneg _)
    (fun t _ => LevyStochCalc.Driver.norm_cellPairing_bound (l := l) N w hBm hZ2 hVm hMv0 hVb
      (hXbase.measurable t)) ?_
  · intro t ht
    exact norm_eq_zero.mp (hzero t ht)
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hu0, norm_zero, Set.Ioc_self]
      simp
    · have hb := _root_.Prove2MeSourceProof.h_c464ce22d9a9d649a047ee62 N hℱN W hℱW hXbase hX0 ha hab l hT hbT hA hAν w hBm
        hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb h0 (ht.2.trans hbT.le)
      rw [hu0, norm_zero, zero_add] at hb
      exact hb
end Identity

end LevyStochCalc.Driver


