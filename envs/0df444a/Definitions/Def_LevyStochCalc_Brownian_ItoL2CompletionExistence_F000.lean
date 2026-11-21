-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
-- name    : LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:40:35.416338+00:00
-- url     : https://prove2.me/theorems/8819dda8-61ab-4de6-9735-b2f52ba3e781
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionExistence
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionExistence. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityUnbounded_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionLp_F000
import Definitions.Def_SourceProof_79c2c57f6aeff6dbd6853f31

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: existence of the `L²` integral

Adaptedness, integrability and conditional-expectation identities for the
simple-integrand Brownian integral, and the existence statements they yield for
the `L²` Itô integral of a bounded, respectively progressively measurable and
square-integrable, integrand against a Brownian motion `W` on a Brownian
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **C0b.10-post8: `simpleIntegral W H t` is StronglyAdapted at `t`
to `ℱ`.**

For each `t : ℝ` and adapted SimplePredictable `H`, the function
`ω ↦ simpleIntegral W H t ω` is StronglyMeasurable wrt the
filtration's σ-algebra at `t`. Direct from
`martingale_simpleIntegral_brownian` (which establishes adaptedness as
its first conjunct). -/
lemma simpleIntegral_stronglyAdapted_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t)
      (fun ω => simpleIntegral W H t ω) :=
  (_root_.Prove2MeSourceProof.h_79c2c57f6aeff6dbd6853f31 W ℱ hℱ H h_adapt).stronglyAdapted t
/-- **C0b.10-post9: `simpleIntegral W H t` is in `Lp ℝ 1 P`** (integrable).

Direct from `Lp 2 ⊆ Lp 1` for finite measures (`MemLp.mono_exponent`)
applied to `simpleIntegral_memLp_brownian` (post2). Used in martingale
property checks where integrability (Lp¹) is required. -/
lemma simpleIntegral_integrable_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Integrable (fun ω => simpleIntegral W H T ω) P := by
  have h_memLp := _root_.Prove2MeSourceProof.h_f66d6db4e190cceae9d19c65 W ℱ hℱ hT H h_adapt
  -- MemLp 2 P implies MemLp 1 P (= Integrable) when measure is finite.
  exact (h_memLp.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable
    (le_refl 1)
/-- **C0b.10-post10: cond-exp identity for `simpleIntegral`.** Direct
extraction of the cond-exp clause from `martingale_simpleIntegral_brownian`
for downstream use without unpacking the Martingale structure. -/
lemma simpleIntegral_condExp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => simpleIntegral W H t ω
        | ℱ s]
      =ᵐ[P] (fun ω => simpleIntegral W H s ω) :=
  (_root_.Prove2MeSourceProof.h_79c2c57f6aeff6dbd6853f31 W ℱ hℱ H h_adapt).condExp_ae_eq hst
/-- **C0b.10-final: existence of an L²-isometric process for adapted-approximated H.**

Conditional on:
- `H` being approximated in `L²(λ⊗P)` by an adapted approximating
  sequence `(G n)` of `SimplePredictable`s sharing common endpoint, AND
- the lintegral_sq of `(G n).eval` converging to lintegral_sq of `H`,

we get an `L²(P)`-element `M` (the L²-extended Itô integral) satisfying
the L² isometry `eLpNorm² M = lintegral_sq H` over `[0,T] × Ω`.

This is the existence content extracted from the C0b chain, without
the additional martingale + quadVar conjuncts of the full strong-exists.
For closing the full strong-exists, one needs (a) extending C0b.9 to
general time `t < T`, (b) the limit-of-martingales + limit-of-quadVar
arguments for the time-parametrized version. -/
theorem exists_itoIntegralL2_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε)
    (H : Ω → ℝ → ℝ)
    (h_eval_norm_tendsto : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) :
    ∃ M : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑M : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
  ⟨itoIntegralLp_brownian W ℱ hℱ hT G h_eq h_adapt h_cauchy_eval,
   itoIntegralLp_brownian_L2_isometry W ℱ hℱ hT G h_eq h_adapt h_cauchy_eval H
     h_eval_norm_tendsto⟩
/-- **Bounded progressively-measurable existence.** For bounded progressively-measurable
`g : Ω → ℝ → ℝ` with explicit bound `M`, there exists an `Lp ℝ 2 P` element whose
squared `eLpNorm` over `P` equals the full `L²(P × ds)` norm of `g` over `[0,T]`.

Construction: feed the explicit `predictableDyadicSimple_brownian` sequence into
`exists_itoIntegralL2_brownian`. All four prerequisites are dyadic-specific lemmas
already in `Brownian.Ito`:

* `_partition_last` for `h_eq` (constant endpoint = T).
* `_adapted` for `h_adapt` (under progressive measurability).
* `L2_cauchy_of_L2_tendsto_brownian` applied to `_L2_converges` for `h_cauchy_eval`.
* `_eval_norm_tendsto_bounded` for `h_eval_norm_tendsto`. -/
theorem exists_itoIntegralL2_brownian_progMeas_bounded
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ g)
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Mlp : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set G : ℕ → SimplePredictable Ω T :=
    fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n with hG
  have h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N) := by
    intro n m
    rw [predictableDyadicSimple_brownian_partition_last hT g h_meas M h_bound n,
        predictableDyadicSimple_brownian_partition_last hT g h_meas M h_bound m]
  have h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((G n).partition i.castSucc)) ((G n).ξ i) :=
    fun n => predictableDyadicSimple_brownian_adapted ℱ hT g h_meas M h_bound h_progMeas n
  have h_norm_tendsto :=
    predictableDyadicSimple_brownian_eval_norm_tendsto_bounded
      (P := P) hT g h_meas M h_bound
  -- L²-Cauchy: from L²-Tendsto via the generic helper.
  have h_L2_diff := _root_.Prove2MeSourceProof.h_5731c142c22a48f56440eba3
    (P := P) hT g h_meas M h_bound
  have h_eval_meas : ∀ n,
      Measurable (fun (p : Ω × ℝ) => (G n).eval p.2 p.1) :=
    fun n => _root_.Prove2MeSourceProof.h_4d8cba1d4063b809a3d381bd
      hT g h_meas M h_bound n
  have h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε :=
    _root_.Prove2MeSourceProof.h_6f312b3c41a43c93c4f0c9a1 (P := P) (T := T)
      G g h_eval_meas h_meas h_L2_diff
  exact exists_itoIntegralL2_brownian (P := P) W ℱ hℱ hT G h_eq h_adapt h_cauchy_eval g
    h_norm_tendsto
end LevyStochCalc.Brownian.Ito


