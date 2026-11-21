-- Prove2me | Definitions.Def_SourceProof_79c2c57f6aeff6dbd6853f31
-- name    : SourceProof_79c2c57f6aeff6dbd6853f31
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:38:44.537235+00:00
-- url     : https://prove2.me/theorems/ff56042d-27c5-4e3c-8bed-2976d43f5e92
-- title:
--   LevyStochCalc source module: SourceProof_79c2c57f6aeff6dbd6853f31
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_brownian` comes from the `LevyStochCalc.Brownian.ItoMartingale` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoMartingale_F000

open private simpleIntegral_term_adapted_brownian simpleIntegral_term_condExp_brownian simpleIntegral_term_integrable_brownian from Definitions.Def_LevyStochCalc_Brownian_ItoMartingale_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingale property of the simple Brownian integral

`simpleIntegral W H` is a martingale w.r.t. any filtration `ℱ` for which `W` is a
Brownian motion and `H` is adapted (`martingale_simpleIntegral_brownian`), via the
conditional-expectation identity for `W`. Builds on `Brownian/ItoSimple.lean` and
`Brownian/ItoDensity.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_79c2c57f6aeff6dbd6853f31
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => simpleIntegral W H t)
      ℱ P := by
  refine ⟨?_, ?_⟩
  · -- StronglyAdapted: per-term + `Finset.stronglyMeasurable_fun_sum`.
    intro t
    change @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
      (fun ω => ∑ i : Fin H.N,
        H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
                  - W.W (min (H.partition i.castSucc) t) ω))
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    exact simpleIntegral_term_adapted_brownian W ℱ hℱ H i t (h_adapt i)
  · -- Cond-exp identity: per-term + `condExp_finset_sum`.
    intro s t hst
    -- Rewrite each `simpleIntegral W H u` as a Pi-sum of per-term functions.
    have h_unfold_pi : ∀ u : ℝ, (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W H u ω) =
        ∑ i : Fin H.N, (fun ω : Ω => H.ξ i ω *
          (W.W (min (H.partition i.succ) u) ω
            - W.W (min (H.partition i.castSucc) u) ω)) := by
      intro u
      ext ω
      rw [Finset.sum_apply]
      rfl
    change P[fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω | ℱ.seq s] =ᵐ[P]
      fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W H s ω
    rw [h_unfold_pi t, h_unfold_pi s]
    have h_int : ∀ i ∈ (Finset.univ : Finset (Fin H.N)),
        MeasureTheory.Integrable (fun ω => H.ξ i ω *
          (W.W (min (H.partition i.succ) t) ω
            - W.W (min (H.partition i.castSucc) t) ω)) P :=
      fun i _ => simpleIntegral_term_integrable_brownian W H i t
    have h_step1 := MeasureTheory.condExp_finsetSum h_int (m := ℱ.seq s)
    refine h_step1.trans ?_
    refine eventuallyEq_sum ?_
    intro i _
    exact simpleIntegral_term_condExp_brownian W ℱ hℱ H i (h_adapt i) hst
end LevyStochCalc.Brownian.Ito


