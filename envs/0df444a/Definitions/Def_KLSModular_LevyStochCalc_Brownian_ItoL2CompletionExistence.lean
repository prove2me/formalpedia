-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionExistence
-- name    : KLSModular_LevyStochCalc_Brownian_ItoL2CompletionExistence
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:03:34.303675+00:00
-- url     : https://prove2.me/theorems/9727ce0e-a8ed-421f-8cc3-bd27f99d9261
-- title:
--   Strong adaptedness of the simple Brownian integral
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. Given a Brownian motion $W$, a Brownian filtration $\mathcal F$, and an adapted `SimplePredictable` integrand $H$, `simpleIntegral_stronglyAdapted_brownian` states that for every $t\in\mathbb R$, the map $\omega\mapsto\operatorname{simpleIntegral}(W,H,t)(\omega)$ is strongly measurable with respect to $\mathcal F_t$. This is the adaptedness component of the simple-integral construction; it does not define the completed $L^2$ integral.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoL2CompletionLp
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   lemma simpleIntegral_stronglyAdapted_brownian
--       {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
--       (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       {T : ℝ} (H : SimplePredictable Ω T)
--       (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (H.partition i.castSucc)) (H.ξ i))
--       (t : ℝ) :
--       @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ t)
--         (fun ω => simpleIntegral W H t ω) :=
--     (martingale_simpleIntegral_brownian W ℱ hℱ H h_adapt).stronglyAdapted t
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoL2CompletionLp`](https://prove2.me/theorems/4aa3ab04-3958-47e7-870f-6b1a325ace99).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionExistence.lean) · `LevyStochCalc.Brownian.ItoL2CompletionExistence` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionExistence.lean#L26-L45 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionExistence`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoL2CompletionExistence`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionLp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionExistence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
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
  (martingale_simpleIntegral_brownian W ℱ hℱ H h_adapt).stronglyAdapted t
end Ito
end Brownian
end LevyStochCalc


