-- Prove2me | Definitions.Def_CK_GeneralCK_ConditionalCK
-- name    : CK_GeneralCK_ConditionalCK
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:27:35.698171+00:00
-- url     : https://prove2.me/theorems/97529a78-c586-441a-b693-fe0bea6938e1
-- title:
--   Courtade–Kumar proof module `GeneralCK.ConditionalCK` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ConditionalCK` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ConditionalCK` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ConditionalCK (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ConditionalCK.lean)

import Definitions.Def_CK_GeneralCK_EntropyFlow
import Definitions.Def_CK_GeneralCK_LimitTransfer

namespace GeneralCK
open scoped BigOperators

theorem regularizedEntropyBound_of_bellman (hB : FiniteHybridBellman) :
    LimitTransfer.RegularizedEntropyBound := by
  intro n f eps p he he' hp hp'
  let T : ℝ := -Real.log (1 - 2 * p) / 2
  have harg : 0 < 1 - 2 * p := by linarith
  have harg' : 1 - 2 * p ≤ 1 := by linarith
  have hT : 0 ≤ T := by
    have hlog := Real.log_nonpos harg.le harg'
    dsimp [T]
    linarith
  have hexp : Real.exp (-2 * T) = 1 - 2 * p := by
    have h : -2 * T = Real.log (1 - 2 * p) := by dsimp [T]; ring
    rw [h, Real.exp_log harg]
  have hcross : Noise.crossover T = p := by unfold Noise.crossover; rw [hexp]; ring
  have hparam : Comparison.noiseParameter eps T = eps + p - 2 * eps * p := by
    unfold Comparison.noiseParameter
    rw [hexp]
    ring
  have hflow : Flow.flow f eps T = LimitTransfer.regularizedPosterior f p eps := by
    funext x
    unfold Flow.flow Flow.regularized LimitTransfer.regularizedPosterior
    rw [hcross, Noise.applyNoise_affine, Noise.applyNoise_indicator]
  have h := Flow.entropy_flow_bound hB f he he' hT
  rw [hparam] at h
  simpa only [Flow.delta, Flow.gamma, Flow.initialMean_eq, hflow,
    CubeAnalysis.mean, Information.cubeWeight, LimitTransfer.regularizedMean,
    Function.comp_apply] using h

/-- Complete conditional deduction: the precise finite hybrid Bellman
inequality implies the approved general CK theorem, including every endpoint.
The Bellman premise itself remains to be proved. -/
theorem generalCourtadeKumar_of_finiteHybridBellman
    (hB : FiniteHybridBellman) : GeneralCourtadeKumar :=
  LimitTransfer.regularizedEntropyBound_implies_CK (regularizedEntropyBound_of_bellman hB)

theorem bellmanToCK : BellmanToCK := generalCourtadeKumar_of_finiteHybridBellman

end GeneralCK


