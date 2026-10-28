-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
-- name    : KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:54:15.79085+00:00
-- url     : https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3
-- title:
--   Gaussian fourth moment and elementary Itô-integral sums
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `gaussianFourthMoment` is the real fourth moment $\int x^4\,d\mathcal N(0,1)$; for a simple predictable integrand $G$ and Brownian motion $W$ under a probability measure $P$, `SimplePredictable.term G W i ω` is its $i$-th coefficient times the corresponding Brownian increment, and `SimplePredictable.partialSum G W k ω` sums these terms for $i<k$. `SimplePredictable.varClock G W c k` records $\sum_{j<k}c_j^2(\tau_{j+1}-\tau_j)$, with terms beyond the partition length contributing zero.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoAlgebra
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def gaussianFourthMoment : ℝ :=
--     ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoAlgebra`](https://prove2.me/theorems/602bc476-bf93-48d5-972e-3d6b80e662e4).
--
--   Theorems in source order:
--
--   - [`integral_pow_gaussianReal_zero`](https://prove2.me/theorems/5bcebbba-553a-4972-8595-83ab7dcceb2b)
--   - [`integral_mul_increment_pow`](https://prove2.me/theorems/8fc1f6bc-eb0f-42e8-a4c1-562b4c26ab81)
--   - [`stronglyMeasurable_partialSum`](https://prove2.me/theorems/fd1cc025-8f0a-4737-8e80-8b55eaf193de)
--   - [`varClock_mono`](https://prove2.me/theorems/ca4d3739-0c25-400e-91e5-2326905bc735)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean) · `LevyStochCalc.Brownian.ItoFourthMomentIncrements` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentIncrements`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean, lines 30-246). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebra

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The fourth moment of the standard real Gaussian distribution. -/
noncomputable def gaussianFourthMoment : ℝ :=
  ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)
namespace SimplePredictable
variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
/-- The `i`-th summand of the elementary integral, indexed by a natural number. -/
noncomputable def term (i : ℕ) (ω : Ω) : ℝ :=
  if h : i < G.N then
    G.ξ ⟨i, h⟩ ω * (W.W (G.partition (⟨i, h⟩ : Fin G.N).succ) ω
      - W.W (G.partition (⟨i, h⟩ : Fin G.N).castSucc) ω)
  else 0
/-- The partial sums of the elementary integral. -/
noncomputable def partialSum (k : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range k, G.term W i ω
/-- The variance budget of the first `k` tiles for a per-tile coefficient bound `c`:
`∑_{j < k} c_j² (τ_{j+1} − τ_j)`. -/
noncomputable def varClock (c : Fin G.N → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if h : j < G.N then
    c ⟨j, h⟩ ^ 2 * (G.partition (⟨j, h⟩ : Fin G.N).succ
      - G.partition (⟨j, h⟩ : Fin G.N).castSucc) else 0
end SimplePredictable
end Ito
end Brownian
end LevyStochCalc


