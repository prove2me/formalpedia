-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_StoppedProcess
-- name    : KLSModular_BrownianMotion_Auxiliary_StoppedProcess
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:47:35.268996+00:00
-- url     : https://prove2.me/theorems/b4c3b2bd-27ef-4c9e-ad42-8ef7fe087414
-- title:
--   Stopped-process simplification rules
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `stoppedProcess_of_eq_coe` identifies a stopped process at a stopping time equal to an ordinary index $t$ with the original process evaluated at `min s t`. The bundle also proves that `stoppedValue` distributes over addition, negation, and subtraction.
--
--   **Original module imports**
--
--   ```lean
--   public import BrownianMotion.Auxiliary.Indistinguishable
--   public import BrownianMotion.StochasticIntegral.Cadlag
--   public import Mathlib.Probability.Process.Stopping
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   @[simp]
--   lemma stoppedProcess_of_eq_coe (s : ι) (hτ : τ ω = t) :
--       stoppedProcess X τ s ω = X (min s t) ω := by
--     obtain h | h := le_total s t <;> simp [stoppedProcess, hτ, h]
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`BrownianMotion/Auxiliary/Indistinguishable`](https://prove2.me/theorems/3a794f16-2add-4e7d-a6e0-8ee3c433f2af), [`BrownianMotion/StochasticIntegral/Cadlag`](https://prove2.me/theorems/018dc80a-f371-45a4-ad73-e4ef0a7c732d).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/StoppedProcess.lean) · `BrownianMotion.Auxiliary.StoppedProcess` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/StoppedProcess.lean#L26-L133 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.StoppedProcess`, definition bundle `KLSModular_BrownianMotion_Auxiliary_StoppedProcess`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Indistinguishable
import Definitions.Def_KLSModular_BrownianMotion_StochasticIntegral_Cadlag
import Mathlib.Probability.Process.Stopping

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/StoppedProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace MeasureTheory
variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Nonempty ι]
  {τ : Ω → WithTop ι} {ω : Ω} {t : ι} {X Y : ι → Ω → E}
section stoppedProcess
variable [LinearOrder ι]
@[simp]
lemma stoppedProcess_of_eq_coe (s : ι) (hτ : τ ω = t) :
    stoppedProcess X τ s ω = X (min s t) ω := by
  obtain h | h := le_total s t <;> simp [stoppedProcess, hτ, h]
end stoppedProcess
namespace stoppedValue
@[simp] lemma add [Add E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u + v) τ = stoppedValue u τ + stoppedValue v τ := rfl
@[simp] lemma neg [Neg E] {u : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (-u) τ = -stoppedValue u τ := rfl
@[simp] lemma sub [Sub E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u - v) τ = stoppedValue u τ - stoppedValue v τ := rfl
end stoppedValue
end MeasureTheory


