-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_StoppedProcess
-- name    : KLS408915f_BrownianMotion_Auxiliary_StoppedProcess
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:38:44.616496+00:00
-- url     : https://prove2.me/theorems/d4db6692-84d6-4bfd-a87c-6f96aade8554
-- title:
--   Stopped-process simplification rules
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `stoppedProcess_of_eq_coe` identifies a stopped process at a stopping time equal to an ordinary index $t$ with the original process evaluated at `min s t`. The bundle also proves that `stoppedValue` distributes over addition, negation, and subtraction.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/StoppedProcess.lean#L26-L133 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.StoppedProcess`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_StoppedProcess`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Indistinguishable
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Cadlag
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightLim

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


