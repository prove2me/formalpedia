-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
-- name    : KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:09:42.397526+00:00
-- url     : https://prove2.me/theorems/fcb8c55c-6db4-438c-b9a8-83e9d6d16f2c
-- title:
--   Dense subsets of open sets
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `subset_closure_dense_inter` states that if `T'` is dense in a topological space and `U` is open, then $U⊆\overline{T'∩U}$.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Gaussian/StochasticProcesses.lean#L30-L37 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Gaussian.StochasticProcesses`, definition bundle `KLS408915f_BrownianMotion_Gaussian_StochasticProcesses`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Gaussian/StochasticProcesses.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E}
open scoped Topology in
lemma subset_closure_dense_inter {α : Type*} [TopologicalSpace α] {T' U : Set α}
    (hT'_dense : Dense T') (hU : IsOpen U) :
    U ⊆ closure (T' ∩ U) := by
  refine fun x hxU ↦ mem_closure_iff_nhds.mpr fun t ht ↦ ?_
  have htU : t ∩ U ∈ 𝓝 x := by simp [ht, hU.mem_nhds hxU]
  suffices (T' ∩ (t ∩ U)).Nonempty by grind
  exact hT'_dense.inter_nhds_nonempty htU


