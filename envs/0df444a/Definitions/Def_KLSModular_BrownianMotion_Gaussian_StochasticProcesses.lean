-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Gaussian_StochasticProcesses
-- name    : KLSModular_BrownianMotion_Gaussian_StochasticProcesses
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:35:18.657443+00:00
-- url     : https://prove2.me/theorems/9e942262-b382-43fc-abe4-0bf280337f00
-- title:
--   Dense subsets of open sets
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `subset_closure_dense_inter` states that if `T'` is dense in a topological space and `U` is open, then $U⊆\overline{T'∩U}$.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   open scoped Topology in
--   lemma subset_closure_dense_inter {α : Type*} [TopologicalSpace α] {T' U : Set α}
--       (hT'_dense : Dense T') (hU : IsOpen U) :
--       U ⊆ closure (T' ∩ U) := by
--     refine fun x hxU ↦ mem_closure_iff_nhds.mpr fun t ht ↦ ?_
--     have htU : t ∩ U ∈ 𝓝 x := by simp [ht, hU.mem_nhds hxU]
--     suffices (T' ∩ (t ∩ U)).Nonempty by grind
--     exact hT'_dense.inter_nhds_nonempty htU
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Gaussian/StochasticProcesses.lean) · `BrownianMotion.Gaussian.StochasticProcesses` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Gaussian/StochasticProcesses.lean#L30-L37 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Gaussian.StochasticProcesses`, definition bundle `KLSModular_BrownianMotion_Gaussian_StochasticProcesses`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

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


