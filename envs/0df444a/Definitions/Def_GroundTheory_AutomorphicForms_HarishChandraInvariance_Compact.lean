-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
-- name    : GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:46.131544+00:00
-- url     : https://prove2.me/theorems/8156cbc2-5398-429f-b56c-10c8dbea3818
-- title:
--   Compact
-- statement:
--   Definitions and structural lemmas for Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
section Conj
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def conjCME (k : G) : G ≃ₜ* G :=
  { MulAut.conj k with
    continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
    continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
end Conj
section Closed
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
end Closed
section MaxCompact
open Matrix
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
end MaxCompact
end GroundTheory.Automorphic


