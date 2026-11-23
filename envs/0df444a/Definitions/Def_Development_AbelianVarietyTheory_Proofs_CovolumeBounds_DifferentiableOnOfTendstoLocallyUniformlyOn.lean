-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:10.710719+00:00
-- url     : https://prove2.me/theorems/dc86dfc5-6841-40ae-91ca-d90bb91e9bc7
-- title:
--   Differentiable On Of Tendsto Locally Uniformly On
-- statement:
--   Definitions and structural lemmas for Differentiable On Of Tendsto Locally Uniformly On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
namespace GlobalTheory.SCV
section Estimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
end Estimates
section FiniteDimensional
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
section Limits
variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}
end Limits
end FiniteDimensional
end GlobalTheory.SCV


