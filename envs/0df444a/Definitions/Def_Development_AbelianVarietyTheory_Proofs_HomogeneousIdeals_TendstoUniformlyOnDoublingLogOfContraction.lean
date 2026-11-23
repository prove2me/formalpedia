-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:34.54056+00:00
-- url     : https://prove2.me/theorems/27c2dfac-0e43-4258-b7ca-c348660ac39a
-- title:
--   Tendsto Uniformly On Doubling Log Of Contraction
-- statement:
--   Definitions and structural lemmas for Tendsto Uniformly On Doubling Log Of Contraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
namespace GlobalTheory
section Taylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
end Taylor
section Halving
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
noncomputable def doublingLog (ε : V → V) (x : V) : V :=
  limUnder atTop fun j : ℕ => (2 : ℂ) ^ j • ε^[j] x
variable {ε : V → V} {r C : ℝ}
variable [CompleteSpace V]
end Halving
section Extension
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]
end Extension
end GlobalTheory


