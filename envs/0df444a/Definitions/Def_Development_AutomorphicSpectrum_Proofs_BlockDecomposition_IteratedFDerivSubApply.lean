-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:09.194303+00:00
-- url     : https://prove2.me/theorems/8c1e8d01-fb71-4cfa-ab00-4a1193281217
-- title:
--   Iterated FDeriv Sub Apply
-- statement:
--   Definitions and structural lemmas for Iterated FDeriv Sub Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedFDerivSubApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff Topology Uniformity
open Filter
namespace GlobalTheory.CompanionTheory.SchwartzBaire
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end GlobalTheory.CompanionTheory.SchwartzBaire


