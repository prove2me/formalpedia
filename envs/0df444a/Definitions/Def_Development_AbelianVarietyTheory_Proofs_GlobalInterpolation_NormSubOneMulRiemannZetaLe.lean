-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:29.767831+00:00
-- url     : https://prove2.me/theorems/cf42faf3-1b76-4424-9b68-9c5064657c66
-- title:
--   Norm Sub One Mul Riemann Zeta Le
-- statement:
--   Definitions and structural lemmas for Norm Sub One Mul Riemann Zeta Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
namespace GlobalTheory.ZetaLeft
noncomputable def emT (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (1 - s) - (1 - s) * (x : ℂ) ^ (1 - s - 1) / 2
    + (1 - s) * (1 - s - 1) * (x : ℂ) ^ (1 - s - 1 - 1) / 12
noncomputable def emE (x : ℝ) (s : ℂ) : ℂ :=
  emT (x + 1) s - emT x s - (1 - s) * (x : ℂ) ^ (1 - s - 1)
end GlobalTheory.ZetaLeft


