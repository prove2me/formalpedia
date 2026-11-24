-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicPeriodicCocycleCoboundary
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicPeriodicCocycleCoboundary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:19.783273+00:00
-- url     : https://prove2.me/theorems/5fc75857-31f1-4b99-b079-227729e77887
-- title:
--   Holomorphic Periodic Cocycle Coboundary
-- statement:
--   Definitions and structural lemmas for Holomorphic Periodic Cocycle Coboundary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicPeriodicCocycleCoboundary.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DbarSolveComplexTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
namespace GlobalTheory.PeriodicCousin
variable {g : ℕ}
noncomputable def dbar (a : Fin g) (f : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) : ℂ :=
  fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))
noncomputable def antilin (t : Fin g → ℂ) : (Fin g → ℂ) →L[ℝ] ℂ :=
  ∑ a, t a • ((conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj a))
end GlobalTheory.PeriodicCousin
namespace GlobalTheory
open PeriodicCousin
end GlobalTheory


