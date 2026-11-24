-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_PairsD
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_PairsD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:32.794805+00:00
-- url     : https://prove2.me/theorems/3f8a5fe0-1230-4759-93a3-9cc8618558df
-- title:
--   Pairs D
-- statement:
--   Definitions and structural lemmas for Pairs D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/PairsD.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.ThK.Dbl.Dens
open Polynomial Cardinal
section Schur
variable {R V : Type} [Ring R] [Algebra ℂ R] [AddCommGroup V] [Module ℂ V] [Module R V]
  [IsScalarTower ℂ R V] [IsSimpleModule R V]
end Schur
end GlobalTheory.ThK.Dbl.Dens


