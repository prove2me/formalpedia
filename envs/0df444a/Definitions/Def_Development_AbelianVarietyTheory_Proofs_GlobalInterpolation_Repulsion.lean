-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:18.804603+00:00
-- url     : https://prove2.me/theorems/551db994-e7fc-4525-bc97-be17d53ae87d
-- title:
--   Repulsion
-- statement:
--   Definitions and structural lemmas for Repulsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
namespace GlobalTheory.Lin.Repulsion
noncomputable def powSum (W : Multiset ℂ) (t : ℝ) (j : ℕ) : ℂ :=
  (W.map fun w => (1 / ((2 : ℂ) + t * I - w)) ^ j).sum
end GlobalTheory.Lin.Repulsion


