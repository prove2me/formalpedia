-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LocrepSB
-- name    : Development_WeilBound_CoreStatements_LocalThetaKernels_LocrepSB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:12.214366+00:00
-- url     : https://prove2.me/theorems/5e62edd0-5965-4468-a725-fd06c4d7985e
-- title:
--   Locrep SB
-- statement:
--   Definitions and structural lemmas for Locrep SB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKH.Locrep
open Filter Topology GlobalTheory.WeilM
variable {A K : Type} [AddCommGroup A] [AddCommGroup K] (ev : A →+ K) (ι : K →+ A)
def put (x : A) (y : K) : A := x - ι (ev x) + ι y
def Pm (φ : K → ℂ) (y : K) : Module.End ℂ (A → ℂ) where
  toFun Φ x := φ (ev x) * Φ (put ev ι x y)
  map_add' Φ Ψ := by funext x; simp [mul_add]
  map_smul' c Φ := by funext x; simp [mul_left_comm]
variable {ev ι}
variable [TopologicalSpace A] [IsTopologicalAddGroup A] [TopologicalSpace K] [IsTopologicalAddGroup K]
end PositivityTheory.ThKH.Locrep


