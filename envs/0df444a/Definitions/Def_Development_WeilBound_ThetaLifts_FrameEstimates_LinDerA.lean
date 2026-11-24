-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA
-- name    : Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:01.720801+00:00
-- url     : https://prove2.me/theorems/11a9c3b8-a7da-4c78-8cb5-d98e67e26ec7
-- title:
--   Lin Der A
-- statement:
--   Definitions and structural lemmas for Lin Der A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
section Step
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
end Step
section Alg
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
def Gr (a : A →L[ℝ] A) (g : A) : Prop := a g * g = 1 ∧ g * a g = 1
def pr (a : A →L[ℝ] A) : A →L[ℝ] A := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ A - a)
variable {a : A →L[ℝ] A}
end Alg
end PositivityTheory.ThKEst.LinDerPf
end


