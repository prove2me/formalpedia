-- Prove2me | Definitions.Def_ConnesGreen_sharp_certificate_threshold
-- name    : ConnesGreen_sharp_certificate_threshold
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-09T04:18:24.271451+00:00
-- url     : https://prove2.me/theorems/cda5e0f6-bd57-42bf-aec7-fc494711be1d
-- title:
--   Sharp loss threshold of the original selected physical form
-- statement:
--   Fix an ORIGINAL positive window $t$ and finite ACTUAL zero packet $S$. For the unchanged synthesis maps on the completed physical carrier, define $$\mu_{t,S}=\sup_{x\in\mathrm{Physical}(t)}\frac{\|N_{t,S}^{*}x\|^2-\|P_t^{*}x\|^2}{\|x\|^2}.$$ The zero vector contributes zero by Lean real division. This is an auxiliary scalar of the ORIGINAL form; it neither asserts its sign nor replaces any carrier, zero actor, packet or finite correction. Subsequent theorems prove this real supremum is bounded and nonnegative, without assuming it is attained.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/SharpCertificateThreshold.lean, definition canonicalCertificateThreshold, source 9d3b6d1e5542440726233de5981abcdaa263ba8f

import Definitions.Def_ConnesGreen_arithmetic_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability
namespace ConnesGreen
def canonicalCertificateThreshold (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) : ℝ :=
  sSup (Set.range (fun x : Physical t =>
    (‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2) / ‖x‖ ^ 2))
end ConnesGreen


