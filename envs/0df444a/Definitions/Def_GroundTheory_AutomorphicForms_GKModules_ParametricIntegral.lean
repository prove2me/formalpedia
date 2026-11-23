-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
-- name    : GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:58.777287+00:00
-- url     : https://prove2.me/theorems/16b92e5a-44a0-4b20-a384-58d31e2f9544
-- title:
--   Parametric Integral
-- statement:
--   Definitions and structural lemmas for Parametric Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ParametricIntegral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Metric
open scoped ContDiff
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable {α : Type*} [TopologicalSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
namespace ParamIntegral
variable (F : P → α → F')
noncomputable def iter (k : ℕ) (Y : P) (a : α) : ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F' :=
  iteratedFDeriv ℝ k (fun Y => F Y a) Y
variable {F}
end ParamIntegral
open ParamIntegral
end GroundTheory.Automorphic


