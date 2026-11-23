-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
-- name    : GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:51.748808+00:00
-- url     : https://prove2.me/theorems/d207d274-b124-4fbe-9a58-a89498fefdf2
-- title:
--   Dixmier Malliavin Line Kernel
-- statement:
--   Definitions and structural lemmas for Dixmier Malliavin Line Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean

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
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
namespace LineKernel
def cutoff (r t : ℝ) : ℝ := 1 - smoothTransition (t / r - 1)
def kern (a r : ℝ) : ℝ → ℝ :=
  indicator (Ici 0) fun t => a * exp (-a * t) * cutoff r t
def rem (a r : ℝ) (t : ℝ) : ℝ := -(exp (-a * t) * deriv (cutoff r) t)
def khat (a r : ℝ) (ξ : ℝ) : ℂ := 𝓕 (fun t => (kern a r t : ℂ)) ξ
end LineKernel
end
end GroundTheory.Automorphic


