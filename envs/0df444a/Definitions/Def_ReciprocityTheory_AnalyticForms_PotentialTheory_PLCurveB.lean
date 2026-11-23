-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveB
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:42.302646+00:00
-- url     : https://prove2.me/theorems/ccc91e94-8e6d-47e0-94fd-1d058cc6772c
-- title:
--   PLCurve B
-- statement:
--   Definitions and structural lemmas for PLCurve B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace PLC
variable {X : Type} [TopologicalSpace X]
open scoped Classical in

def zeroExt (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ)) (v : X → ℝ) (y : Fin 1 → ℂ) : ℝ :=
  if y ∈ ψ.target then v (ψ.symm y) else 0
end PLC
end
end ReciprocityTheory.AnForm.M


