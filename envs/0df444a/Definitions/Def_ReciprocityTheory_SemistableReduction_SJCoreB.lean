-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
-- name    : ReciprocityTheory_SemistableReduction_SJCoreB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:23.733376+00:00
-- url     : https://prove2.me/theorems/5e644e16-8033-42fb-964b-02dc8f9945eb
-- title:
--   SJCore B
-- statement:
--   Definitions and structural lemmas for SJCore B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
def conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ star (WithLp.ofLp c i))
def gaussLogC (a : ℝ) : ℝ := ∫ z : ℂ, log (a * ‖z‖) * exp (-‖z‖ ^ 2)
def gaussOneC : ℝ := ∫ z : ℂ, exp (-‖z‖ ^ 2)
end ReciprocityTheory.MultiplicativeHeights


