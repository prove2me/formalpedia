-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:12.993387+00:00
-- url     : https://prove2.me/theorems/416610d3-4226-4d5d-b489-3419892aa393
-- title:
--   RLLie A
-- statement:
--   Definitions and structural lemmas for RLLie A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
namespace PositivityTheory.RL.Up
open GlobalTheory.RealWeil
variable {l : Type} [Fintype l] [DecidableEq l]
def Good {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (U : ℝ → (Sch l →L[ℂ] Sch l)) (Q : Sch l →L[ℂ] Sch l)
    (j : Sch l →L[ℂ] B) : Prop := ∀ f, HasDerivAt (fun t => j (U t f)) (j (Q f)) 0
end PositivityTheory.RL.Up
end


