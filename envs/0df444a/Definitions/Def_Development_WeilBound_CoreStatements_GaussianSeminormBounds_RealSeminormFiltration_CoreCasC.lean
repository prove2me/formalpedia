-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:25.312951+00:00
-- url     : https://prove2.me/theorems/259eaf83-d448-405b-ab2d-9d221aad906c
-- title:
--   Core Cas C
-- statement:
--   Definitions and structural lemmas for Core Cas C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasC.lean

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
open Matrix
open scoped InnerProductSpace
namespace PositivityTheory.KReal
section SlopeTestRemainingChoices
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def positionA (m : Matrix I I ℂ) (Θ : (J → I) → V) : (J → I) → V :=
  fun w => ∑ s, ∑ j, m (w s) j • Θ (Function.update w s j)
def formT (Θ Θ' : (J → I) → V) : ℂ := ∑ w, ⟪Θ w, Θ' w⟫_ℂ
end SlopeTestRemainingChoices
end PositivityTheory.KReal
end


