-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:20.139399+00:00
-- url     : https://prove2.me/theorems/d900cdc7-818c-45ea-97bc-35d6337ccea5
-- title:
--   Core Cas B
-- statement:
--   Definitions and structural lemmas for Core Cas B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasB.lean

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
variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]
def wordX (X : I → Module.End ℂ M) (l : List I) : Module.End ℂ M := (l.map X).prod
def filtX (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (l : List I) (v : V), l.length ≤ n ∧ y = wordX X l (ι v)}
end PositivityTheory.KReal
end


