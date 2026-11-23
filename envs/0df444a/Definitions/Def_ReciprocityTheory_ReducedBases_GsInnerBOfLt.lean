-- Prove2me | Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
-- name    : ReciprocityTheory_ReducedBases_GsInnerBOfLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:16.699803+00:00
-- url     : https://prove2.me/theorems/cc3ca003-839a-4182-b41f-4bc10ab861b7
-- title:
--   Gs Inner BOf Lt
-- statement:
--   Definitions and structural lemmas for Gs Inner BOf Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean

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
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
abbrev gs (b : Fin d → E) : Fin d → E := gramSchmidt ℝ b
def mu (b : Fin d → E) (i j : Fin d) : ℝ := ⟪gs b j, b i⟫_ℝ / ‖gs b j‖ ^ 2
def nu (b : Fin d → E) (c : Fin d → ℝ) (j : Fin d) : ℝ := ∑ l, c l * mu b l j
end ReciprocityTheory.ReducedBases.T2
end


