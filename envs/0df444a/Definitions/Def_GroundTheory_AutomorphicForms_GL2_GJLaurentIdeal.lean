-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
-- name    : GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:14.792519+00:00
-- url     : https://prove2.me/theorems/dbaed738-df28-45c9-a053-ee6bf927c4c3
-- title:
--   GJLaurent Ideal
-- statement:
--   Definitions and structural lemmas for GJLaurent Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace GodementJacquet
open Polynomial
def laurentSubalgebra : Subalgebra ℂ (RatFunc ℂ) :=
  Algebra.adjoin ℂ {RatFunc.X, RatFunc.X⁻¹}
section Ideal
variable {I : Submodule ℂ (RatFunc ℂ)}
end Ideal
end GodementJacquet
end GroundTheory.Automorphic


