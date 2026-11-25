-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_Support
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_Support
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T04:32:01.321457+00:00
-- url     : https://prove2.me/theorems/6db2e1bd-cdf6-418b-bd40-3e91243b5dc5
-- title:
--   Support
-- statement:
--   Definitions and structural lemmas for Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/Support.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {X : Scheme.{u}}
def Scheme.Modules.SupportedIn (F : X.Modules) (T : Set X) : Prop :=
  ∀ U : X.Opens, Disjoint (U : Set X) T → ∀ s : Γ(F, U), s = 0
namespace Scheme.Modules.SupportedIn
end Scheme.Modules.SupportedIn
section Restrict
variable {F G : X.Modules} (φ : F ⟶ G) (W : X.Opens)
end Restrict
end
end GroundTheory.Arith.SchemeCoh


