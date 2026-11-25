-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosCut
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosCut
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:00.38325+00:00
-- url     : https://prove2.me/theorems/67871fa8-1f49-4979-a4cd-cc131142fd30
-- title:
--   Leading Coeff Pos Cut
-- statement:
--   Definitions and structural lemmas for Leading Coeff Pos Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LeadingCoeffPosCut.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLeadingCoeffPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
universe u w
section Numbers
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (hR : GenericPointSectionInput.Statement.{u, w})
end Numbers
end GroundTheory.Heights₂.Heights.Kleiman


