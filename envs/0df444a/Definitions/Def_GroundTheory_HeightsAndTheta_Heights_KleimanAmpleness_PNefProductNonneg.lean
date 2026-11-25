-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:21:08.015813+00:00
-- url     : https://prove2.me/theorems/4b1453c7-9684-4fe0-b7bf-f1ec1355c03c
-- title:
--   PNef Product Nonneg
-- statement:
--   Definitions and structural lemmas for PNef Product Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
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
noncomputable section
universe u w
section Expand
end Expand
section Numbers
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
def bundleNum (pp : Ideal (Poly k N)) {n : ℕ} (L : Fin n → LineBundle k x) : ℤ :=
  interNum pp (fun i => (L i).toSubSystem)
variable (hR : GenericPointSectionInput.Statement.{u, w})
include hR
end Numbers
end
end GroundTheory.Heights₂.Heights.Kleiman


