-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:25:33.227683+00:00
-- url     : https://prove2.me/theorems/4ca60f19-9682-459a-922d-7bf2cf29b2a8
-- title:
--   PStep Three
-- statement:
--   Definitions and structural lemmas for PStep Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
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
open MvPolynomial
noncomputable section
universe u w
section ChartIdeal
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
abbrev idealChart (J : Ideal (Poly k N)) (I : Chart x) : Ideal (chartRing k x I) :=
  (idealMod (x := x) J I).comap (Algebra.linearMap (chartRing k x I) Ω)
end ChartIdeal
section Algebra
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
end Algebra
end
end GroundTheory.Heights₂.Heights.Kleiman


