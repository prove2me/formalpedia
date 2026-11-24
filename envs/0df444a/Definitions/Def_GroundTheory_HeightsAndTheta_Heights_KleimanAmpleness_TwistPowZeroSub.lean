-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:08.527871+00:00
-- url     : https://prove2.me/theorems/d9d1bb55-fafd-4ff5-a176-9d02ff6e5e51
-- title:
--   Twist Pow Zero Sub
-- statement:
--   Definitions and structural lemmas for Twist Pow Zero Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
end
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq


