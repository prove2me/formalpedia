-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefExtendIso
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefExtendIso
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:21:24.995806+00:00
-- url     : https://prove2.me/theorems/72f115fa-658b-4781-974a-8c7d288bda1f
-- title:
--   PNef Extend Iso
-- statement:
--   Definitions and structural lemmas for PNef Extend Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefExtendIso.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
namespace NefExtendIso
variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
def Same (A : Kleiman.SubSystem S x Ω) (B : Kleiman.SubSystem F x Ω) : Prop :=
  ∀ I, (A.sub I : Set Ω) = B.sub I
end NefExtendIso
end
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


