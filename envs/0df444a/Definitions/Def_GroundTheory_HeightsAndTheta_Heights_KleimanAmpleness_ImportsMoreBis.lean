-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsMoreBis
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsMoreBis
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:58.882836+00:00
-- url     : https://prove2.me/theorems/521aa996-17a5-5cf7-9898-8cb445f540f5
-- title:
--   Imports More Bis
-- statement:
--   Definitions and structural lemmas for Imports More Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ImportsMoreBis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
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
def DomRingTwist.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (Ω : Type) [Field Ω] [Algebra S Ω] (N N' : ℕ) (x : Fin (N + 1) → Ω)
    (x' : Fin (N' + 1) → Ω) (i : Fin (N + 1)), x i ≠ 0 → ∀ b ∈ Kleiman.domRing S x x' i,
      ∃ c : ℕ, b * x i ^ c ∈ Kleiman.pullSecs x' (Kleiman.twistSys S x (c : ℤ))
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


