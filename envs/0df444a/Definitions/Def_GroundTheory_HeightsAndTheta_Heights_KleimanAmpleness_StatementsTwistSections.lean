-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:13.302792+00:00
-- url     : https://prove2.me/theorems/419a9407-638d-4790-9c49-84c9763e389c
-- title:
--   Statements Twist Sections
-- statement:
--   Definitions and structural lemmas for Statements Twist Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsTwistSections.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
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
def TwistSections.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (y : Fin (N + 1) → Ω), y ≠ 0 →
    ∀ᶠ n : ℕ in Filter.atTop, (twistSys S y (n : ℤ)).secs = (coordGraded S y).piece (n : ℤ)
end
end GroundTheory.Heights₂.Heights.Kleiman


