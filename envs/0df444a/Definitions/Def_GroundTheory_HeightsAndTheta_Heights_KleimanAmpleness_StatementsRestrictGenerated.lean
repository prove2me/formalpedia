-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:38:36.450086+00:00
-- url     : https://prove2.me/theorems/d5356e12-3c6f-4235-9f9b-fe1fd741b5e9
-- title:
--   Statements Restrict Generated
-- statement:
--   Definitions and structural lemmas for Statements Restrict Generated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsRestrictGenerated.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
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
def RestrictGenerated.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (pp : Ideal (Poly S N)), primeOf (S := S) x ≤ pp → primeOf (S := S) y = pp →
    ∀ (Q : LineBundle S x) (Q' : LineBundle S y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r → Q'.toSubSystem.Generated →
      ∀ I : Chart x, Q.toSubSystem.sub I ≤
        Submodule.span (chartRing S x I) {z | ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
          (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
          z = s I} ⊔ (Q.toSubSystem.twist (idealSys x pp)).sub I
end
end GroundTheory.Heights₂.Heights.Kleiman


