-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StCutRestrLenExact
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StCutRestrLenExact
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:06.144127+00:00
-- url     : https://prove2.me/theorems/e1dde1d6-dd0d-4960-b3ac-76c0ce8fef79
-- title:
--   St Cut Restr Len Exact
-- statement:
--   Definitions and structural lemmas for St Cut Restr Len Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StCutRestrLenExact.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
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
def CutRestrLenExact.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp e → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      ∀ Q : LineBundle k x, ∀ᶠ c : ℕ in atTop,
        restrLen pp ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ))) -
            restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ))) =
          restrLen (pp ⊔ zeroIdeal Lc.toSubSystem s)
            ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ)))
end
end GroundTheory.Heights₂.Heights.Kleiman


