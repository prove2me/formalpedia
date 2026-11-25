-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:23:43.67693+00:00
-- url     : https://prove2.me/theorems/7b75c282-9de6-46c4-b0bc-4f62e9a98cdc
-- title:
--   Restr Len Restrict St
-- statement:
--   Definitions and structural lemmas for Restr Len Restrict St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrLenRestrictSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
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
def RestrLenRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (pp : Ideal (Poly k N)) (e : ℕ), IsSubvar y pp e →
    ∀ (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∀ᶠ c : ℕ in atTop, restrLen pp (Q'.toSubSystem.twist (twistSys k y (c : ℤ))) =
        restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ)))
end
end GroundTheory.Heights₂.Heights.Kleiman


