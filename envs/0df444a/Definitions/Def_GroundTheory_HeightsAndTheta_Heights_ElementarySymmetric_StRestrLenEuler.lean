-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StRestrLenEuler
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StRestrLenEuler
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:27:24.523159+00:00
-- url     : https://prove2.me/theorems/7e20c220-fa33-5643-82f5-dd686de3acfb
-- title:
--   St Restr Len Euler
-- statement:
--   Definitions and structural lemmas for St Restr Len Euler, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StRestrLenEuler.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
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
def RestrLenEuler.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (qq : Ideal (Poly k N)), (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) →
    primeOf (S := k) x ≤ qq → ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∀ᶠ c : ℤ in atTop,
        restrLen qq (((twistSys k x 0).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          pieceChar k qq 0 L n c
end
end GroundTheory.Heights₂.Heights.Kleiman


