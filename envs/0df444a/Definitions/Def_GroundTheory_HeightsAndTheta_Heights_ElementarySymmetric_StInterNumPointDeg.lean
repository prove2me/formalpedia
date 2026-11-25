-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:16:26.271894+00:00
-- url     : https://prove2.me/theorems/2a5481cb-2f23-51ea-8438-b8113c4d55f2
-- title:
--   St Inter Num Point Deg
-- statement:
--   Definitions and structural lemmas for St Inter Num Point Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StInterNumPointDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
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
def InterNumPointDeg.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), IsSubvar x pp 0 →
      interNum pp (![] : Fin 0 → SubSystem k x Ω) =
        (FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) : ℤ)
end
end GroundTheory.Heights₂.Heights.Kleiman


