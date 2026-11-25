-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:16:09.69309+00:00
-- url     : https://prove2.me/theorems/71842a53-f06a-4f59-a337-fd478638627a
-- title:
--   St Inter Num Additive
-- statement:
--   Definitions and structural lemmas for St Inter Num Additive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StInterNumAdditive.lean

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
def InterNumAdditive.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (i : Fin n)
      (L' L'' : LineBundle k x), IsSubvar x pp n →
      interNum pp (Function.update (fun j => (L j).toSubSystem) i (L'.twist L''.toSubSystem)) =
        interNum pp (Function.update (fun j => (L j).toSubSystem) i L'.toSubSystem) +
          interNum pp (Function.update (fun j => (L j).toSubSystem) i L''.toSubSystem)
end
end GroundTheory.Heights₂.Heights.Kleiman


