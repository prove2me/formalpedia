-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumPointSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumPointSt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:11:01.181645+00:00
-- url     : https://prove2.me/theorems/c7c3039b-0599-4e3f-9db9-b80dfb4a7026
-- title:
--   Inter Num Point St
-- statement:
--   Definitions and structural lemmas for Inter Num Point St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/InterNumPointSt.lean

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
universe u v w
def InterNumPoint.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω),
    IsSubvar y (primeOf (S := k) y) 0 → ∀ L : Fin 0 → SubSystem k y Ω,
      interNum (primeOf (S := k) y) L = (Module.finrank k (funField (k := k) y) : ℤ)
end
end GroundTheory.Heights₂.Heights.Kleiman


