-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsClosedPointConeCoord
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsClosedPointConeCoord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:45.64433+00:00
-- url     : https://prove2.me/theorems/111a5e7a-9bd1-41bb-94fd-139c611ef6aa
-- title:
--   Statements Closed Point Cone Coord
-- statement:
--   Definitions and structural lemmas for Statements Closed Point Cone Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsClosedPointConeCoord.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowDegreeClosedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace ObjectsChow
open MvPolynomial
def ClosedPointConeCoord.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (y : Fin n → Ω), y ≠ 0 → (∀ g ∈ I, aeval y g = 0) → y i ≠ 0
end ObjectsChow
end GroundTheory.Heights₂.Heights


