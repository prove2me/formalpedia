-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobeniusSep
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobeniusSep
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:29.704803+00:00
-- url     : https://prove2.me/theorems/a2a27f5b-5c2a-42a7-adba-784d5e1471c6
-- title:
--   Isogeny Frobenius Sep
-- statement:
--   Definitions and structural lemmas for Isogeny Frobenius Sep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobeniusSep.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
noncomputable def powAdjoin (M : IntermediateField F E.toAffine.FunctionField) (a : ℕ) :
    IntermediateField M E.toAffine.FunctionField :=
  M⟮genX E ^ p ^ a, genY E ^ p ^ a⟯
variable [PerfectRing F p]
end GroundTheory.Arith.Abelian


