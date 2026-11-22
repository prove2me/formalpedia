-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EvalFrameOrd
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EvalFrameOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:57.938212+00:00
-- url     : https://prove2.me/theorems/d03dc4cd-e1ea-438f-9bc2-2add8697f0ee
-- title:
--   Eval Frame Ord
-- statement:
--   Definitions and structural lemmas for Eval Frame Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/EvalFrameOrd.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Mathlib.Meta.Positivity
open Lean Meta Qq
@[positivity Formalism.HC.Frame.ord _]
def evalFrameOrd : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with
  | none => throwError "no order"
  | some _pα => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Formalism.HC.Frame.ord $a) =>
    assertInstancesCommute
    return .positive q(Formalism.HC.Frame.ord_pos $a)
  | _, _, _ => throwError "not the order of a frame"
end Mathlib.Meta.Positivity


