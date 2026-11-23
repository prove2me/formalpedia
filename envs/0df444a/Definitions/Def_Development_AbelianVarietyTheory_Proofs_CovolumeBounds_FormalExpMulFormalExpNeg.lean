-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:57.365271+00:00
-- url     : https://prove2.me/theorems/38017d49-d018-4202-a400-0bda42cc0fce
-- title:
--   Formal Exp Mul Formal Exp Neg
-- statement:
--   Definitions and structural lemmas for Formal Exp Mul Formal Exp Neg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
noncomputable def formalExp (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  (PowerSeries.exp A).subst f
noncomputable def formalLog (g : MvPowerSeries σ A) : MvPowerSeries σ A :=
  (PowerSeries.log A).subst (g - 1)
end GlobalTheory.FormalCalc


