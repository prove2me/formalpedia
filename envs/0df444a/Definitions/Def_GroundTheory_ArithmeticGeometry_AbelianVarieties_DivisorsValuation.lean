-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:25.235889+00:00
-- url     : https://prove2.me/theorems/bbd1c4ee-fdfe-43c5-a83e-9f6f7e73d976
-- title:
--   Divisors Valuation
-- statement:
--   Definitions and structural lemmas for Divisors Valuation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
section Poly
variable {W}
end Poly
section Gen
noncomputable def weierstrassB : F[X] := C W.a₁ * X + C W.a₃
noncomputable def weierstrassRHS : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆
variable {W}
end Gen
section CaseA
variable {W} [IsAlgClosed F] [W.IsElliptic]
end CaseA
end GroundTheory.Arith.Abelian


