-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
-- name    : TaoFivePrimes_RHFastComplexBallSemantics
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T09:27:25.969317+00:00
-- url     : https://prove2.me/theorems/7fdc3342-88c1-4920-a241-fb22c6d901fa
-- title:
--   Complex interpretation of fixed-point error balls
-- statement:
--   The complex value and closed error-ball interpretation of the ordinary integer Ball record. No arithmetic soundness or numerical enclosure is asserted by this definition alone.
-- source:
--   Complex fixed-point arithmetic; application to the center Gaussian/Hermite route and Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastComplexBallArithmetic
import Mathlib.Analysis.Complex.Basic
namespace RHFastBallSemantics
noncomputable def value (D:Nat) (a:RHFastBallArithmetic.Ball) : ℂ :=
 ((a.re:ℂ)+(a.im:ℂ)*Complex.I)/(D:ℂ)
noncomputable def encloses (D:Nat) (a:RHFastBallArithmetic.Ball) (z:ℂ) : Prop :=
 ‖z-value D a‖≤(a.radius:ℝ)/(D:ℝ)
end RHFastBallSemantics
noncomputable def TaoFivePrimes_RHFastComplexBallSemantics : Nat := 128


