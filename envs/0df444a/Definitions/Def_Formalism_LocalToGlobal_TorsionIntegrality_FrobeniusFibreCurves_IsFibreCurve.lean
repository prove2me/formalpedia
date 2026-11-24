-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_IsFibreCurve
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_IsFibreCurve
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:43.606865+00:00
-- url     : https://prove2.me/theorems/3dfa20e1-42c5-4f3e-9abb-0d86ba839fc9
-- title:
--   Is Fibre Curve
-- statement:
--   Definitions and structural lemmas for Is Fibre Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/IsFibreCurve.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_DivByXSq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.B
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr)
section Alg
variable {K : Type} [Field K] [CharZero K]
abbrev phTw (g2 s2 c0 xT : K) (P l : PowerSeries K) : PowerSeries K :=
  phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l
abbrev thTw (g2 s2 c0 xT : K) (P : PowerSeries K) : PowerSeries K :=
  thZ s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P)
def IsFibreZ (P tr : PowerSeries K) {ι : Type} [Fintype ι] (c : ι → K)
    (wp wm : ι → PowerSeries K) (al S : K) : Prop :=
  (∀ Q, HasSecondLogDeriv (wpShift P (c Q)) (2 * P - wp Q - wm Q)) ∧
    PowerSeries.C (al ^ 2) * PowerSeries.rescale al tr = ∑ Q, (wp Q + wm Q) - PowerSeries.C S
def IsFibreCurve (W : WeierstrassCurve K) (xT yT : K) {ι : Type} [Fintype ι] (xQ yQ : ι → K)
    (al S : K) : Prop :=
  (∀ Q, W.toAffine.Equation (xQ Q) (yQ Q)) ∧
    PowerSeries.C (al ^ 2) * PowerSeries.rescale al (wTr W xT yT) =
      ∑ Q, (wTr W (xQ Q) (yQ Q) + wTr W (xQ Q) (W.toAffine.negY (xQ Q) (yQ Q))) - PowerSeries.C S
end Alg
end Formalism.L2.Th1.B


