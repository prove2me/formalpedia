-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
-- name    : Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:25:45.291957+00:00
-- url     : https://prove2.me/theorems/de6c4230-1317-4233-9596-749c59e5353a
-- title:
--   Var Change
-- statement:
--   Definitions and structural lemmas for Var Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
namespace Formalism.L2.KerInert.VC
section Alg
variable {A : Type*} [CommRing A] (a1 a2 a3 a4 a6 U Ui r s t u w v : A)
end Alg
open Formalism.L2.Th1.A
section Ring
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
def den : R⟦X⟧ := 1 + PowerSeries.C C.s * X + PowerSeries.C (C.t - C.s * C.r) * wSer W
def vv : R⟦X⟧ := invOfUnit (den W C) 1
def phi : R⟦X⟧ := PowerSeries.C (C.u : R) * (X - PowerSeries.C C.r * wSer W) * vv W C
def psi : R⟦X⟧ := PowerSeries.C ((C.u : R) ^ 3) * wSer W * vv W C
end Ring
section Subst
variable {R : Type} [CommRing R]
end Subst
section Field
variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
end Field
section Integral
open Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] (R' : Subring K)
variable {R'}
end Integral
end Formalism.L2.KerInert.VC


