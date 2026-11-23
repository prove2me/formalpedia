-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LawDifferenceThree
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LawDifferenceThree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:09.631848+00:00
-- url     : https://prove2.me/theorems/0e87564f-608f-467d-9381-014a725616e1
-- title:
--   Law Difference Three
-- statement:
--   Definitions and structural lemmas for Law Difference Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LawDifferenceThree.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_CurveHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1 cob d1 in3 swap2 DivAB)
section Alg
variable {K : Type} [Field K] [CharZero K]
def wp3 (P : PowerSeries K) (j k : Fin 3) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.X j ^ 2 - MvPowerSeries.X k ^ 2 +
    MvPowerSeries.X j ^ 2 * MvPowerSeries.X k ^ 2 * (at1 k P - at1 j P)
def det3 (P : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  Matrix.det (Matrix.of fun j : Fin 3 =>
    ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3,
      MvPowerSeries.X j * (1 + MvPowerSeries.X j ^ 2 * at1 j P),
      -2 + MvPowerSeries.X j ^ 3 * at1 j (dz P)])
def vand3 (K : Type) [Field K] : MvPowerSeries (Fin 3) K :=
  (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
    (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
    (MvPowerSeries.X 1 - MvPowerSeries.X 2)
def evalSumThree (f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  PowerSeries.subst
    (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f
def evalDiffThree (j k : Fin 3) (f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  PowerSeries.subst (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K) f
def fsE (f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  evalSumThree f + evalDiffThree 0 1 f + evalDiffThree 0 2 f + evalDiffThree 1 2 f - 3 * at1 0 f - 3 * at1 1 f - 3 * at1 2 f
def ev3 (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1, 0] h
def F3 (F : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] F
def lawDifferenceThree (F : MvPowerSeries (Fin 2) K) (i : PowerSeries K) (j k : Fin 3) :
    MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), at1 k i] F
def par3 (F : MvPowerSeries (Fin 2) K) (i f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  PowerSeries.subst (F3 F) f + PowerSeries.subst (lawDifferenceThree F i 0 1) f +
    PowerSeries.subst (lawDifferenceThree F i 0 2) f + PowerSeries.subst (lawDifferenceThree F i 1 2) f -
    3 * at1 0 f - 3 * at1 1 f - 3 * at1 2 f
end Alg
section Norm
open Formalism.DworkPowerSeriesWeights (Integral)
variable {K : Type} [NormedField K]
def CurveHyp3 (F : MvPowerSeries (Fin 2) K) (l P ep : PowerSeries K) (a1 a3 : K) : Prop :=
  PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative K P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3) ∧
    ∃ e : MvPowerSeries (Fin 3) K, Integral e ∧ MvPowerSeries.constantCoeff e = -1 ∧
      Matrix.det (Matrix.of fun j : Fin 3 =>
        ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3, MvPowerSeries.X j * at1 j ep,
          -at1 j ep]) =
        e * F3 F * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
          (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2)
end Norm
end Formalism.L2.Th1.B


