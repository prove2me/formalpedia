-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_CurveHyp
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_CurveHyp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:12.766332+00:00
-- url     : https://prove2.me/theorems/22818288-09dd-4e8a-bf35-9d04c3a53997
-- title:
--   Curve Hyp
-- statement:
--   Definitions and structural lemmas for Curve Hyp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/CurveHyp.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_IsLawOfLog
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
open Formalism.InvariantFactorPaths.G7 (at1 cob d1 swap2 DivAB)
section Alg
variable {K : Type} [Field K] [CharZero K]
def fExp {ι : Type} (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  PowerSeries.subst f (PowerSeries.exp K)
def fLog {ι : Type} (g : MvPowerSeries ι K) : MvPowerSeries ι K :=
  PowerSeries.subst (g - 1) (PowerSeries.log K)
def prim (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) f / (n : K)
abbrev dz (f : PowerSeries K) : PowerSeries K := PowerSeries.derivative K f
def IsWp (g2 g3 : K) (P : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff P = 0 ∧ (∀ n, Odd n → PowerSeries.coeff n P = 0) ∧
    (-2 + PowerSeries.X ^ 3 * dz P) ^ 2 =
      4 * (1 + PowerSeries.X ^ 2 * P) ^ 3 -
        PowerSeries.C g2 * PowerSeries.X ^ 4 * (1 + PowerSeries.X ^ 2 * P) -
        PowerSeries.C g3 * PowerSeries.X ^ 6
def sigS (P : PowerSeries K) : PowerSeries K := -prim (prim P)
def sigma (P : PowerSeries K) : PowerSeries K := PowerSeries.X * fExp (sigS P)
def sgStar (s2 : K) (P : PowerSeries K) : PowerSeries K :=
  sigma P * fExp (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2))
def IsW (A kap : K) (w : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff w = 0 ∧ PowerSeries.coeff 2 w = 1 ∧
    dz w ^ 2 = 4 * w + 4 * PowerSeries.C A * w ^ 2 + 4 * PowerSeries.C kap * w ^ 3
def wOf (e1 : K) (P : PowerSeries K) : PowerSeries K :=
  PowerSeries.X ^ 2 * (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2)⁻¹
def sigmaOneSeries (e1 kap : K) (w : PowerSeries K) : PowerSeries K :=
  -prim (prim (PowerSeries.C e1 + PowerSeries.C kap * w))
def sigma1 (e1 kap : K) (w : PowerSeries K) : PowerSeries K := fExp (sigmaOneSeries e1 kap w)
def atS (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) f
def atD (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) f
def par0 (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  atS f + atD f - 2 * at1 0 f - 2 * at1 1 f
def wpDiff (P : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2 +
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (at1 1 P - at1 0 P)
def dq (P : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  fun n => if Even (n 0) ∧ Even (n 1) then PowerSeries.coeff (n 0 + n 1 + 2) P else 0
def ev0 (h : MvPowerSeries (Fin 2) K) : PowerSeries K :=
  MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0] h
abbrev pd {ι : Type} (i : ι) (h : MvPowerSeries ι K) : MvPowerSeries ι K :=
  MvPowerSeries.pderiv K i h
def lU (l : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) l
def phO (s2 : K) (P l : PowerSeries K) : PowerSeries K :=
  -PowerSeries.subst l (sigS P) + PowerSeries.C (s2 / 2) * l ^ 2 - fLog (lU l)
def phE (s2 e1 kap : K) (w l : PowerSeries K) : PowerSeries K :=
  -PowerSeries.subst l (sigmaOneSeries e1 kap w) + PowerSeries.C (s2 / 2) * l ^ 2
def FI (F : MvPowerSeries (Fin 2) K) (i : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 1 i] F
def par (F : MvPowerSeries (Fin 2) K) (i f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst F f + PowerSeries.subst (FI F i) f - 2 * at1 0 f - 2 * at1 1 f
def Dinv (l f : PowerSeries K) : PowerSeries K := (dz l)⁻¹ * dz f
end Alg
section Norm
open Formalism.DworkPowerSeriesWeights (Integral)
variable {K : Type} [NormedField K]
def LawLog (F : MvPowerSeries (Fin 2) K) (l : PowerSeries K) : Prop :=
  MvPowerSeries.constantCoeff F = 0 ∧ Integral F ∧ PowerSeries.constantCoeff l = 0 ∧
    PowerSeries.coeff 1 l = 1 ∧ cob F l = 0
def IsInv (l i : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff i = 0 ∧ Integral (ι := Unit) i ∧ PowerSeries.subst i l = -l
def IsHalf (l h : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff h = 0 ∧ Integral (ι := Unit) h ∧
    PowerSeries.subst h l = PowerSeries.C (2 : K)⁻¹ * l
def CurveHyp (F : MvPowerSeries (Fin 2) K) (i l P ep : PowerSeries K) (c0 : K) : Prop :=
  Integral (ι := Unit) ep ∧ PowerSeries.constantCoeff ep = 1 ∧
    PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2) ∧
    ∃ c : MvPowerSeries (Fin 2) K, Integral c ∧ MvPowerSeries.constantCoeff c = -1 ∧
      MvPowerSeries.X 1 ^ 2 * at1 0 ep - MvPowerSeries.X 0 ^ 2 * at1 1 ep = c * F * FI F i
end Norm
end Formalism.L2.Th1.B


