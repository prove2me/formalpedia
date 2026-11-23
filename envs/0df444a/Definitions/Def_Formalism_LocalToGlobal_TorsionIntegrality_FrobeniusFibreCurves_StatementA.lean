-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:58.75629+00:00
-- url     : https://prove2.me/theorems/eff0c13c-3543-4cf5-8746-067e74dfe91e
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/StatementA.lean

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
open Formalism.InvariantFactorPaths.G7 (at1)
def ExpLogRules : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type),
    (∀ f g : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → fExp (f + g) = fExp f * fExp g) ∧
    (∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (fExp f) = 1 ∧ fLog (fExp f) = f) ∧
    (∀ g : MvPowerSeries ι K, MvPowerSeries.constantCoeff g = 1 →
      MvPowerSeries.constantCoeff (fLog g) = 0 ∧ fExp (fLog g) = g)
def ExpLogDeriv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Finite ι] (i : ι),
    (∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      pd i (fExp f) = fExp f * pd i f) ∧
    (∀ g : MvPowerSeries ι K, MvPowerSeries.constantCoeff g = 1 → g * pd i (fLog g) = pd i g)
def ExpLogSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι κ : Type) [Finite ι] (φ : ι → MvPowerSeries κ K),
    (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
    (∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.subst φ (fExp f) = fExp (MvPowerSeries.subst φ f)) ∧
    (∀ g : MvPowerSeries ι K, MvPowerSeries.constantCoeff g = 1 →
      MvPowerSeries.subst φ (fLog g) = fLog (MvPowerSeries.subst φ g))
def PrimRules : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : PowerSeries K),
    dz (prim f) = f ∧ PowerSeries.constantCoeff (prim f) = 0
def WaveUnique : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (h : MvPowerSeries (Fin 2) K),
    pd 0 (pd 0 h) = pd 1 (pd 1 h) → ev0 h = 0 → ev0 (pd 1 h) = 0 → h = 0
def WaveKills : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : PowerSeries K),
    pd 0 (pd 0 (par0 f)) - pd 1 (pd 1 (par0 f)) = -2 * at1 0 (dz (dz f)) + 2 * at1 1 (dz (dz f))
def ParCauchy : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : PowerSeries K),
    PowerSeries.constantCoeff f = 0 → PowerSeries.coeff 1 f = 0 →
    ev0 (par0 f) = 0 ∧ ev0 (pd 1 (par0 f)) = 0
def WpReduced : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    PowerSeries.X ^ 4 * dz P ^ 2 - 4 * PowerSeries.X * dz P =
        12 * P + 12 * PowerSeries.X ^ 2 * P ^ 2 + 4 * PowerSeries.X ^ 4 * P ^ 3 -
          PowerSeries.C g2 * PowerSeries.X ^ 2 * (1 + PowerSeries.X ^ 2 * P) -
          PowerSeries.C g3 * PowerSeries.X ^ 4 ∧
      PowerSeries.X ^ 2 * dz (dz P) =
        12 * P + 6 * PowerSeries.X ^ 2 * P ^ 2 - PowerSeries.C (g2 / 2) * PowerSeries.X ^ 2
def WSecond : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap : K) (w : PowerSeries K), IsW A kap w →
    PowerSeries.coeff 1 w = 0 ∧
      dz (dz w) = 2 + 4 * PowerSeries.C A * w + 6 * PowerSeries.C kap * w ^ 2
def WEven : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap : K) (w : PowerSeries K), IsW A kap w →
    ∀ n, Odd n → PowerSeries.coeff n w = 0
def WOfWp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 e1 : K) (P : PowerSeries K), IsWp g2 g3 P →
    4 * e1 ^ 3 - g2 * e1 - g3 = 0 → IsW (3 * e1) (3 * e1 ^ 2 - g2 / 4) (wOf e1 P)
def AddSigma1Log : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap e1 : K) (w : PowerSeries K), IsW A kap w →
    par0 (sigmaOneSeries e1 kap w) = fLog (1 - MvPowerSeries.C kap * at1 0 w * at1 1 w)
def AddSigma1 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap e1 : K) (w : PowerSeries K), IsW A kap w →
    atS (sigma1 e1 kap w) * atD (sigma1 e1 kap w) =
      at1 0 (sigma1 e1 kap w) ^ 2 * at1 1 (sigma1 e1 kap w) ^ 2 *
        (1 - MvPowerSeries.C kap * at1 0 w * at1 1 w)
def DqRule : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (P : PowerSeries K),
    (∀ n, Odd n → PowerSeries.coeff n P = 0) →
    at1 0 P - at1 1 P = (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * dq P
def AddSigmaLog : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    par0 (sigS P) = fLog (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P)
def AddSigma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (atS (sigma P) * atD (sigma P)) =
      at1 0 (sigma P) ^ 2 * at1 1 (sigma P) ^ 2 * wpDiff P
def AddSgStar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 s2 : K) (P : PowerSeries K), IsWp g2 g3 P →
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (atS (sgStar s2 P) * atD (sgStar s2 P)) =
      at1 0 (sgStar s2 P) ^ 2 * at1 1 (sgStar s2 P) ^ 2 * wpDiff P
def Sigma1Sq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 e1 : K) (P : PowerSeries K), IsWp g2 g3 P →
    4 * e1 ^ 3 - g2 * e1 - g3 = 0 →
    PowerSeries.X ^ 2 * sigma1 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) ^ 2 =
      sigma P ^ 2 * (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2)
def SigmaOdd : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (P : PowerSeries K),
    (∀ n, Odd n → PowerSeries.coeff n P = 0) →
    PowerSeries.coeff 1 (sigma P) = 1 ∧ ∀ n, Even n → PowerSeries.coeff n (sigma P) = 0
def Sigma1Even : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e1 kap : K) (w : PowerSeries K),
    (∀ n, Odd n → PowerSeries.coeff n w = 0) →
    PowerSeries.constantCoeff (sigma1 e1 kap w) = 1 ∧
      ∀ n, Odd n → PowerSeries.coeff n (sigma1 e1 kap w) = 0
end Formalism.L2.Th1.B


