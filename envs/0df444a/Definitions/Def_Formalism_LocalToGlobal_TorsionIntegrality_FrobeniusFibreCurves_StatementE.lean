-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:51.324794+00:00
-- url     : https://prove2.me/theorems/e082be8e-7f04-4407-b510-296a46be5205
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/StatementE.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_DivByXSq
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
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
def SRules : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap : K) (w : PowerSeries K), IsW A kap w →
    sW w ^ 2 = w ∧ PowerSeries.constantCoeff (sW w) = 0 ∧ PowerSeries.coeff 1 (sW w) = 1 ∧
      2 * sW w * dz (sW w) = dz w ∧
      dz (sW w) ^ 2 = 1 + PowerSeries.C A * w + PowerSeries.C kap * w ^ 2 ∧
      dz (dz (sW w)) = (PowerSeries.C A + 2 * PowerSeries.C kap * w) * sW w
def ShearTwo : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (h : MvPowerSeries (Fin 2) K),
    pd 0 h = pd 1 h → h = atS (ev0 h)
def SAdd : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap : K) (w : PowerSeries K), IsW A kap w →
    atS (sW w) * (1 - MvPowerSeries.C kap * at1 0 w * at1 1 w) =
      at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w))
def WAdd : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap : K) (w : PowerSeries K), IsW A kap w →
    4 * at1 0 w * at1 1 w * (1 - MvPowerSeries.C kap * at1 0 w * at1 1 w) ^ 2 * atS w =
      (at1 0 w * at1 1 (dz w) + at1 1 w * at1 0 (dz w)) ^ 2
def WPrimeU : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    2 * yT + a1 * xT + a3 = 0 →
    PowerSeries.X * PowerSeries.subst l (dz (wOf (xT + c0) P)) =
      PowerSeries.subst l (wOf (xT + c0) P) *
        (2 * thT ep xT yT - PowerSeries.C a1 * PowerSeries.X)
def GCob : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    2 * yT + a1 * xT + a3 = 0 → 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 →
    PowerSeries.subst F (gT ep xT) * LT ep xT yT a1 ^ 2 =
      at1 0 (gT ep xT) * at1 1 (gT ep xT) * F ^ 2 *
        (1 - MvPowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) *
          at1 0 (PowerSeries.subst l (wOf (xT + c0) P)) *
          at1 1 (PowerSeries.subst l (wOf (xT + c0) P))) ^ 2
def LDiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    TwoHyp g2 g3 c0 a1 a3 xT yT →
    ∃ nu : MvPowerSeries (Fin 2) K, Integral nu ∧ MvPowerSeries.constantCoeff nu = 1 ∧
      LT ep xT yT a1 = F * nu
def BeESim : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    TwoHyp g2 g3 c0 a1 a3 xT yT →
    Simeq (cob F (phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l))
      (cob F (phO s2 P l))
def CocycleDiffExpEquiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F H H' : MvPowerSeries (Fin 2) K),
    MvPowerSeries.constantCoeff F = 0 → Integral F → Simeq H H' → Simeq (d1 F H) (d1 F H')
def CubeE : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    TwoHyp g2 g3 c0 a1 a3 xT yT →
    let ph' := phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l
    DivAB (cob F ph') ∧ swap2 (cob F ph') = cob F ph' ∧ Simeq (d1 F (cob F ph')) 0 ∧
      Simeq (d1 F (swap2 (cob F ph'))) 0
def JetsSeries : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l f : PowerSeries K), LawLog F l → Simeq (d1 F (cob F f)) 0 →
    ∀ n : ℕ, 3 ≤ n → Integral (ι := Unit) ((Dinv l)^[n] f)
end Formalism.L2.Th1.B


