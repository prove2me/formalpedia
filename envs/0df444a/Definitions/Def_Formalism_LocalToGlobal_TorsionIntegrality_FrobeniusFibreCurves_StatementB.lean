-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:48.970802+00:00
-- url     : https://prove2.me/theorems/abe430fd-b45e-4d63-a8cc-29e151fca2ec
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/StatementB.lean

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
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
def InvExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l : PowerSeries K), LawLog F l → ∃ i, IsInv l i
def HalfExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l : PowerSeries K), LawLog F l → ‖(2 : K)‖ = 1 → ∃ h, IsHalf l h
def SimeqInt : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (f g f' g' : MvPowerSeries ι K),
    Simeq f g → Simeq f' g' →
    Simeq (f - f') (g - g') ∧ Simeq (-f) (-g) ∧ ∀ n : ℤ, Simeq ((n : MvPowerSeries ι K) * f) (n * g)
def SimeqZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    [NormedAlgebra ℚ_[p] K] (f g : MvPowerSeries ι K) (c : ℤ_[p]), Simeq f g →
    Simeq (MvPowerSeries.C (algebraMap ℚ_[p] K (c : ℚ_[p])) * f)
      (MvPowerSeries.C (algebraMap ℚ_[p] K (c : ℚ_[p])) * g)
def SimeqHalf : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (f g : MvPowerSeries ι K),
    ‖(2 : K)‖ = 1 → Simeq (2 * f) (2 * g) → Simeq f g
def SimeqLog : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g : MvPowerSeries ι K),
    MvPowerSeries.constantCoeff g = 1 → Integral g → Simeq (fLog g) 0 ∧ Simeq (-fLog g) 0
def PhODef : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s2 : K) (P l : PowerSeries K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    PowerSeries.constantCoeff (phO s2 P l) = 0 ∧
      PowerSeries.subst l (sgStar s2 P) = PowerSeries.X * fExp (-phO s2 P l)
def PhEDef : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s2 e1 kap : K) (w l : PowerSeries K),
    PowerSeries.constantCoeff l = 0 →
    PowerSeries.constantCoeff (phE s2 e1 kap w l) = 0 ∧
      PowerSeries.subst l
          (sigma1 e1 kap w * fExp (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2))) =
        fExp (-phE s2 e1 kap w l)
def ParEFormula : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A kap e1 s2 : K)
    (w l i : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsW A kap w → LawLog F l → IsInv l i →
    par F i (phE s2 e1 kap w l) =
      -fLog (1 - MvPowerSeries.C kap * at1 0 (PowerSeries.subst l w) *
        at1 1 (PowerSeries.subst l w))
def ParE : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A kap e1 s2 : K)
    (w l i : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsW A kap w → LawLog F l → IsInv l i → ‖kap‖ ≤ 1 →
    Integral (ι := Unit) (PowerSeries.subst l w) →
    Simeq (par F i (phE s2 e1 kap w l)) 0
def ParO : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 →
    Simeq (par F i (phO s2 P l)) 0
def WIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (c0 e1 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    LawLog F l → CurveHyp F i l P ep c0 → ‖c0 - e1‖ ≤ 1 →
    PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) =
        PowerSeries.X ^ 2 ∧
      Integral (ι := Unit) (PowerSeries.subst l (wOf e1 P))
def DiffPh : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 e1 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → 4 * e1 ^ 3 - g2 * e1 - g3 = 0 → LawLog F l → CurveHyp F i l P ep c0 →
    2 * (phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l - phO s2 P l) =
        -fLog (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) ∧
      (‖c0 - e1‖ ≤ 1 →
        Simeq (ι := Unit) (2 * phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l) (2 * phO s2 P l))
def CobRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l f : PowerSeries K), LawLog F l → PowerSeries.constantCoeff f = 0 →
    DivAB (cob F f) ∧ swap2 (cob F f) = cob F f
def Cube : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i f : PowerSeries K), LawLog F l → IsInv l i → ‖(2 : K)‖ = 1 →
    Simeq (par F i f) 0 → Simeq (d1 F (cob F f)) 0
def LogSigmaPullbackCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → ‖(2 : K)‖ = 1 →
    DivAB (cob F (phO s2 P l)) ∧ swap2 (cob F (phO s2 P l)) = cob F (phO s2 P l) ∧
      Simeq (d1 F (cob F (phO s2 P l))) 0 ∧ Simeq (d1 F (swap2 (cob F (phO s2 P l)))) 0
def LogSigmaOnePullbackCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A kap e1 s2 : K)
    (w l i : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsW A kap w → LawLog F l → IsInv l i → ‖kap‖ ≤ 1 →
    Integral (ι := Unit) (PowerSeries.subst l w) → ‖(2 : K)‖ = 1 →
    DivAB (cob F (phE s2 e1 kap w l)) ∧
      swap2 (cob F (phE s2 e1 kap w l)) = cob F (phE s2 e1 kap w l) ∧
      Simeq (d1 F (cob F (phE s2 e1 kap w l))) 0 ∧
      Simeq (d1 F (swap2 (cob F (phE s2 e1 kap w l)))) 0
def DiagTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i f : PowerSeries K), LawLog F l → IsInv l i → Simeq (par F i f) 0 →
    Simeq (ι := Unit)
        (PowerSeries.subst
          (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), PowerSeries.X] F) f) (4 * f) ∧
      Simeq (ι := Unit)
        (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), PowerSeries.X] (cob F f)) (2 * f)
def PhOEven : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (s2 : K) (P l i : PowerSeries K),
    (∀ n, Odd n → PowerSeries.coeff n P = 0) → PowerSeries.constantCoeff l = 0 →
    PowerSeries.coeff 1 l = 1 → IsInv l i →
    Simeq (ι := Unit) (PowerSeries.subst i (phO s2 P l)) (phO s2 P l)
def PhEEven : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (s2 e1 kap : K)
    (w l i : PowerSeries K),
    (∀ n, Odd n → PowerSeries.coeff n w = 0) → PowerSeries.constantCoeff l = 0 → IsInv l i →
    PowerSeries.subst i (phE s2 e1 kap w l) = phE s2 e1 kap w l
def CobEven : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i f : PowerSeries K), LawLog F l → IsInv l i →
    Simeq (ι := Unit) (PowerSeries.subst i f) f →
    Simeq (MvPowerSeries.subst ![at1 0 i, at1 1 i] (cob F f)) (cob F f)
def JetsThree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l f : PowerSeries K), LawLog F l → Simeq (d1 F (cob F f)) 0 →
    ∀ n : ℕ, 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv l)^[n] f)‖ ≤ 1
end Formalism.L2.Th1.B


