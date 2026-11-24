-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementI
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementI
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:36.089984+00:00
-- url     : https://prove2.me/theorems/9e04e7d8-6f9d-4bb1-a5ac-af6541433f3a
-- title:
--   Statement I
-- statement:
--   Definitions and structural lemmas for Statement I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/StatementI.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_IsFibreCurve
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
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr IsLogPair mulBy EndInt PhNormAt IsBinomScalar)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel)
def NotReduce : Prop :=
  ∀ (G : Type) [AddCommGroup G] (G1 : AddSubgroup G) (β β' : G →+ G),
    (∀ x ∈ G1, β x ∈ G1) → (∀ x ∈ G1, β' x ∈ G1) → (∀ x ∈ G1, β x = 0 → x = 0) →
    ∀ t0 t' t'' : G, t0 = t' + t'' → β' t' = 0 → β' t'' = t'' → t'' ≠ 0 → β t'' = 0 →
    t0 ∉ G1 ∧ ∀ Q : G, β Q = t0 → Q ∉ G1
def Th0Isogeny : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 s2 c0 xT al S : K) (P : PowerSeries K)
    (ι : Type) [Fintype ι] (c : ι → K) (wp wm : ι → PowerSeries K),
    IsWp g2 g3 P → 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 →
    IsFibreZ P (PowerSeries.C (xT + c0) +
      PowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) * wOf (xT + c0) P) c wp wm al S →
    (al ^ 2 - 2 * (Fintype.card ι : K)) * s2 = S →
    PowerSeries.rescale al (thTw g2 s2 c0 xT P) * wpShift P (xT + c0) ^ Fintype.card ι =
      thTw g2 s2 c0 xT P ^ (2 * Fintype.card ι) * ∏ Q, wpShift P (c Q)
def PhENorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 xT al albar S : K)
    (P l linv i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K)
    (ι : Type) [Fintype ι] (xQ : ι → K) (wp wm : ι → PowerSeries K),
    IsWp g2 g3 P → 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 → IsLogPair l linv →
    CurveHyp F i l P ep c0 → ‖xT‖ ≤ 1 → (∀ Q, ‖xQ Q‖ ≤ 1) →
    IsFibreZ P (PowerSeries.C (xT + c0) +
      PowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) * wOf (xT + c0) P)
      (fun Q => xQ Q + c0) wp wm al S →
    al * albar = 2 * (Fintype.card ι : K) → al * (al - albar) * s2 = S →
    PhNormAt (unitBall K) l linv (phTw g2 s2 c0 xT P l) al albar
def ThetaZeroVanishing : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (g2 g3 s2 c0 a1 a3 xT yT al albar S : K)
    (P l linv i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K)
    (ι : Type) [Fintype ι] (xQ : ι → K) (wp wm : ι → PowerSeries K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → IsLogPair l linv → CurveHyp F i l P ep c0 →
    CurveHyp3 F l P ep a1 a3 → TwoHyp g2 g3 c0 a1 a3 xT yT → (∀ Q, ‖xQ Q‖ ≤ 1) →
    IsFibreZ P (PowerSeries.C (xT + c0) +
      PowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) * wOf (xT + c0) P)
      (fun Q => xQ Q + c0) wp wm al S →
    al * albar = 2 * (Fintype.card ι : K) → al * (al - albar) * s2 = S →
    EndInt (unitBall K) l linv al → al ∈ closure (Set.range (fun n : ℤ => (n : K))) →
    al ≠ 0 → al ≠ albar → albar ≠ 1 →
    IsBinomScalar (unitBall K) (al * (al - albar))⁻¹ →
    IsBinomScalar (unitBall K) (al * (1 - albar))⁻¹ →
    Simeq (ι := Unit) (phTw g2 s2 c0 xT P l) 0 ∧
      PowerSeries.constantCoeff (PowerSeries.subst l (thTw g2 s2 c0 xT P)) = 1 ∧
      Integral (ι := Unit) (PowerSeries.subst l (thTw g2 s2 c0 xT P))
def TwoBridge : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (s2 xT yT : K),
    W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    wTr W xT yT = PowerSeries.C (e1W W xT) + PowerSeries.C (kapW W xT) * wOf (e1W W xT) (wpReg W) ∧
      Formalism.L2.Th1.G.th0 W xT yT s2 = thZ s2 (e1W W xT) (kapW W xT) (wOf (e1W W xT) (wpReg W)) ∧
      Formalism.L2.Th1.G.phT W xT yT s2 = evenSigmaLogAtTwoTorsion W s2 xT
def CurveCubeTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K)
    (s2 xT yT : K), IntModel W → W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    ‖xT‖ ≤ 1 → ‖yT‖ ≤ 1 →
    Simeq (cob (fgl W) (evenSigmaLogAtTwoTorsion W s2 xT)) (beW W s2) ∧
    DivAB (cob (fgl W) (evenSigmaLogAtTwoTorsion W s2 xT)) ∧
    swap2 (cob (fgl W) (evenSigmaLogAtTwoTorsion W s2 xT)) = cob (fgl W) (evenSigmaLogAtTwoTorsion W s2 xT) ∧
    Simeq (d1 (fgl W) (cob (fgl W) (evenSigmaLogAtTwoTorsion W s2 xT))) 0 ∧
    Simeq (d1 (fgl W) (swap2 (cob (fgl W) (evenSigmaLogAtTwoTorsion W s2 xT)))) 0
def CurveTh0Vanish : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K)
    (s2 xT yT al albar S : K) (ι : Type) [Fintype ι] (xQ yQ : ι → K),
    IntModel W → W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    ‖xT‖ ≤ 1 → ‖yT‖ ≤ 1 → (∀ Q, ‖xQ Q‖ ≤ 1) → IsFibreCurve W xT yT xQ yQ al S →
    al * albar = 2 * (Fintype.card ι : K) → al * (al - albar) * s2 = S →
    EndInt (unitBall K) (logSer W) (expSer W) al →
    al ∈ closure (Set.range (fun n : ℤ => (n : K))) →
    al ≠ 0 → al ≠ albar → albar ≠ 1 →
    IsBinomScalar (unitBall K) (al * (al - albar))⁻¹ →
    IsBinomScalar (unitBall K) (al * (1 - albar))⁻¹ →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W s2 xT) 0 ∧
      PowerSeries.constantCoeff
        (PowerSeries.subst (logSer W) (Formalism.L2.Th1.G.th0 W xT yT s2)) = 1 ∧
      Integral (ι := Unit) (PowerSeries.subst (logSer W) (Formalism.L2.Th1.G.th0 W xT yT s2))
def TwoAdicScalars : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [NormedAlgebra ℚ_[2] K]
    (F : MvPowerSeries (Fin 2) K) (l linv : PowerSeries K) (b b' : ℤ_[2]),
    LawLog F l → IsLogPair l linv → ‖b‖ = 1 → ‖b'‖ < 1 →
    let al : K := algebraMap ℚ_[2] K (b : ℚ_[2])
    let albar : K := algebraMap ℚ_[2] K (b' : ℚ_[2])
    EndInt (unitBall K) l linv al ∧ al ∈ closure (Set.range (fun n : ℤ => (n : K))) ∧
      al ≠ 0 ∧ al ≠ albar ∧ albar ≠ 1 ∧
      IsBinomScalar (unitBall K) (al * (al - albar))⁻¹ ∧
      IsBinomScalar (unitBall K) (al * (1 - albar))⁻¹
end Formalism.L2.Th1.B


