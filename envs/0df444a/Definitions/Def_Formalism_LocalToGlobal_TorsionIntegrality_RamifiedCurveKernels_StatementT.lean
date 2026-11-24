-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:56:55.358896+00:00
-- url     : https://prove2.me/theorems/26443eba-5683-42e9-bbea-e065398aeeb8
-- title:
--   Statement T
-- statement:
--   Definitions and structural lemmas for Statement T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/StatementT.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_GaussJetBounds_StatementQ
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
namespace Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)
section DefsT
variable {K : Type} [Field K]
def th0 [CharZero K] (W : WeierstrassCurve K) (x0 y0 s2 : K) : PowerSeries K :=
  mvExp (-(lam (wTr W x0 y0) s2))
def phT (W : WeierstrassCurve K) (x0 y0 s2 : K) : PowerSeries K :=
  PowerSeries.subst (logSer W) (lam (wTr W x0 y0) s2)
end DefsT
def ThetaZeroSquare : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (x0 y0 s2 : K),
    W.toAffine.Equation x0 y0 → 2 * y0 + W.a₁ * x0 + W.a₃ = 0 →
    PowerSeries.X ^ 2 * th0 W x0 y0 s2 ^ 2 =
      sgStar (wpReg W) s2 ^ 2 * wpShift (wpReg W) (x0 + W.b₂ / 12)
def ThetaZeroEven : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (x0 y0 s2 : K),
    W.toAffine.Equation x0 y0 → 2 * y0 + W.a₁ * x0 + W.a₃ = 0 →
    PowerSeries.constantCoeff (th0 W x0 y0 s2) = 1 ∧
      ∀ n : ℕ, Odd n → PowerSeries.coeff n (th0 W x0 y0 s2) = 0
def ShiftedSigmaConstantIntegralOfIsogenySum : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (s2 al albar b : K) (ι : Type)
    [Fintype ι] (xP : ι → K),
    al * albar = (Fintype.card ι : K) + 1 → ‖al * (al - albar)‖ = 1 → (∀ P, ‖xP P‖ ≤ 1) →
    ‖(al ^ 2 - 1) * (b / 12)‖ ≤ 1 → al * (al - albar) * s2 = ∑ P, (xP P + b / 12) →
    ‖s2 + b / 12‖ ≤ 1
def ThetaZeroJetsTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ∀ (x0 y0 s2 : K), W.toAffine.Equation x0 y0 →
    2 * y0 + W.a₁ * x0 + W.a₃ = 0 → ‖x0‖ ≤ 1 → ‖y0‖ ≤ 1 → ‖x0 + W.b₂ / 12 + s2‖ ≤ 1 →
    (∀ i : ℕ, 1 ≤ i → ‖jet (logSer W) (phT W x0 y0 s2) i‖ ≤ 1) ∧
    JetsIn1 (unitBall K) (th0 W x0 y0 s2) ∧
    ∀ i : ℕ, ‖jet (logSer W) (PowerSeries.subst (logSer W) (th0 W x0 y0 s2)) i‖ ≤ 1
def ThetaZeroJetsCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W →
    ∀ (s2 al albar : K) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al * (al - albar)‖ = 1 →
    ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 → al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ∀ (x0 y0 : K), W.toAffine.Equation x0 y0 → 2 * y0 + W.a₁ * x0 + W.a₃ = 0 →
    ‖x0‖ ≤ 1 → ‖y0‖ ≤ 1 →
    JetsIn1 (unitBall K) (th0 W x0 y0 s2) ∧
      ∀ i : ℕ, 1 ≤ i → ‖jet (logSer W) (phT W x0 y0 s2) i‖ ≤ 1
def KernelTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → (∀ i : ℕ, 1 ≤ i → ‖jet l ph i‖ ≤ 1) →
    ∀ (n : Type) [Fintype n] (c : n → K), (∀ i, ‖c i‖ ≤ 1) →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    JetsIntegral (toZ linv (mvExp (-(phSum c ph)) * G)) ∧
    ∀ P : MvPolynomial n K, (∀ m, ‖MvPolynomial.coeff m P‖ ≤ 1) →
      ‖jetPair P (toZ linv (mvExp (-(phSum c ph)) * G))‖ ≤ 1
def CurveKernelTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W →
    ∀ (s2 al albar : K) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al * (al - albar)‖ = 1 →
    ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 → al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ∀ (x0 y0 : K), W.toAffine.Equation x0 y0 → 2 * y0 + W.a₁ * x0 + W.a₃ = 0 →
    ‖x0‖ ≤ 1 → ‖y0‖ ≤ 1 →
    ∀ (n : Type) [Fintype n] (c : n → K), (∀ i, ‖c i‖ ≤ 1) →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    ∀ P : MvPolynomial n K, (∀ m, ‖MvPolynomial.coeff m P‖ ≤ 1) →
      ‖jetPair P (toZ (expSer W) (mvExp (-(phSum c (phT W x0 y0 s2))) * G))‖ ≤ 1
def SplitVanishTwo : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → F1 R l linv ph → EndInt R l linv a →
    a ∈ closure (Set.range (fun n : ℤ => (n : K))) → PhNormAt R l linv ph a b →
    a ≠ 0 → a ≠ b → b ≠ 1 →
    IsBinomScalar R (a * (a - b))⁻¹ → IsBinomScalar R (a * (1 - b))⁻¹ →
    LG R ph
end Formalism.L2.Th1.G


