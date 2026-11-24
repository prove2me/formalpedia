-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:34:17.209287+00:00
-- url     : https://prove2.me/theorems/2761fc17-a70e-4f6c-b211-5c2c66f1875a
-- title:
--   Statement R
-- statement:
--   Definitions and structural lemmas for Statement R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/StatementR.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
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
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
open Formalism.G (unitBall)
def ShapeAt {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K)
    (d : ℕ) : Prop :=
  ‖jet l ph 2‖ ≤ ‖(d : K)‖ ^ (-(1 / 2 : ℝ)) ∧ (∀ i : ℕ, 1 ≤ i → i ≠ 2 → ‖jet l ph i‖ ≤ 1) ∧
  ∃ J : PowerSeries K, JetsIn1 (unitBall K) J ∧ PowerSeries.constantCoeff J = 1 ∧
    PowerSeries.subst linv (mvExp (-ph) : PowerSeries K) =
      (mvExp (-(PowerSeries.C (jet l ph 2 / 2) * PowerSeries.X ^ 2)) : PowerSeries K) * J
def InvEndInt : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (l linv : PowerSeries K) (a : K),
    IsLogPair l linv → a ≠ 0 → a⁻¹ ∈ R → EndInt R l linv a → EndInt R l linv a⁻¹
def AdjUnitNorm : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K) (N : ℤ),
    Frame R l linv ph → F1 R l linv ph → a ≠ 0 → a⁻¹ ∈ R → EndInt R l linv a → EndInt R l linv b →
    a * b = (N : K) → PhNormAt R l linv ph a b → AdjAt R l linv ph a b
def HalfValuation : Prop :=
  ∀ (K : Type) [NormedField K] (S c : K) (d : ℕ), c ^ 2 = -(d : K) → (d : K) ≠ 0 → ‖c * S‖ ≤ 1 →
    ‖S‖ ≤ ‖(d : K)‖ ^ (-(1 / 2 : ℝ))
def RamifiedShape : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K)
    (a b : K) (d : ℕ),
    Frame (unitBall K) l linv ph → F1 (unitBall K) l linv ph →
    PhNormAt (unitBall K) l linv ph (-1) (-1) → ‖(2 : K)‖ = 1 →
    AdjAt (unitBall K) l linv ph a b → (a - b) ^ 2 = -(d : K) → d ≠ 0 →
    ShapeAt l linv ph d
def CurveNegNorm : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (W : WeierstrassCurve K), CoeffIn R W →
    (2 : K)⁻¹ ∈ R → ∀ s2 : K,
    PhNormAt R (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (-1) (-1)
def WeierstrassBiadditiveModEquiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 → ∀ s2 : K,
    F1 (unitBall K) (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W))
def CurveRamified : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 →
    ∀ (s2 al albar : K) (d : ℕ) (t : ℤ) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al‖ = 1 → al + albar = (t : K) →
    (al - albar) ^ 2 = -(d : K) → d ≠ 0 → ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 →
    al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ShapeAt (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) d
end Formalism.L2.Th1.G


