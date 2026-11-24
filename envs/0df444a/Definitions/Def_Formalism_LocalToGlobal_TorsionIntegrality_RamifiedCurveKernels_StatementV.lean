-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementV
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementV
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:57.451207+00:00
-- url     : https://prove2.me/theorems/d8842d86-d752-4803-8a5f-4aeb4240aecc
-- title:
--   Statement V
-- statement:
--   Definitions and structural lemmas for Statement V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/StatementV.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
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
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)
def IntUnram : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K),
    Frame (unitBall K) l linv ph → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    F1 (unitBall K) l linv ph → (∀ i : ℕ, 1 ≤ i → ‖jet l ph i‖ ≤ 1) →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt (unitBall K) l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar (unitBall K) (τ z)) →
    (∀ α : O, PhNormAt (unitBall K) l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt (unitBall K) l linv ph (τ α) (τ (star α))) →
    ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] (w : n → O), (∀ j, star (w j) = w j) →
    ∀ δ : m → Fin 4 × n → O,
      (∀ a b, ∑ i, star (δ i a) * δ i b = if a = b then w a.2 else 0) →
    ∀ (Th : MvPowerSeries n K) (G : MvPowerSeries (Fin 4 × n) K), IntMv (unitBall K) G →
      tens4 Th = toZ linv (mvExp (-(phIso τ l linv ph δ)) * G) →
    JetsIntegral Th ∧
    ∀ (ν : Type) [Fintype ν] (A : n → ν → K), (∀ i x, ‖A i x‖ ≤ 1) →
    ∀ P : MvPolynomial ν K, (∀ k, ‖MvPolynomial.coeff k P‖ ≤ 1) →
      ‖jetPair P (linSub A Th)‖ ≤ 1
def CurveJetsUnram : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 →
    ∀ (s2 al albar : K) (t : ℤ) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al‖ = 1 → al + albar = (t : K) →
    ‖al - albar‖ = 1 → ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 →
    al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ∀ i : ℕ, 1 ≤ i → ‖jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) i‖ ≤ 1
end Formalism.L2.Th1.G


