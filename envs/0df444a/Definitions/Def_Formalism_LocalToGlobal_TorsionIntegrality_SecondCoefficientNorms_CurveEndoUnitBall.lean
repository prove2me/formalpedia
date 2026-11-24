-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoUnitBall
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoUnitBall
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:34:25.276546+00:00
-- url     : https://prove2.me/theorems/92584472-c46c-40a4-81fd-46f6db3b9bfb
-- title:
--   Curve Endo Unit Ball
-- statement:
--   Definitions and structural lemmas for Curve Endo Unit Ball, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/CurveEndoUnitBall.lean

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
namespace Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
def CurveEndoUnitBall : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K], ‖(2 : K)‖ = 1 →
    ∀ (W : WeierstrassCurve K), Formalism.L2.Th1.A.IntModel W → ∀ s2 : K,
    ∀ (O : Type) [CommRing O] [StarRing O] [TopologicalSpace O] (τ : O →+* K),
    Continuous τ → Continuous (star : O → O) →
    (∀ z : O, star z = z → τ z ∈ closure (Set.range (fun n : ℤ => (n : K)))) →
    IsUnit (2 : O) → (∀ α : O, ∃ u v : Oˣ, α = u + v) →
    ∀ Dn : Set O, (∀ α : Oˣ, (α : O) ∈ closure Dn) →
    (∀ α ∈ Dn, ∃ (ι : Type) (_ : Fintype ι) (neg : ι → ι) (xP yP : ι → K),
      IsEndoCurve W neg xP yP (τ α) ∧ (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
      τ α * τ (star α) = (Fintype.card ι : K) + 1 ∧ ‖τ α‖ = 1 ∧
      ‖((τ α) ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 ∧
      τ α * (τ α - τ (star α)) * s2 = ∑ P, (xP P + W.b₂ / 12)) →
    (∀ α : O, EndInt (Formalism.G.unitBall K) (logSer W) (expSer W) (τ α) ∧
      PhNormAt (Formalism.G.unitBall K) (logSer W) (expSer W)
        (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (τ α) (τ (star α)) ∧
      AdjAt (Formalism.G.unitBall K) (logSer W) (expSer W)
        (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (τ α) (τ (star α)) ∧
      ‖(τ α - τ (star α)) * jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) 2‖ ≤ 1) ∧
    (∃ H : PowerSeries K, (∀ i : ℕ, ‖jet (logSer W) H i‖ ≤ 1) ∧
      (mvExp (-(Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W))) : PowerSeries K) =
        mvExp (-(PowerSeries.C (jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) 2 / 2)
          * (logSer W) ^ 2)) * H) ∧
    (∀ α : O, ‖τ α - τ (star α)‖ = 1 → ∀ i : ℕ,
      ‖jet (logSer W) (mvExp (-(Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W))) : PowerSeries K) i‖ ≤ 1)
def CurveJetsUnitBall : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K], ‖(2 : K)‖ = 1 →
    ∀ (W : WeierstrassCurve K), Formalism.L2.Th1.A.IntModel W → ∀ s2 : K,
    ∀ i : ℕ, 1 ≤ i → i ≠ 2 →
      ‖jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) i‖ ≤ 1
end Formalism.L2.Th1.C


