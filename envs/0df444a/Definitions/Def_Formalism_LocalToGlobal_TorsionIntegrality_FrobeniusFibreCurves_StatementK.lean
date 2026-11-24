-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:51.292925+00:00
-- url     : https://prove2.me/theorems/8092c800-1fcf-4bc1-a8a3-010bbcf8de22
-- title:
--   Statement K
-- statement:
--   Definitions and structural lemmas for Statement K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/StatementK.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.B
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
open Formalism.L2.Th1.E (Unif ptW inW px py IntCurve OneUnit GaussOne)
open Classical in

def TwoTorsionKernelUnique : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K), IntCurve W →
    ‖(2 : K)‖ = 2⁻¹ → ‖W.a₁‖ = 1 →
    ∀ P Q : W.toAffine.Point, P ≠ 0 → P + P = 0 → InFormalGroupPoints P →
      ‖px W P‖ = 4 ∧ (Q ≠ 0 → Q + Q = 0 → InFormalGroupPoints Q → P = Q)
open Classical in

def DupBig : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K), IntCurve W →
    ‖(2 : K)‖ = 2⁻¹ → ∀ P : W.toAffine.Point, 4 ≤ ‖px W P‖ → P + P ≠ 0 → 4 < ‖px W (P + P)‖
open Classical in

def TorsBound : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K), IntCurve W →
    ‖(2 : K)‖ = 2⁻¹ → ∀ (P : W.toAffine.Point) (k : ℕ), (2 ^ k) • P = 0 → P + P ≠ 0 →
      ‖px W P‖ < 4
def KapNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.A.IntModel W → ‖(2 : K)‖ = 2⁻¹ → ∀ x : K,
      (‖x‖ = 4 → ‖3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4‖ = 16) ∧
      (‖x‖ < 4 → ‖3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4‖ < 16)
def KappaSum : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∑ P ∈ S, (3 * L.weierstrassP P ^ 2 - L.g₂ / 4) = (α ^ 4 - 1) * L.g₂ / 20
def KernelIntegral : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α : ℂ) (b : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 →
    ∀ t, α * t ∈ L.lattice → t ∉ L.lattice → ¬ InFormalGroupPoints (ptW 2 L ι W t)
def KernelStableUnderMultiplier : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α : ℂ) (b : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 →
    ∀ t, InFormalGroupPoints (ptW 2 L ι W t) → InFormalGroupPoints (ptW 2 L ι W (α * t))
def PointsTwoFinal : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (b b' : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 → ‖b'‖ < 1 →
    ω₀ ∈ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    ¬ InFormalGroupPoints (ptW 2 L ι W (ω₀ / 2)) ∧
      (∀ Q, α * Q - ω₀ / 2 ∈ L.lattice → ¬ InFormalGroupPoints (ptW 2 L ι W Q)) ∧
      (∀ z, α * z - ω₀ / 2 ∈ L.lattice → 2 * z ∉ L.lattice)
def ThetaZeroAtTwo : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (b b' : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 → ‖b'‖ < 1 →
    ω₀ ∈ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ 2 ∣ N → (N : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))
end Formalism.L2.Th1.B


