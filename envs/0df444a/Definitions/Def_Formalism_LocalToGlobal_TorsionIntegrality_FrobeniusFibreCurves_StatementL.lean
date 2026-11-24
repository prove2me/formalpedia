-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementL
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementL
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:36.881221+00:00
-- url     : https://prove2.me/theorems/4cc33a0e-bb31-4a3d-a6ce-5dd1fab09d9a
-- title:
--   Statement L
-- statement:
--   Definitions and structural lemmas for Statement L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/StatementL.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
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
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.L2.Th1.F (MulStable)
open Formalism.L2.Th1.E (Unif ptW inW px IntCurve OneUnit GaussOne)
def QuadTwoAdic : Prop :=
  ∀ T N : ℤ, Odd T → Even N →
    ∃ b b' : ℤ_[2], b + b' = (T : ℤ_[2]) ∧ b * b' = (N : ℤ_[2]) ∧ ‖b‖ = 1 ∧ ‖b'‖ < 1
def RootsTwoAdic : Prop :=
  ∀ (ι : ℂ ≃+* ℂ_[2]) (α : ℂ) (T N : ℤ), α + conj α = (T : ℂ) → α * conj α = (N : ℂ) → Odd T →
    Even N → ∃ b b' : ℤ_[2], ‖b‖ = 1 ∧ ‖b'‖ < 1 ∧
      ((ι α = ((b : ℚ_[2]) : ℂ_[2]) ∧ ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2])) ∨
        (ι α = ((b' : ℚ_[2]) : ℂ_[2]) ∧ ι (conj α) = ((b : ℚ_[2]) : ℂ_[2])))
def ThetaZeroTwoTrace : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (T N : ℤ), MulStable L α → α + conj α = (T : ℂ) →
    α * conj α = (N : ℂ) → Odd T → Even N →
    ω₀ ∈ L.lattice → α * (ω₀ / 2) ∉ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (M : ℕ), 0 < M → ¬ 2 ∣ M → (M : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))
def ThetaZeroTwoCM : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → Formalism.L2.Th1.CM.HasCMBy d L →
    ∀ (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W → ‖W.a₁‖ = 1 →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → Formalism.L2.Th1.CM.omegaK d * (ω₀ / 2) ∉ L.lattice →
    conj (Formalism.L2.Th1.CM.omegaK d) * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (M : ℕ), 0 < M → ¬ 2 ∣ M → (M : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))
end Formalism.L2.Th1.B


