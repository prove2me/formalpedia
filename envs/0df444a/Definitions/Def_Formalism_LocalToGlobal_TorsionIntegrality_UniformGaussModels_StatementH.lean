-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementH
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementH
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:05:39.320778+00:00
-- url     : https://prove2.me/theorems/72eb357f-1f5b-4856-a087-657f051497ea
-- title:
--   Statement H
-- statement:
--   Definitions and structural lemmas for Statement H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/StatementH.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_GoodModelAll
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementL
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
namespace Formalism.L2.Th1.Top
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)
def IntOpTwoOrth : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → HasCMBy d L →
  ∀ (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W → ‖W.a₁‖ = 1 →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → omegaK d * (ω₀ / 2) ∉ L.lattice → conj (omegaK d) * (ω₀ / 2) ∉ L.lattice →
  ∀ (n : Type) [Fintype n] (κ : Type) [Fintype κ] (r : κ → ℂ_[2]) (s : κ → n → ℂ) (N : ℕ),
    (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 2 ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (thetaZ 2 L ι ω₀ r s) ∧
    ∀ P : MvPolynomial n ℂ_[2], (∀ m, ‖MvPolynomial.coeff m P‖ ≤ 1) →
      ‖jetPair P (thetaZ 2 L ι ω₀ r s)‖ ≤ 1
def GoodModelTwo : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ (c : ℂ) (hc : c ≠ 0) (W : WeierstrassCurve ℂ_[2]),
      Unif 2 (Formalism.L2.Th1.F.scalePair L c hc) ι W ∧ IntCurve W ∧ ‖W.a₁‖ = 1
end Formalism.L2.Th1.Top


