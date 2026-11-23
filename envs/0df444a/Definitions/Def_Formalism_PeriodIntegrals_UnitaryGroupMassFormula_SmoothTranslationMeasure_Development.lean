-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:34.913083+00:00
-- url     : https://prove2.me/theorems/db225bbb-fdfe-4f6c-b575-1894608c5777
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff
noncomputable section
namespace PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
def MulOnUH {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ ∀ a ∈ UH Hm, ∀ b ∈ UH Hm, σ (a * b) = (σ a).comp (σ b)
def StepRed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin n) (Fin n) ℂ),
    IsUnit P → Pᴴ * Jm ε * P = Hm →
    (σ (P⁻¹ * 1 * P) = 1 ∧ ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) →
    IsUnit Hm ∧ MulOnUH Hm σ
def StepExp : Prop :=
  ∀ (n : ℕ) (Hm X : Matrix (Fin n) (Fin n) ℂ), IsUnit Hm → InLie Hm X →
    ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm
def StepSub : Prop :=
  ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
    MulOnUH Hm σ → w ∈ smoothVecs Hm σ →
    (∀ g ∈ UH Hm, σ g w ∈ smoothVecs Hm σ) ∧
    ∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, v - v' ∈ smoothVecs Hm σ
section Deriv
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def StepExpDeriv : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ),
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0
end Deriv
def StepWord : Prop :=
  ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
    MulOnUH Hm σ → (∀ X, InLie Hm X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm) →
    w ∈ smoothVecs Hm σ →
    ∀ ws : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ ws, InLie Hm X) →
      ContinuousOn (fun g => dsigW σ ws (σ g w)) (UH Hm) ∧
      ∀ g ∈ UH Hm, ∀ g₀ ∈ UH Hm,
        dsigW σ ws (σ g w - σ g₀ w) = dsigW σ ws (σ g w) - dsigW σ ws (σ g₀ w)
end PI.PhMeasCore.UnitaryGroupMassFormula
end


